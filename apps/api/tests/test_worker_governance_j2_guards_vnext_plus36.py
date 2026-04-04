from __future__ import annotations

import asyncio
import fnmatch
import json
import subprocess
from pathlib import Path
from typing import Any

import adeu_api.urm_routes as urm_routes_module
import pytest
from fastapi import FastAPI
from urm_runtime.capability_policy import (
    POLICY_ACTION_URM_AGENT_CANCEL,
    POLICY_ACTION_URM_WORKER_RUN,
    load_capability_policy,
)
from urm_runtime.errors import URMError
from urm_runtime.models import WorkerCancelResponse, WorkerRunResult


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise RuntimeError("repository root not found")


def _worker_run_payload(
    *,
    client_request_id: str,
    provider: str = "codex",
    role: str = "pipeline_worker",
) -> dict[str, Any]:
    return {
        "provider": provider,
        "role": role,
        "client_request_id": client_request_id,
        "prompt": "j2 worker governance test",
        "template_id": "adeu.workflow.pipeline_worker.v0",
        "template_version": "v0",
        "schema_version": "urm.workflow.v0",
        "domain_pack_id": "urm_domain_adeu",
        "domain_pack_version": "0.0.0",
    }


class _StubWorkerRunner:
    def __init__(self) -> None:
        self.run_calls: list[Any] = []
        self.cancel_calls: list[str] = []

    def run(self, request: Any) -> WorkerRunResult:
        self.run_calls.append(request)
        return WorkerRunResult(
            worker_id="worker-run-guard",
            status="ok",
            exit_code=0,
            evidence_id="evidence-guard",
            raw_jsonl_path="/tmp/worker-run-guard.jsonl",
            urm_events_path=None,
            normalized_event_count=0,
            artifact_candidate=None,
            parse_degraded=False,
            invalid_schema=False,
            schema_validation_errors=[],
            error=None,
            idempotent_replay=False,
        )

    def cancel(self, *, worker_id: str) -> WorkerCancelResponse:
        self.cancel_calls.append(worker_id)
        return WorkerCancelResponse(
            worker_id=worker_id,
            status="cancelled",
            idempotent_replay=False,
            error=None,
        )


@pytest.fixture()
def worker_app() -> FastAPI:
    app = FastAPI()
    app.include_router(urm_routes_module.router)
    return app


def _asgi_post_json(*, app: FastAPI, path: str, payload: dict[str, Any]) -> tuple[int, Any]:
    body_bytes = json.dumps(payload).encode("utf-8")
    scope = {
        "type": "http",
        "asgi": {"version": "3.0", "spec_version": "2.3"},
        "http_version": "1.1",
        "method": "POST",
        "scheme": "http",
        "path": path,
        "raw_path": path.encode("ascii"),
        "query_string": b"",
        "headers": [
            (b"host", b"testserver"),
            (b"content-type", b"application/json"),
            (b"content-length", str(len(body_bytes)).encode("ascii")),
        ],
        "client": ("testclient", 50000),
        "server": ("testserver", 80),
    }
    events: list[dict[str, Any]] = [
        {"type": "http.request", "body": body_bytes, "more_body": False}
    ]
    sent: list[dict[str, Any]] = []

    async def _receive() -> dict[str, Any]:
        if events:
            return events.pop(0)
        return {"type": "http.disconnect"}

    async def _send(message: dict[str, Any]) -> None:
        sent.append(message)

    async def _invoke() -> None:
        await app(scope, _receive, _send)

    asyncio.run(_invoke())

    try:
        start_message = next(
            message for message in sent if message["type"] == "http.response.start"
        )
    except StopIteration:
        raise AssertionError(
            "No 'http.response.start' message was sent by the application."
        ) from None
    body = b"".join(
        message.get("body", b"") for message in sent if message["type"] == "http.response.body"
    )
    if not body:
        return int(start_message["status"]), None
    return int(start_message["status"]), json.loads(body.decode("utf-8"))


def _install_noop_policy_event_emitter(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        urm_routes_module,
        "_policy_event_emitter",
        lambda *, session_id: (lambda *_args, **_kwargs: None),
    )


def _git_text(*args: str) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=str(_repo_root()),
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        stderr = completed.stderr.strip()
        raise AssertionError(f"git {' '.join(args)} failed: {stderr}")
    return completed.stdout.strip()


def _changed_files_against_origin_main() -> list[str]:
    merge_base = _git_text("merge-base", "origin/main", "HEAD")
    changed = _git_text("diff", "--name-only", "--diff-filter=ACDMRTUXB", f"{merge_base}..HEAD")
    return [line.strip() for line in changed.splitlines() if line.strip()]


def test_v36_worker_run_http_path_calls_authorize_action_with_frozen_defaults(
    worker_app: FastAPI,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_noop_policy_event_emitter(monkeypatch)
    runner = _StubWorkerRunner()
    authorize_calls: list[dict[str, Any]] = []

    original_authorize_action = urm_routes_module.authorize_action

    def _spy_authorize_action(**kwargs: Any) -> Any:
        authorize_calls.append(dict(kwargs))
        return original_authorize_action(**kwargs)

    monkeypatch.setattr(urm_routes_module, "authorize_action", _spy_authorize_action)
    monkeypatch.setattr(urm_routes_module, "_get_worker_runner", lambda: runner)

    status_code, payload = _asgi_post_json(
        app=worker_app,
        path="/urm/worker/run",
        payload=_worker_run_payload(
            client_request_id="worker-run-http-allow",
            role="payload-spoofed-role",
        ),
    )
    assert status_code == 200
    assert payload["worker_id"] == "worker-run-guard"
    assert payload["status"] == "ok"
    assert payload["evidence_id"] == "evidence-guard"

    assert len(runner.run_calls) == 1
    assert len(authorize_calls) == 1
    call = authorize_calls[0]
    assert call["role"] == "copilot"
    assert call["action"] == POLICY_ACTION_URM_WORKER_RUN
    assert call["writes_allowed"] is False
    assert call["approval_provided"] is False
    assert call["session_active"] is False
    assert call["action_payload"] == {"client_request_id": "worker-run-http-allow"}


def test_v36_worker_cancel_http_path_calls_authorize_action_with_frozen_defaults(
    worker_app: FastAPI,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_noop_policy_event_emitter(monkeypatch)
    runner = _StubWorkerRunner()
    authorize_calls: list[dict[str, Any]] = []

    original_authorize_action = urm_routes_module.authorize_action

    def _spy_authorize_action(**kwargs: Any) -> Any:
        authorize_calls.append(dict(kwargs))
        return original_authorize_action(**kwargs)

    monkeypatch.setattr(urm_routes_module, "authorize_action", _spy_authorize_action)
    monkeypatch.setattr(urm_routes_module, "_get_worker_runner", lambda: runner)

    status_code, payload = _asgi_post_json(
        app=worker_app,
        path="/urm/worker/worker-cancel-http/cancel",
        payload={"provider": "codex"},
    )
    assert status_code == 200
    assert payload["worker_id"] == "worker-cancel-http"
    assert payload["status"] == "cancelled"

    assert runner.cancel_calls == ["worker-cancel-http"]
    assert len(authorize_calls) == 1
    call = authorize_calls[0]
    assert call["role"] == "copilot"
    assert call["action"] == POLICY_ACTION_URM_AGENT_CANCEL
    assert call["writes_allowed"] is False
    assert call["approval_provided"] is False
    assert call["session_active"] is False
    assert call["action_payload"] == {"worker_id": "worker-cancel-http"}


@pytest.mark.parametrize(
    ("path", "json_payload"),
    (
        (
            "/urm/worker/run",
            _worker_run_payload(client_request_id="worker-run-invalid-provider", provider="other"),
        ),
        ("/urm/worker/worker-invalid-provider/cancel", {"provider": "other"}),
    ),
)
def test_v36_non_codex_provider_path_does_not_invoke_authorize_action(
    path: str,
    json_payload: dict[str, Any],
    worker_app: FastAPI,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_noop_policy_event_emitter(monkeypatch)
    called = False

    def _fail_authorize_action(**_: Any) -> Any:
        nonlocal called
        called = True
        raise AssertionError("authorize_action must not run for invalid provider branches")

    monkeypatch.setattr(urm_routes_module, "authorize_action", _fail_authorize_action)
    monkeypatch.setattr(
        urm_routes_module,
        "_get_worker_runner",
        lambda: (_ for _ in ()).throw(
            AssertionError("_get_worker_runner must not run for invalid provider branches")
        ),
    )

    status_code, _ = _asgi_post_json(app=worker_app, path=path, payload=json_payload)
    assert status_code == 422
    assert called is False


@pytest.mark.parametrize(
    ("path", "json_payload", "expected_action"),
    (
        (
            "/urm/worker/run",
            _worker_run_payload(client_request_id="worker-run-denied"),
            POLICY_ACTION_URM_WORKER_RUN,
        ),
        (
            "/urm/worker/worker-denied/cancel",
            {"provider": "codex"},
            POLICY_ACTION_URM_AGENT_CANCEL,
        ),
    ),
)
def test_v36_worker_routes_denial_envelope_has_structured_role_and_action(
    path: str,
    json_payload: dict[str, Any],
    expected_action: str,
    worker_app: FastAPI,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_noop_policy_event_emitter(monkeypatch)

    def _deny_authorize_action(**_: Any) -> Any:
        raise URMError(
            code="URM_POLICY_DENIED",
            message="denied by guard test",
            context={"reason": "expected-test-denial"},
        )

    monkeypatch.setattr(urm_routes_module, "authorize_action", _deny_authorize_action)
    monkeypatch.setattr(urm_routes_module, "_get_worker_runner", lambda: _StubWorkerRunner())

    status_code, payload = _asgi_post_json(app=worker_app, path=path, payload=json_payload)
    assert status_code == 400
    detail = payload["detail"]
    assert detail["code"] == "URM_POLICY_DENIED"
    assert detail["context"]["role"] == "copilot"
    assert detail["context"]["action"] == expected_action
    assert detail["context"]["reason"] == "expected-test-denial"


def test_v36_required_worker_action_ids_are_members_of_capability_lattice() -> None:
    policy = load_capability_policy()
    action_names = set(policy.actions.keys())
    assert {POLICY_ACTION_URM_WORKER_RUN, POLICY_ACTION_URM_AGENT_CANCEL}.issubset(action_names)


def test_v36_worker_role_derivation_resolver_is_canonical_and_deterministic() -> None:
    first = urm_routes_module._resolve_worker_route_authorization_role()
    second = urm_routes_module._resolve_worker_route_authorization_role()
    assert first == "copilot"
    assert second == first


def test_v36_j2_anti_coupling_diff_guard_for_v31_g_surfaces() -> None:
    changed_files = _changed_files_against_origin_main()

    migration_or_sql_matches = [
        path
        for path in changed_files
        if fnmatch.fnmatch(path, "apps/**/migrations/**") or fnmatch.fnmatch(path, "apps/**/*.sql")
    ]
    assert migration_or_sql_matches == []

    forbidden_v31_g_surface_changes = {
        "apps/api/src/adeu_api/main.py",
        "apps/api/src/adeu_api/storage.py",
    }
    touched_forbidden_surfaces = sorted(
        forbidden_v31_g_surface_changes.intersection(changed_files)
    )
    if touched_forbidden_surfaces:
        # v36 anti-coupling guard remains strict-by-default, but v37 K1 is
        # allowed to touch the frozen V31-G release surfaces with a narrow file set.
        if touched_forbidden_surfaces == ["apps/api/src/adeu_api/main.py"]:
            # V51-B may touch the main API app only to register the bounded
            # ODEU simulation route, without widening into the deferred V31-G
            # storage/persistence seam.
            allowed_v51_b_api_changes = {
                "apps/api/pyproject.toml",
                "apps/api/src/adeu_api/main.py",
                "apps/api/src/adeu_api/odeu_sim.py",
                "apps/api/tests/fixtures/v51b/reference_odeu_run_response_healthy_baseline.json",
                "apps/api/tests/fixtures/v51b/reference_odeu_run_response_invalid_negative_seed.json",
                "apps/api/tests/fixtures/v51b/reference_odeu_run_response_kernel_mismatch.json",
                "apps/api/tests/fixtures/v51b/reference_odeu_run_response_weak_d.json",
                "apps/api/tests/test_odeu_sim_vnext_plus125.py",
                "apps/api/tests/test_worker_governance_j2_guards_vnext_plus36.py",
            }
            unexpected_changes = sorted(set(changed_files).difference(allowed_v51_b_api_changes))
            assert unexpected_changes == []
        else:
            assert touched_forbidden_surfaces == sorted(forbidden_v31_g_surface_changes)
            allowed_v31_g_release_changes = {
                "apps/api/src/adeu_api/main.py",
                "apps/api/src/adeu_api/storage.py",
                "apps/api/tests/test_core_ir_proposer_y2.py",
                "apps/api/tests/test_core_ir_proposer_y4_guards.py",
                "apps/api/tests/test_worker_governance_j2_guards_vnext_plus36.py",
            }
            unexpected_changes = sorted(
                set(changed_files).difference(allowed_v31_g_release_changes)
            )
            assert unexpected_changes == []
    else:
        assert touched_forbidden_surfaces == []

    merge_base = _git_text("merge-base", "origin/main", "HEAD")
    diff_text = _git_text("diff", "--unified=0", f"{merge_base}..HEAD", "--", "apps/api/src")
    added_lines = [
        line[1:]
        for line in diff_text.splitlines()
        if line.startswith("+") and not line.startswith("+++")
    ]
    assert all("_CORE_IR_PROPOSER_IDEMPOTENCY_BY_KEY" not in line for line in added_lines)
