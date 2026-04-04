"use client";

import { type ChangeEvent, type FormEvent, useState } from "react";

import { apiBase } from "../lib/api-base";
import styles from "./page.module.css";
import {
  buildApiPayload,
  buildDefaultViewConfig,
  createViewModelFromApiResponse,
  parseApiResponse,
  RELEASED_SCENARIO_NAMES,
  type OdeuRouteStatus,
  type OdeuRunViewConfig,
  type OdeuRunViewModel,
  validateViewConfig,
} from "./view-model";

type FailureMessage = {
  title: string;
  detail: string;
};

const INITIAL_ROUTE_STATUS: OdeuRouteStatus = "idle";

function failureMessageForStatus(
  status: Exclude<OdeuRouteStatus, "idle" | "loading">,
  failureCode: string | null,
): FailureMessage {
  if (status === "fail_closed_invalid_request") {
    return {
      title: "Request failed closed",
      detail: failureCode ?? "The released V51-B input contract rejected the current request.",
    };
  }
  return {
    title: "Kernel/API stack failed closed",
    detail: failureCode ?? "The released route response could not be trusted as a stable V51-B payload.",
  };
}

function renderSparseCounts(actionCounts: Record<string, number> | null) {
  if (!actionCounts || Object.keys(actionCounts).length === 0) {
    return <p className={styles.emptyNote}>No observed action counts were emitted.</p>;
  }
  return (
    <ul className={styles.inlineList}>
      {Object.entries(actionCounts).map(([name, count]) => (
        <li key={name}>
          <span>{name}</span>
          <strong>{count}</strong>
        </li>
      ))}
    </ul>
  );
}

function renderObjectTable(value: Record<string, unknown>) {
  return (
    <dl className={styles.detailGrid}>
      {Object.entries(value).map(([key, entryValue]) => (
        <div key={key}>
          <dt>{key}</dt>
          <dd>{String(entryValue)}</dd>
        </div>
      ))}
    </dl>
  );
}

export function OdeuSimClient() {
  const [viewConfig, setViewConfig] = useState<OdeuRunViewConfig>(buildDefaultViewConfig);
  const [routeStatus, setRouteStatus] = useState<OdeuRouteStatus>(INITIAL_ROUTE_STATUS);
  const [viewModel, setViewModel] = useState<OdeuRunViewModel | null>(null);
  const [failureMessage, setFailureMessage] = useState<FailureMessage | null>(null);

  function updateNumberField(
    field: "seed" | "steps",
    event: ChangeEvent<HTMLInputElement>,
  ): void {
    const next = Number(event.target.value);
    if (!Number.isFinite(next)) return;
    setViewConfig((current) => ({
      ...current,
      [field]: next,
    }));
  }

  function updateScenario(event: ChangeEvent<HTMLSelectElement>): void {
    const nextScenario = event.target.value;
    if (!RELEASED_SCENARIO_NAMES.includes(nextScenario as (typeof RELEASED_SCENARIO_NAMES)[number])) {
      return;
    }
    setViewConfig((current) => ({
      ...current,
      scenario_name: nextScenario as OdeuRunViewConfig["scenario_name"],
    }));
  }

  async function handleSubmit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();

    const validationError = validateViewConfig(viewConfig);
    if (validationError) {
      setRouteStatus("fail_closed_invalid_request");
      setViewModel(null);
      setFailureMessage({
        title: "Request failed closed",
        detail: validationError,
      });
      return;
    }

    setRouteStatus("loading");
    setViewModel(null);
    setFailureMessage(null);

    try {
      const response = await fetch(`${apiBase()}/odeu-sim/run`, {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
        },
        body: JSON.stringify(buildApiPayload(viewConfig)),
      });
      const payload = (await response.json()) as unknown;
      const parsed = parseApiResponse(payload);
      if (!parsed) {
        setRouteStatus("fail_closed_kernel_mismatch");
        setFailureMessage({
          title: "Kernel/API stack failed closed",
          detail: "The released response shape did not match the bounded V51-B contract.",
        });
        return;
      }

      const nextViewModel = createViewModelFromApiResponse(parsed);
      setViewModel(nextViewModel);
      setRouteStatus(nextViewModel.route_status);
      setFailureMessage(
        nextViewModel.route_status === "completed_clean"
          ? null
          : failureMessageForStatus(nextViewModel.route_status, nextViewModel.failure_code),
      );
    } catch {
      setRouteStatus("fail_closed_kernel_mismatch");
      setViewModel(null);
      setFailureMessage({
        title: "Kernel/API stack failed closed",
        detail: "The released ODEU simulation API could not be reached from the bounded web route.",
      });
    }
  }

  const isCompleted = routeStatus === "completed_clean" && viewModel !== null;
  const isLoading = routeStatus === "loading";

  return (
    <div className={styles.shell} data-route-id="odeu_sim_summary_surface" data-route-status={routeStatus}>
      <section className={styles.hero}>
        <div>
          <p className={styles.eyebrow}>V51-C bounded browser consumer</p>
          <h1>ODEU Simulation Summary</h1>
          <p className={styles.lede}>
            One released API route in, one bounded summary surface out. This web slice stays
            subordinate to the released kernel and refuses the prototype sandbox controls.
          </p>
        </div>
        <span className={styles.statusBadge} data-status={routeStatus}>
          {routeStatus}
        </span>
      </section>

      <section className={styles.controlsPanel}>
        <div className={styles.controlsIntro}>
          <h2>Run released scenario</h2>
          <p className={styles.panelNote}>
            Initial render remains idle. Defaults are prefilled, and execution starts only when
            you submit the bounded form.
          </p>
        </div>
        <form className={styles.formGrid} onSubmit={handleSubmit}>
          <label className={styles.field}>
            <span>Scenario</span>
            <select value={viewConfig.scenario_name} onChange={updateScenario} disabled={isLoading}>
              {RELEASED_SCENARIO_NAMES.map((scenarioName) => (
                <option key={scenarioName} value={scenarioName}>
                  {scenarioName}
                </option>
              ))}
            </select>
          </label>
          <label className={styles.field}>
            <span>Seed</span>
            <input
              type="number"
              min={0}
              step={1}
              value={viewConfig.seed}
              onChange={(event) => updateNumberField("seed", event)}
              disabled={isLoading}
            />
          </label>
          <label className={styles.field}>
            <span>Steps</span>
            <input
              type="number"
              min={1}
              max={25}
              step={1}
              value={viewConfig.steps}
              onChange={(event) => updateNumberField("steps", event)}
              disabled={isLoading}
            />
          </label>
          <div className={styles.submitRow}>
            <button type="submit" className={styles.submitButton} disabled={isLoading}>
              {isLoading ? "Running…" : "Run released summary"}
            </button>
            <p className={styles.muted}>
              Fixed output mode: <code>summary_only_json</code>
            </p>
          </div>
        </form>
      </section>

      {failureMessage ? (
        <section className={styles.failureBanner} data-failure-status={routeStatus}>
          <strong>{failureMessage.title}</strong>
          <p>{failureMessage.detail}</p>
        </section>
      ) : null}

      {isCompleted ? (
        <div className={styles.grid}>
          <section className={styles.panel}>
            <h2>Response identity</h2>
            <dl className={styles.detailGrid}>
              <div>
                <dt>request_ref</dt>
                <dd>{viewModel.request_ref}</dd>
              </div>
              <div>
                <dt>kernel_contract_ref</dt>
                <dd>{viewModel.kernel_contract_ref}</dd>
              </div>
              <div>
                <dt>response_hash</dt>
                <dd>{viewModel.response_hash}</dd>
              </div>
              <div>
                <dt>regime_label</dt>
                <dd>{viewModel.meta?.regime_label ?? "n/a"}</dd>
              </div>
            </dl>
          </section>

          <section className={styles.panel}>
            <h2>Lane summary</h2>
            {viewModel.lane_summary ? (
              <dl className={styles.detailGrid}>
                <div>
                  <dt>mean_legitimacy_belief</dt>
                  <dd>{viewModel.lane_summary.mean_legitimacy_belief}</dd>
                </div>
                <div>
                  <dt>mean_uncertainty</dt>
                  <dd>{viewModel.lane_summary.mean_uncertainty}</dd>
                </div>
                <div>
                  <dt>mean_resources</dt>
                  <dd>{viewModel.lane_summary.mean_resources}</dd>
                </div>
              </dl>
            ) : (
              <p className={styles.emptyNote}>No lane summary available.</p>
            )}
          </section>

          <section className={styles.panel}>
            <h2>Action counts</h2>
            {renderSparseCounts(viewModel.action_counts)}
          </section>

          <section className={styles.panel}>
            <h2>Observed counts</h2>
            <dl className={styles.detailGrid}>
              <div>
                <dt>event_record_count</dt>
                <dd>{viewModel.event_record_count}</dd>
              </div>
              <div>
                <dt>evidence_record_count</dt>
                <dd>{viewModel.evidence_record_count}</dd>
              </div>
              <div>
                <dt>sanction_event_count</dt>
                <dd>{viewModel.sanction_event_count}</dd>
              </div>
            </dl>
          </section>

          <section className={styles.panel}>
            <h2>Config snapshot</h2>
            {viewModel.config_snapshot ? (
              renderObjectTable(viewModel.config_snapshot as unknown as Record<string, unknown>)
            ) : (
              <p className={styles.emptyNote}>No config snapshot available.</p>
            )}
          </section>

          <section className={styles.panel}>
            <h2>Current metric</h2>
            {viewModel.current_metric ? (
              renderObjectTable(viewModel.current_metric as unknown as Record<string, unknown>)
            ) : (
              <p className={styles.emptyNote}>No current metric available.</p>
            )}
          </section>
        </div>
      ) : (
        <section className={styles.emptyPanel}>
          <h2>Idle first render</h2>
          <p>
            The route does not auto-run on page load. Submit the bounded form to request one
            released summary from <code>POST /odeu-sim/run</code>.
          </p>
        </section>
      )}
    </div>
  );
}
