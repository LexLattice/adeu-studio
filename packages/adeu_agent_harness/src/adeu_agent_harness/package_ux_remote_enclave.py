from __future__ import annotations

from .package_ux import DEPLOYMENT_MODE_REMOTE_ENCLAVE, main_for_mode


def main(argv: list[str] | None = None) -> int:
    return main_for_mode(expected_mode=DEPLOYMENT_MODE_REMOTE_ENCLAVE, argv=argv)


if __name__ == "__main__":
    raise SystemExit(main())
