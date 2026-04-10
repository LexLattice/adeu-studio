import type { HostBridge } from "../shared/types";

declare global {
  interface Window {
    opusWorkbench: HostBridge;
  }
}

export {};
