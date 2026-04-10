import type { Metadata } from "next";

import { OdeuSimClient } from "./odeu-sim-client";

export const metadata: Metadata = {
  title: "ODEU Simulation Summary | ADEU Studio",
};

export default function OdeuSimPage() {
  return <OdeuSimClient />;
}
