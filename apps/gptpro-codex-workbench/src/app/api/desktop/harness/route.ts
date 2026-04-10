import { NextResponse } from "next/server";

import { getHarnessSummary } from "../../../lib/desktop/repo-access";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function GET() {
  try {
    const payload = await getHarnessSummary();
    return NextResponse.json(payload, { headers: { "cache-control": "no-store" } });
  } catch (error) {
    return NextResponse.json(
      { error: String(error) },
      { status: 500, headers: { "cache-control": "no-store" } },
    );
  }
}
