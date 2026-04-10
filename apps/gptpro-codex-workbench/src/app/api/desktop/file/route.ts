import { NextRequest, NextResponse } from "next/server";

import { normalizeRepoRelativePath, readRepoFile } from "../../../lib/desktop/repo-access";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function GET(request: NextRequest) {
  try {
    const pathValue = normalizeRepoRelativePath(request.nextUrl.searchParams.get("path"));
    const payload = await readRepoFile(pathValue);
    return NextResponse.json(payload, { headers: { "cache-control": "no-store" } });
  } catch (error) {
    return NextResponse.json(
      { error: String(error) },
      { status: 400, headers: { "cache-control": "no-store" } },
    );
  }
}
