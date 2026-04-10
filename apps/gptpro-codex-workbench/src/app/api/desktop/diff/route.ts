import { NextRequest, NextResponse } from "next/server";

import { buildDiffDocument, normalizeRepoRelativePath } from "../../../lib/desktop/repo-access";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function GET(request: NextRequest) {
  try {
    const left = normalizeRepoRelativePath(request.nextUrl.searchParams.get("left"));
    const right = normalizeRepoRelativePath(request.nextUrl.searchParams.get("right"));
    if (!left || !right) {
      return NextResponse.json(
        { error: "left and right query parameters are required" },
        { status: 400, headers: { "cache-control": "no-store" } },
      );
    }
    const payload = await buildDiffDocument(left, right);
    return NextResponse.json(payload, { headers: { "cache-control": "no-store" } });
  } catch (error) {
    return NextResponse.json(
      { error: String(error) },
      { status: 400, headers: { "cache-control": "no-store" } },
    );
  }
}
