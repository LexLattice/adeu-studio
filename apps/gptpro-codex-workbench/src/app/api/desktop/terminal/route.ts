import { NextRequest, NextResponse } from "next/server";

import { isTerminalCommandId } from "../../../codex-workbench/contract";
import { normalizeRepoRelativePath, runTerminalSnapshot } from "../../../lib/desktop/repo-access";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

export async function GET(request: NextRequest) {
  try {
    const commandParam = (request.nextUrl.searchParams.get("command") || "pwd").trim();
    if (!isTerminalCommandId(commandParam)) {
      return NextResponse.json(
        { error: `unsupported command: ${commandParam}` },
        { status: 400, headers: { "cache-control": "no-store" } },
      );
    }
    const cwd = normalizeRepoRelativePath(request.nextUrl.searchParams.get("cwd"));
    const payload = await runTerminalSnapshot(commandParam, cwd);
    return NextResponse.json(payload, { headers: { "cache-control": "no-store" } });
  } catch (error) {
    return NextResponse.json(
      { error: String(error) },
      { status: 400, headers: { "cache-control": "no-store" } },
    );
  }
}
