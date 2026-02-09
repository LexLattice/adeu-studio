export const DEFAULT_API_BASE_URL = "http://localhost:8000";

export function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || DEFAULT_API_BASE_URL;
}
