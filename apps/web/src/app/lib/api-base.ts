export function apiBase(): string {
  return process.env.NEXT_PUBLIC_ADEU_API_URL || "http://localhost:8000";
}
