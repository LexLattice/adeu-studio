function decodePayload() {
  const raw = window.location.hash.slice(1);
  if (!raw) return null;
  try {
    const normalized = raw.replace(/-/g, "+").replace(/_/g, "/");
    const json = decodeURIComponent(
      Array.from(atob(normalized), (char) => `%${char.charCodeAt(0).toString(16).padStart(2, "0")}`).join(""),
    );
    return JSON.parse(json);
  } catch (error) {
    console.error("Unable to decode local Codex surface payload", error);
    return null;
  }
}

function setText(id, value) {
  const element = document.getElementById(id);
  if (element) element.textContent = String(value ?? "—");
}

function writeClipboard(text) {
  navigator.clipboard?.writeText(String(text ?? "")).catch(() => {
    const textarea = document.createElement("textarea");
    textarea.value = String(text ?? "");
    document.body.appendChild(textarea);
    textarea.select();
    document.execCommand("copy");
    textarea.remove();
  });
}

function addMessage(role, text, extraClass = "") {
  const transcript = document.getElementById("transcript");
  const message = document.createElement("article");
  message.className = `message ${role} ${extraClass}`.trim();
  message.innerHTML = `<div class="role"></div><div class="bubble"></div>`;
  message.querySelector(".role").textContent = role === "user" ? "You" : role === "assistant" ? "Codex" : "System";
  message.querySelector(".bubble").textContent = text;
  transcript.appendChild(message);
  transcript.scrollTop = transcript.scrollHeight;
}

const payload = decodePayload();
const project = payload?.project;

if (project) {
  const workspace = project.workspace?.kind === "wsl"
    ? `WSL ${project.workspace.distro || "default"}:${project.workspace.linuxPath}`
    : `Local ${project.workspace?.localPath || project.repoPath}`;
  setText("projectName", project.name);
  setText("repoPath", workspace);
  setText("bindingLabel", `${project.codex?.mode ?? "local"} · ${project.codex?.label ?? "Codex target"}`);

  addMessage(
    "system",
    payload.shell?.doctrine ??
      "Codex plane is the work chat. ADEU control plane owns the binding. ChatGPT plane remains the review thread.",
    "system",
  );
  addMessage(
    "assistant",
    `Workspace bound.\n\nWorkspace: ${workspace}\nRepo display: ${project.repoPath}\nCodex target: ${project.codex?.target ?? "local"}\n\nThis local lane is a lightweight Codex-compatible work chat surface. Point the Codex binding at a local app-server URL when you want to replace it with a real Codex surface.`,
  );

  document.getElementById("copyPromptButton").addEventListener("click", () => {
    writeClipboard(project.flowProfile?.reviewPromptTemplate ?? "");
  });
  document.getElementById("copyHeaderButton").addEventListener("click", () => {
    writeClipboard(project.flowProfile?.returnHeader ?? "GPT feedback");
  });
} else {
  setText("projectName", "Codex work companion");
  addMessage("system", "No project payload was supplied.", "system");
}

const composerForm = document.getElementById("composerForm");
const composerInput = document.getElementById("composerInput");

composerForm.addEventListener("submit", (event) => {
  event.preventDefault();
  const text = composerInput.value.trim();
  if (!text) return;
  addMessage("user", text);
  composerInput.value = "";
  addMessage(
    "assistant",
    "Queued locally in the v1 shell lane. This placeholder intentionally does not automate Codex execution yet. Use an embedded Codex URL binding for a real app-server surface, or paste this note into Codex manually.",
  );
});
