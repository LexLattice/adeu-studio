const bridge = window.workspaceShell;

const MIN_WIDTHS = {
  left: 330,
  middle: 390,
  right: 350,
  splitter: 8,
};

const state = {
  config: null,
  configPath: "",
  repoRoot: "",
  surfaceEvents: {
    codex: { type: "idle" },
    chatgpt: { type: "idle" },
  },
  drawerMode: "edit",
  currentWidths: { left: 0, middle: 0, right: 0 },
  layoutFrame: 0,
  lastLayoutSignature: "",
  selectedFileRelPath: "",
  workspaceStatuses: {},
};

const els = {
  appShell: document.getElementById("appShell"),
  selectedProjectName: document.getElementById("selectedProjectName"),
  repoPath: document.getElementById("repoPath"),
  workspacePath: document.getElementById("workspacePath"),
  backendStatus: document.getElementById("backendStatus"),
  bindingStatus: document.getElementById("bindingStatus"),
  projectList: document.getElementById("projectList"),
  projectCount: document.getElementById("projectCount"),
  configPath: document.getElementById("configPath"),
  codexSlot: document.getElementById("codexSlot"),
  chatgptSlot: document.getElementById("chatgptSlot"),
  leftSplitter: document.getElementById("leftSplitter"),
  rightSplitter: document.getElementById("rightSplitter"),
  codexStatus: document.getElementById("codexStatus"),
  chatgptStatus: document.getElementById("chatgptStatus"),
  lastEvent: document.getElementById("lastEvent"),
  addProjectButton: document.getElementById("addProjectButton"),
  editProjectButton: document.getElementById("editProjectButton"),
  copyPromptButton: document.getElementById("copyPromptButton"),
  copyHeaderButton: document.getElementById("copyHeaderButton"),
  reloadCodexButton: document.getElementById("reloadCodexButton"),
  reloadChatButton: document.getElementById("reloadChatButton"),
  externalChatButton: document.getElementById("externalChatButton"),
  forceDarkButton: document.getElementById("forceDarkButton"),
  chatSettingsButton: document.getElementById("chatSettingsButton"),
  promptTemplatePreview: document.getElementById("promptTemplatePreview"),
  watchedRulesPreview: document.getElementById("watchedRulesPreview"),
  returnHeaderPreview: document.getElementById("returnHeaderPreview"),
  refreshWorkTreeButton: document.getElementById("refreshWorkTreeButton"),
  workTree: document.getElementById("workTree"),
  previewPath: document.getElementById("previewPath"),
  previewMeta: document.getElementById("previewMeta"),
  filePreview: document.getElementById("filePreview"),
  drawer: document.getElementById("projectDrawer"),
  drawerTitle: document.getElementById("drawerTitle"),
  form: document.getElementById("projectForm"),
  closeDrawerButton: document.getElementById("closeDrawerButton"),
  cancelProjectButton: document.getElementById("cancelProjectButton"),
  chooseRepoButton: document.getElementById("chooseRepoButton"),
  deleteProjectButton: document.getElementById("deleteProjectButton"),
  projectIdInput: document.getElementById("projectIdInput"),
  projectNameInput: document.getElementById("projectNameInput"),
  repoPathInput: document.getElementById("repoPathInput"),
  workspaceKindInput: document.getElementById("workspaceKindInput"),
  workspaceLabelInput: document.getElementById("workspaceLabelInput"),
  wslDistroInput: document.getElementById("wslDistroInput"),
  wslLinuxPathInput: document.getElementById("wslLinuxPathInput"),
  codexModeInput: document.getElementById("codexModeInput"),
  codexLabelInput: document.getElementById("codexLabelInput"),
  codexTargetInput: document.getElementById("codexTargetInput"),
  chatgptUrlInput: document.getElementById("chatgptUrlInput"),
  reduceChromeInput: document.getElementById("reduceChromeInput"),
  reviewPromptInput: document.getElementById("reviewPromptInput"),
  watchedPatternsInput: document.getElementById("watchedPatternsInput"),
  returnHeaderInput: document.getElementById("returnHeaderInput"),
};

function activeProject() {
  if (!state.config) return null;
  return state.config.projects.find((project) => project.id === state.config.selectedProjectId) ?? state.config.projects[0] ?? null;
}

function createId() {
  return `project_${crypto.randomUUID().replace(/-/g, "").slice(0, 12)}`;
}

function shortPath(value) {
  const text = String(value ?? "");
  if (text.length <= 64) return text;
  return `${text.slice(0, 28)}…${text.slice(-32)}`;
}

function clamp(value, min, max) {
  if (max < min) return min;
  return Math.min(max, Math.max(min, value));
}

function projectWorkspace(project) {
  const workspace = project?.workspace;
  if (workspace?.kind === "wsl") {
    return {
      kind: "wsl",
      distro: workspace.distro || "",
      linuxPath: workspace.linuxPath || "/home",
      label: workspace.label || "WSL workspace",
    };
  }
  return {
    kind: "local",
    localPath: workspace?.localPath || project?.repoPath || state.repoRoot || "",
    label: workspace?.label || "Local workspace",
  };
}

function workspaceSummary(project) {
  const workspace = projectWorkspace(project);
  if (workspace.kind === "wsl") {
    return `WSL ${workspace.distro || "default"}:${workspace.linuxPath}`;
  }
  return `Local ${workspace.localPath}`;
}

function workspaceRootValue(project) {
  const workspace = projectWorkspace(project);
  return workspace.kind === "wsl" ? workspace.linuxPath : workspace.localPath;
}

function backendStatusText(project) {
  if (!project) return "backend detached";
  const status = state.workspaceStatuses[project.id];
  if (!status) return "backend attaching…";
  const transport = status.transport ? ` · ${status.transport}` : "";
  if (status.status === "attached") return `backend attached${transport}`;
  if (status.status === "failed") return `backend failed${status.lastError ? ` · ${status.lastError}` : ""}`;
  if (status.status === "closed") return `backend closed${status.lastError ? ` · ${status.lastError}` : ""}`;
  return `backend ${status.status || "unknown"}${transport}`;
}

function updateWorkspaceFieldVisibility() {
  const kind = els.workspaceKindInput?.value || "local";
  for (const element of document.querySelectorAll("[data-workspace-kind]")) {
    element.hidden = element.getAttribute("data-workspace-kind") !== kind;
  }
}
function setLastEvent(message) {
  els.lastEvent.textContent = message;
  els.lastEvent.title = message;
}

function formatBytes(bytes) {
  const number = Number(bytes) || 0;
  if (number < 1024) return `${number} B`;
  if (number < 1024 * 1024) return `${(number / 1024).toFixed(1)} KB`;
  return `${(number / (1024 * 1024)).toFixed(1)} MB`;
}

function surfaceStatusLabel(event) {
  if (!event || event.type === "idle") return "idle";
  if (event.type === "loading") return "loading";
  if (event.type === "loaded") return event.title ? `loaded · ${event.title}` : "loaded";
  if (event.type === "load-failed") return "load failed";
  if (event.type === "navigation-blocked") return "blocked navigation";
  if (event.type === "settings-opened") return "settings requested";
  if (event.type === "settings-open-failed") return "settings failed";
  return event.type;
}

function renderStatus() {
  for (const [surface, element] of [
    ["codex", els.codexStatus],
    ["chatgpt", els.chatgptStatus],
  ]) {
    const event = state.surfaceEvents[surface] ?? { type: "idle" };
    element.textContent = surfaceStatusLabel(event);
    element.title = event.title || event.url || event.type || "idle";
    element.className = "status-dot";
    if (event.type === "loading") element.classList.add("loading");
    if (event.type === "loaded") element.classList.add("loaded");
    if (event.type === "load-failed") element.classList.add("failed");
    if (event.type === "navigation-blocked") element.classList.add("blocked");
    if (event.type === "settings-opened") element.classList.add("settings-opened");
    if (event.type === "settings-open-failed") element.classList.add("settings-open-failed");
  }
}

function renderProjectList() {
  const config = state.config;
  if (!config) return;
  els.projectCount.textContent = String(config.projects.length);
  els.projectList.innerHTML = "";
  for (const project of config.projects) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `project-item${project.id === config.selectedProjectId ? " active" : ""}`;
    button.innerHTML = `
      <strong></strong>
      <span class="truncate mono"></span>
      <span class="truncate"></span>
    `;
    button.querySelector("strong").textContent = project.name;
    button.querySelectorAll("span")[0].textContent = shortPath(workspaceSummary(project));
    button.querySelectorAll("span")[1].textContent = project.surfaceBinding.chatgpt.reviewThreadUrl || "No ChatGPT URL";
    button.addEventListener("click", () => selectProject(project.id));
    els.projectList.appendChild(button);
  }
}

function renderSelectedProject() {
  const project = activeProject();
  if (!project) return;
  const codex = project.surfaceBinding.codex;
  const chat = project.surfaceBinding.chatgpt;
  const workspace = projectWorkspace(project);
  const workspaceText = workspaceSummary(project);

  els.selectedProjectName.textContent = project.name;
  els.repoPath.textContent = project.repoPath;
  els.repoPath.title = project.repoPath;
  if (els.workspacePath) {
    els.workspacePath.textContent = workspaceText;
    els.workspacePath.title = workspaceText;
  }
  if (els.backendStatus) {
    els.backendStatus.textContent = backendStatusText(project);
    els.backendStatus.title = backendStatusText(project);
  }
  els.bindingStatus.textContent = `${workspace.kind.toUpperCase()} · ${codex.mode} Codex · ${chat.reviewThreadUrl ? "ChatGPT bound" : "ChatGPT unbound"}`;

  els.promptTemplatePreview.textContent = project.flowProfile.reviewPromptTemplate;
  els.watchedRulesPreview.textContent = project.flowProfile.watchedFilePatterns.join("\n");
  els.returnHeaderPreview.textContent = project.flowProfile.returnHeader;
}

function getUiRatios() {
  const ui = state.config?.ui ?? {};
  return {
    leftRatio: Number.isFinite(Number(ui.leftRatio)) ? Number(ui.leftRatio) : 0.34,
    middleRatio: Number.isFinite(Number(ui.middleRatio)) ? Number(ui.middleRatio) : 0.3,
  };
}

function computePlaneWidths() {
  const rect = els.appShell.getBoundingClientRect();
  const split = MIN_WIDTHS.splitter;
  const total = Math.max(1, Math.round(rect.width) - split * 2);
  const ratios = getUiRatios();

  const minSum = MIN_WIDTHS.left + MIN_WIDTHS.middle + MIN_WIDTHS.right;
  if (total <= minSum) {
    const scale = total / minSum;
    const left = Math.max(280, Math.floor(MIN_WIDTHS.left * scale));
    const middle = Math.max(330, Math.floor(MIN_WIDTHS.middle * scale));
    const right = Math.max(280, total - left - middle);
    return { left, middle, right, total };
  }

  let left = Math.round(total * ratios.leftRatio);
  left = clamp(left, MIN_WIDTHS.left, total - MIN_WIDTHS.middle - MIN_WIDTHS.right);

  let middle = Math.round(total * ratios.middleRatio);
  middle = clamp(middle, MIN_WIDTHS.middle, total - left - MIN_WIDTHS.right);

  let right = total - left - middle;
  if (right < MIN_WIDTHS.right) {
    const deficit = MIN_WIDTHS.right - right;
    const middleCanGive = Math.max(0, middle - MIN_WIDTHS.middle);
    const giveFromMiddle = Math.min(deficit, middleCanGive);
    middle -= giveFromMiddle;
    left = Math.max(MIN_WIDTHS.left, left - (deficit - giveFromMiddle));
    right = total - left - middle;
  }

  return { left, middle, right, total };
}

function applyPlaneWidths() {
  const widths = computePlaneWidths();
  state.currentWidths = widths;
  document.documentElement.style.setProperty("--left-plane-width", `${widths.left}px`);
  document.documentElement.style.setProperty("--control-plane-width", `${widths.middle}px`);
  return widths;
}

function rectToBounds(rect) {
  return {
    x: Math.round(rect.left),
    y: Math.round(rect.top),
    width: Math.max(1, Math.round(rect.width)),
    height: Math.max(1, Math.round(rect.height)),
  };
}

function sendSurfaceLayout() {
  if (!bridge || !els.codexSlot || !els.chatgptSlot) return;
  const codex = rectToBounds(els.codexSlot.getBoundingClientRect());
  const chatgpt = rectToBounds(els.chatgptSlot.getBoundingClientRect());
  const signature = `${codex.x},${codex.y},${codex.width},${codex.height}|${chatgpt.x},${chatgpt.y},${chatgpt.width},${chatgpt.height}`;
  if (signature === state.lastLayoutSignature) return;
  state.lastLayoutSignature = signature;
  bridge.setSurfaceLayout({ codex, chatgpt }).catch((error) => {
    console.error("Unable to set surface layout", error);
  });
}

function performLayout() {
  applyPlaneWidths();
  sendSurfaceLayout();
}

function scheduleLayout() {
  if (state.layoutFrame) cancelAnimationFrame(state.layoutFrame);
  state.layoutFrame = requestAnimationFrame(() => {
    state.layoutFrame = 0;
    performLayout();
  });
}

function scheduleResizeBurst() {
  state.lastLayoutSignature = "";
  for (const delay of [0, 16, 48, 110, 240, 480]) {
    setTimeout(scheduleLayout, delay);
  }
}

function render() {
  if (!state.config) return;
  els.configPath.textContent = state.configPath;
  els.configPath.title = state.configPath;
  renderProjectList();
  renderSelectedProject();
  renderStatus();
  scheduleResizeBurst();
}

async function saveConfig(config) {
  const result = await bridge.saveConfig(config);
  state.config = result.config;
  state.configPath = result.configPath;
  render();
  return result.config;
}

async function selectProject(projectId) {
  const previous = state.config?.selectedProjectId;
  state.surfaceEvents.codex = { type: "loading" };
  state.surfaceEvents.chatgpt = { type: "loading" };
  renderStatus();
  const result = await bridge.selectProject(projectId);
  state.config = result.config;
  render();
  const project = activeProject();
  setLastEvent(`Selected ${project?.name ?? projectId}.`);
  state.selectedFileRelPath = "";
  if (project && bridge.attachWorkspace) {
    setLastEvent(`Attaching workspace: ${workspaceSummary(project)}…`);
    try {
      const status = await bridge.attachWorkspace(project.id);
      state.workspaceStatuses[project.id] = status;
      renderSelectedProject();
    } catch (error) {
      state.workspaceStatuses[project.id] = { status: "failed", lastError: error.message };
      renderSelectedProject();
    }
  }
  await loadWorkTreeRoot();
  if (previous !== projectId) scheduleResizeBurst();
}

function openDrawer(mode) {
  const project = mode === "new" ? null : activeProject();
  state.drawerMode = mode;
  els.drawer.classList.add("open");
  els.drawer.setAttribute("aria-hidden", "false");
  bridge.setSurfaceVisible(false).catch(() => {});
  els.drawerTitle.textContent = mode === "new" ? "New project" : "Edit project";
  els.deleteProjectButton.style.display = mode === "new" ? "none" : "inline-flex";

  const now = new Date().toISOString();
  const draft = project ?? {
    id: createId(),
    name: "New project",
    repoPath: state.repoRoot || "",
    workspace: { kind: "local", localPath: state.repoRoot || "", label: "Local workspace" },
    surfaceBinding: {
      codex: { mode: "local", target: "codex://local-workspace", label: "Local Codex lane" },
      chatgpt: { reviewThreadUrl: "https://chatgpt.com/", reduceChrome: true },
    },
    flowProfile: {
      reviewPromptTemplate:
        "Review the attached/selected Codex artifact for correctness, risks, missing checks, and concrete next actions. Return concise feedback I can paste back into Codex.",
      watchedFilePatterns: ["**/*REVIEW*.md", "**/*review*.md", "artifacts/**/*.md"],
      returnHeader: "GPT feedback",
    },
    createdAt: now,
    updatedAt: now,
  };

  const workspace = projectWorkspace(draft);
  els.projectIdInput.value = draft.id;
  els.projectNameInput.value = draft.name;
  els.workspaceKindInput.value = workspace.kind;
  els.workspaceLabelInput.value = workspace.label || "";
  els.repoPathInput.value = workspace.kind === "local" ? workspace.localPath : draft.repoPath;
  els.wslDistroInput.value = workspace.kind === "wsl" ? workspace.distro : "";
  els.wslLinuxPathInput.value = workspace.kind === "wsl" ? workspace.linuxPath : "";
  updateWorkspaceFieldVisibility();
  els.codexModeInput.value = draft.surfaceBinding.codex.mode;
  els.codexLabelInput.value = draft.surfaceBinding.codex.label;
  els.codexTargetInput.value = draft.surfaceBinding.codex.target;
  els.chatgptUrlInput.value = draft.surfaceBinding.chatgpt.reviewThreadUrl;
  els.reduceChromeInput.checked = draft.surfaceBinding.chatgpt.reduceChrome !== false;
  els.reviewPromptInput.value = draft.flowProfile.reviewPromptTemplate;
  els.watchedPatternsInput.value = draft.flowProfile.watchedFilePatterns.join(", ");
  els.returnHeaderInput.value = draft.flowProfile.returnHeader;
  setTimeout(() => els.projectNameInput.focus(), 0);
}

function closeDrawer() {
  els.drawer.classList.remove("open");
  els.drawer.setAttribute("aria-hidden", "true");
  bridge.setSurfaceVisible(true).then(scheduleResizeBurst).catch(scheduleResizeBurst);
}

function projectFromForm() {
  const existing = state.config?.projects.find((project) => project.id === els.projectIdInput.value);
  const now = new Date().toISOString();
  const workspaceKind = els.workspaceKindInput.value || "local";
  const workspaceLabel = els.workspaceLabelInput.value.trim();
  const localPath = els.repoPathInput.value.trim();
  const linuxPathInput = els.wslLinuxPathInput.value.trim() || "/home";
  const linuxPath = linuxPathInput.startsWith("/") ? linuxPathInput : `/${linuxPathInput}`;
  const workspace = workspaceKind === "wsl"
    ? {
        kind: "wsl",
        distro: els.wslDistroInput.value.trim(),
        linuxPath,
        label: workspaceLabel || "WSL workspace",
      }
    : {
        kind: "local",
        localPath,
        label: workspaceLabel || "Local workspace",
      };
  const repoPath = workspace.kind === "wsl" ? `wsl:${workspace.distro || "default"}:${workspace.linuxPath}` : workspace.localPath;

  return {
    id: els.projectIdInput.value || createId(),
    name: els.projectNameInput.value.trim() || "Untitled project",
    repoPath,
    workspace,
    surfaceBinding: {
      codex: {
        mode: els.codexModeInput.value,
        target: els.codexTargetInput.value.trim(),
        label: els.codexLabelInput.value.trim() || "Codex target",
      },
      chatgpt: {
        reviewThreadUrl: els.chatgptUrlInput.value.trim() || "https://chatgpt.com/",
        reduceChrome: els.reduceChromeInput.checked,
      },
    },
    flowProfile: {
      reviewPromptTemplate: els.reviewPromptInput.value.trim(),
      watchedFilePatterns: els.watchedPatternsInput.value
        .split(",")
        .map((item) => item.trim())
        .filter(Boolean),
      returnHeader: els.returnHeaderInput.value.trim() || "GPT feedback",
    },
    createdAt: existing?.createdAt ?? now,
    updatedAt: now,
  };
}

async function handleProjectFormSubmit(event) {
  event.preventDefault();
  if (!state.config) return;
  const project = projectFromForm();
  const existingIndex = state.config.projects.findIndex((item) => item.id === project.id);
  const projects = [...state.config.projects];
  if (existingIndex >= 0) projects[existingIndex] = project;
  else projects.push(project);
  const nextConfig = {
    ...state.config,
    selectedProjectId: project.id,
    projects,
  };
  await saveConfig(nextConfig);
  closeDrawer();
  await selectProject(project.id);
  setLastEvent(`Saved binding for ${project.name}.`);
}

async function deleteSelectedProject() {
  if (!state.config) return;
  const project = activeProject();
  if (!project) return;
  const confirmed = confirm(`Delete project binding "${project.name}"? This does not delete files or chats.`);
  if (!confirmed) return;
  const projects = state.config.projects.filter((item) => item.id !== project.id);
  if (!projects.length) {
    alert("At least one project binding is required.");
    return;
  }
  const nextSelected = projects[0].id;
  await saveConfig({ ...state.config, selectedProjectId: nextSelected, projects });
  closeDrawer();
  await selectProject(nextSelected);
  setLastEvent(`Deleted binding for ${project.name}.`);
}

async function copyReviewPrompt() {
  const project = activeProject();
  if (!project) return;
  await bridge.copyText(project.flowProfile.reviewPromptTemplate);
  setLastEvent("Review prompt copied to clipboard.");
}

async function copyReturnHeader() {
  const project = activeProject();
  if (!project) return;
  await bridge.copyText(project.flowProfile.returnHeader);
  setLastEvent("Return header copied to clipboard.");
}

function beginDrag(splitterName, event) {
  if (!state.config) return;
  event.preventDefault();
  const drag = {
    splitterName,
    pointerId: event.pointerId,
    startX: event.clientX,
    startWidths: { ...state.currentWidths },
  };
  document.body.classList.add("dragging");
  bridge.setSurfaceVisible(false).catch(() => {});

  const move = (moveEvent) => {
    const rect = els.appShell.getBoundingClientRect();
    const total = Math.max(1, Math.round(rect.width) - MIN_WIDTHS.splitter * 2);
    let left = drag.startWidths.left;
    let middle = drag.startWidths.middle;

    if (splitterName === "left") {
      left = clamp(moveEvent.clientX - rect.left, MIN_WIDTHS.left, total - MIN_WIDTHS.middle - MIN_WIDTHS.right);
      middle = clamp(middle, MIN_WIDTHS.middle, total - left - MIN_WIDTHS.right);
    } else {
      middle = clamp(
        moveEvent.clientX - rect.left - left - MIN_WIDTHS.splitter,
        MIN_WIDTHS.middle,
        total - left - MIN_WIDTHS.right,
      );
    }

    const right = total - left - middle;
    state.currentWidths = { left, middle, right, total };
    state.config = {
      ...state.config,
      ui: {
        ...(state.config.ui ?? {}),
        leftRatio: left / total,
        middleRatio: middle / total,
      },
    };
    document.documentElement.style.setProperty("--left-plane-width", `${Math.round(left)}px`);
    document.documentElement.style.setProperty("--control-plane-width", `${Math.round(middle)}px`);
  };

  const stop = async () => {
    window.removeEventListener("pointermove", move);
    window.removeEventListener("pointerup", stop);
    window.removeEventListener("pointercancel", stop);
    document.body.classList.remove("dragging");
    await saveConfig(state.config);
    bridge.setSurfaceVisible(true).then(scheduleResizeBurst).catch(scheduleResizeBurst);
  };

  window.addEventListener("pointermove", move);
  window.addEventListener("pointerup", stop);
  window.addEventListener("pointercancel", stop);
}

function renderTreeEntries(container, entries) {
  if (!entries.length) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.textContent = "No visible files in this directory.";
    container.appendChild(empty);
    return;
  }

  for (const entry of entries) {
    const wrapper = document.createElement("div");
    wrapper.className = "tree-node";

    const row = document.createElement("button");
    row.type = "button";
    row.className = `tree-row ${entry.type}`;
    row.dataset.relPath = entry.relPath;
    row.innerHTML = `<span class="twisty"></span><span class="truncate mono"></span>`;
    row.querySelector(".twisty").textContent = entry.type === "dir" ? "▸" : entry.type === "file" ? "•" : "◇";
    row.querySelector(".truncate").textContent = entry.name;
    row.title = entry.relPath;

    const children = document.createElement("div");
    children.className = "tree-children";
    children.hidden = true;

    row.addEventListener("click", () => {
      if (entry.type === "dir") toggleDirectory(entry, row, children);
      else if (entry.type === "file") previewFile(entry.relPath, row);
      else setLastEvent(`Preview unavailable for ${entry.type}: ${entry.relPath}`);
    });

    wrapper.appendChild(row);
    wrapper.appendChild(children);
    container.appendChild(wrapper);
  }
}

async function loadWorkTreeRoot() {
  const project = activeProject();
  if (!project) return;
  els.workTree.innerHTML = `<div class="empty-state">Loading ${project.name}…</div>`;
  resetPreview("Select a text/code file from the work tree.");
  try {
    const result = await bridge.listWorkTree(project.id, "");
    els.workTree.innerHTML = "";
    renderTreeEntries(els.workTree, result.entries);
    if (result.skipped) {
      const skipped = document.createElement("div");
      skipped.className = "empty-state";
      skipped.textContent = `${result.skipped} heavy or extra entries hidden for responsiveness.`;
      els.workTree.appendChild(skipped);
    }
    setLastEvent(`Loaded work tree for ${project.name}.`);
  } catch (error) {
    els.workTree.innerHTML = `<div class="empty-state"></div>`;
    els.workTree.querySelector(".empty-state").textContent = `Work tree error: ${error.message}`;
    setLastEvent(`Work tree error: ${error.message}`);
  }
}

async function toggleDirectory(entry, row, children) {
  if (children.dataset.loaded === "true") {
    children.hidden = !children.hidden;
    row.querySelector(".twisty").textContent = children.hidden ? "▸" : "▾";
    return;
  }

  const project = activeProject();
  if (!project) return;
  row.querySelector(".twisty").textContent = "…";
  children.hidden = false;
  children.innerHTML = `<div class="empty-state">Loading…</div>`;
  try {
    const result = await bridge.listWorkTree(project.id, entry.relPath);
    children.innerHTML = "";
    renderTreeEntries(children, result.entries);
    if (result.skipped) {
      const skipped = document.createElement("div");
      skipped.className = "empty-state";
      skipped.textContent = `${result.skipped} entries hidden.`;
      children.appendChild(skipped);
    }
    children.dataset.loaded = "true";
    row.querySelector(".twisty").textContent = "▾";
  } catch (error) {
    children.innerHTML = `<div class="empty-state"></div>`;
    children.querySelector(".empty-state").textContent = error.message;
    row.querySelector(".twisty").textContent = "!";
  }
}

function resetPreview(message) {
  els.previewPath.textContent = "No file selected";
  els.previewPath.title = "";
  els.previewMeta.textContent = "—";
  els.filePreview.textContent = message;
}

async function previewFile(relPath, row) {
  const project = activeProject();
  if (!project) return;
  for (const selected of els.workTree.querySelectorAll(".tree-row.selected")) selected.classList.remove("selected");
  row?.classList.add("selected");
  state.selectedFileRelPath = relPath;
  els.previewPath.textContent = relPath;
  els.previewPath.title = relPath;
  els.previewMeta.textContent = "loading…";
  els.filePreview.textContent = "Loading preview…";

  try {
    const result = await bridge.readProjectFile(project.id, relPath);
    els.previewPath.textContent = result.relPath;
    els.previewPath.title = result.absolutePath;
    els.previewMeta.textContent = `${formatBytes(result.size)}${result.truncated ? ` · first ${formatBytes(result.limit)}` : ""}`;
    if (result.binary) {
      els.filePreview.textContent = "Binary or non-text file. Preview intentionally disabled in v1.";
    } else {
      els.filePreview.textContent = `${result.truncated ? "/* Preview truncated for responsiveness. */\n\n" : ""}${result.text}`;
    }
    setLastEvent(`Previewing ${result.relPath}.`);
  } catch (error) {
    els.previewMeta.textContent = "error";
    els.filePreview.textContent = error.message;
    setLastEvent(`Preview error: ${error.message}`);
  }
}

function bindEvents() {
  els.addProjectButton.addEventListener("click", () => openDrawer("new"));
  els.editProjectButton.addEventListener("click", () => openDrawer("edit"));
  els.closeDrawerButton.addEventListener("click", closeDrawer);
  els.cancelProjectButton.addEventListener("click", closeDrawer);
  els.form.addEventListener("submit", handleProjectFormSubmit);
  els.deleteProjectButton.addEventListener("click", deleteSelectedProject);
  els.chooseRepoButton.addEventListener("click", async () => {
    const selected = await bridge.chooseDirectory();
    if (selected) els.repoPathInput.value = selected;
  });
  els.workspaceKindInput.addEventListener("change", updateWorkspaceFieldVisibility);
  els.copyPromptButton.addEventListener("click", copyReviewPrompt);
  els.copyHeaderButton.addEventListener("click", copyReturnHeader);
  els.reloadCodexButton.addEventListener("click", () => bridge.reloadSurface("codex"));
  els.reloadChatButton.addEventListener("click", () => bridge.reloadSurface("chatgpt"));
  els.externalChatButton.addEventListener("click", () => bridge.openSurfaceExternal("chatgpt"));
  els.forceDarkButton.addEventListener("click", async () => {
    await bridge.forceChatgptDark();
    setLastEvent("Requested best-effort ChatGPT dark mode.");
  });
  els.chatSettingsButton.addEventListener("click", async () => {
    const result = await bridge.openChatgptSettings();
    setLastEvent(result.ok ? `Requested ChatGPT settings (${result.method}).` : `ChatGPT settings failed (${result.method}).`);
  });
  els.refreshWorkTreeButton.addEventListener("click", loadWorkTreeRoot);

  els.leftSplitter.addEventListener("pointerdown", (event) => beginDrag("left", event));
  els.rightSplitter.addEventListener("pointerdown", (event) => beginDrag("right", event));

  window.addEventListener("resize", scheduleResizeBurst);
  if (window.visualViewport) window.visualViewport.addEventListener("resize", scheduleResizeBurst);
  document.addEventListener("visibilitychange", () => {
    if (!document.hidden) scheduleResizeBurst();
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape" && els.drawer.classList.contains("open")) closeDrawer();
  });

  const resizeObserver = new ResizeObserver(scheduleResizeBurst);
  resizeObserver.observe(els.appShell);
  resizeObserver.observe(els.codexSlot);
  resizeObserver.observe(els.chatgptSlot);

  bridge.onSurfaceEvent((event) => {
    if (event.surface === "codex" || event.surface === "chatgpt") {
      state.surfaceEvents[event.surface] = event;
      renderStatus();
      if (event.type === "loaded") setLastEvent(`${event.surface} loaded: ${event.title || event.url || "ready"}`);
      if (event.type === "load-failed") setLastEvent(`${event.surface} load failed: ${event.errorDescription}`);
      if (event.type === "navigation-blocked") setLastEvent(`${event.surface} blocked navigation: ${event.url}`);
      if (event.type === "settings-opened") setLastEvent(`ChatGPT settings requested via ${event.method}.`);
      if (event.type === "settings-open-failed") setLastEvent(`ChatGPT settings request failed via ${event.method}.`);
    }
  });

  bridge.onShellEvent((event) => {
    if (event.type === "layout-request") scheduleResizeBurst();
    if (event.type === "backend-status" && event.session?.projectId) {
      state.workspaceStatuses[event.session.projectId] = event.session;
      renderSelectedProject();
      if (event.error) setLastEvent(`Workspace backend error: ${event.error}`);
      else if (event.session.status === "attached") setLastEvent(`Workspace backend attached: ${event.session.transport}`);
      else if (event.session.status === "failed") setLastEvent(`Workspace backend failed: ${event.session.lastError || "unknown"}`);
    }
  });
}

async function init() {
  if (!bridge) {
    document.body.innerHTML = "<main style='padding:24px;color:white'>Electron preload bridge is unavailable.</main>";
    return;
  }
  bindEvents();
  const result = await bridge.loadConfig();
  state.config = result.config;
  state.configPath = result.configPath;
  state.repoRoot = result.repoRoot;
  render();
  await selectProject(state.config.selectedProjectId);
}

init().catch((error) => {
  console.error(error);
  setLastEvent(`Startup error: ${error.message}`);
});
