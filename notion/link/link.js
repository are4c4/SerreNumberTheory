import { candidateTargetsAtLine, displayKind } from "../lib/manifest.mjs";

const input = document.getElementById("githubUrl");
const error = document.getElementById("error");
const result = document.getElementById("result");
const targetOptions = document.getElementById("targetOptions");
const meta = document.getElementById("meta");
const output = document.getElementById("output");
const openBtn = document.getElementById("openBtn");
let generated = "";
let selectedTarget = null;
let manifestPromise = null;

const manifest = () => manifestPromise ||= fetch("../data/manifest.json", {cache:"no-store"}).then(response => {
  if (!response.ok) throw new Error(`manifest HTTP ${response.status}`);
  return response.json();
});

function parseGithub(raw) {
  const url = new URL(raw.trim());
  if (url.hostname !== "github.com") throw new Error("github.com のURLを貼り付けてください。");
  const parts = url.pathname.split("/").filter(Boolean);
  if (parts.length < 5 || parts[2] !== "blob") throw new Error("GitHubのファイル表示URLを使用してください。");
  const line = Number((url.hash.match(/L(\d+)/) || [])[1]);
  if (!line) throw new Error("GitHubで行番号をクリックし、#L120 のようなURLにしてください。");
  return {
    repository: `${parts[0]}/${parts[1]}`,
    blobTail: parts.slice(3).map(decodeURIComponent).join("/"),
    line,
  };
}

function rangeText(item) {
  const start = Number(item.startLine || 0);
  const end = Number(item.endLine || start);
  return start === end ? `${start}行` : `${start}–${end}行`;
}

function candidateList(m, file, line) {
  const found = candidateTargetsAtLine(m, file, line);
  const candidates = [];
  const seenDeclarations = new Set();

  for (const item of found.declarations) {
    if (!item.primaryDeclaration || seenDeclarations.has(item.primaryDeclaration)) continue;
    seenDeclarations.add(item.primaryDeclaration);
    candidates.push({
      type:"declaration",
      key:`decl:${item.primaryDeclaration}`,
      item,
      title:`${displayKind(item)}  ${item.primaryDeclaration}`,
      detail:`宣言単位 · ${rangeText(item)}`,
    });
  }

  for (const item of found.scopes) {
    candidates.push({
      type:"scope",
      key:`scope:${item.id}`,
      item,
      title:`${item.kind}  ${item.primaryDeclaration}`,
      detail:`${item.kind}全体 · ${rangeText(item)}`,
    });
  }

  if (found.item) {
    candidates.push({
      type:"item",
      key:`item:${found.item.id}`,
      item:found.item,
      title:`選択したLean項目  ${displayKind(found.item)}`,
      detail:`${found.item.primaryDeclaration || found.item.module} · ${rangeText(found.item)}`,
    });
  }
  return candidates;
}

function preferredCandidate(candidates, line) {
  return candidates.find(candidate =>
    candidate.type === "scope" &&
    Number(candidate.item.startLine) === line
  )
    || candidates.find(candidate => candidate.type === "declaration")
    || candidates.find(candidate => candidate.type === "scope")
    || candidates[0]
    || null;
}

function viewerUrl(target) {
  const viewer = new URL("../", location.href);
  const item = target.item;
  if (target.type === "declaration") {
    viewer.searchParams.set("decl", item.primaryDeclaration);
  } else if (target.type === "scope") {
    viewer.searchParams.set("file", item.file);
    viewer.searchParams.set(item.kind, item.primaryDeclaration);
    viewer.searchParams.set("line", String(item.startLine));
  } else {
    viewer.searchParams.set("file", item.file);
    viewer.searchParams.set("line", String(item.startLine));
  }
  return viewer.toString();
}

function updateGenerated(target) {
  selectedTarget = target;
  generated = target ? viewerUrl(target) : "";
  if (!target) {
    meta.textContent = "";
    output.textContent = "";
    openBtn.removeAttribute("href");
    return;
  }
  const item = target.item;
  meta.textContent = `${target.title} | ${item.file}:${rangeText(item)}`;
  output.textContent = generated;
  openBtn.href = generated;
}

function renderTargets(candidates, preferred) {
  targetOptions.replaceChildren();
  candidates.forEach((candidate, index) => {
    const label = document.createElement("label");
    label.className = "target-option";

    const radio = document.createElement("input");
    radio.type = "radio";
    radio.name = "viewerTarget";
    radio.value = candidate.key;
    radio.checked = candidate === preferred;
    radio.addEventListener("change", () => {
      if (radio.checked) updateGenerated(candidate);
    });

    const text = document.createElement("span");
    text.className = "target-option-text";
    const title = document.createElement("strong");
    title.textContent = candidate.title;
    const detail = document.createElement("small");
    detail.textContent = candidate.detail;
    text.append(title, detail);
    label.append(radio, text);
    targetOptions.appendChild(label);

    if (index === 0 && !preferred) radio.checked = true;
  });
}

document.getElementById("makeBtn").addEventListener("click", async () => {
  generated = "";
  selectedTarget = null;
  error.textContent = "";
  result.hidden = true;
  targetOptions.replaceChildren();

  try {
    const parsed = parseGithub(input.value);
    const m = await manifest();
    if (m.github?.repository && parsed.repository !== m.github.repository) {
      throw new Error(`このViewerは ${m.github.repository} 用です。`);
    }
    const file = Object.keys(m.files || {})
      .filter(candidate => parsed.blobTail === candidate || parsed.blobTail.endsWith("/" + candidate))
      .sort((a, b) => b.length - a.length)[0];
    if (!file) throw new Error("URLに対応するLeanファイルがmanifestに見つかりませんでした。");

    const candidates = candidateList(m, file, parsed.line);
    if (!candidates.length) throw new Error("その行の近くに表示可能なLean項目が見つかりませんでした。");

    const preferred = preferredCandidate(candidates, parsed.line);
    renderTargets(candidates, preferred);
    updateGenerated(preferred || candidates[0]);
    result.hidden = false;
  } catch (e) {
    error.textContent = String(e.message || e);
  }
});

document.getElementById("clearBtn").addEventListener("click", () => {
  generated = "";
  selectedTarget = null;
  input.value = "";
  error.textContent = "";
  output.textContent = "";
  targetOptions.replaceChildren();
  result.hidden = true;
  input.focus();
});

document.getElementById("copyBtn").addEventListener("click", async event => {
  if (!generated) return;
  await navigator.clipboard.writeText(generated);
  const button = event.currentTarget;
  button.textContent = "コピーしました";
  setTimeout(() => { button.textContent = "コピー"; }, 1200);
});
