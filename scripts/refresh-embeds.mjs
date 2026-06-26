import fs from "node:fs";
import path from "node:path";

const root = process.cwd();
const postsDir = path.join(root, "_posts");
const cachePath = path.join(root, ".cache", "github-embeds.json");

function key(url, lang, lines) {
  return `${url} ${lang || "text"} ${lines || ""}`.trim();
}

function selectLines(text, ranges) {
  if (!ranges) {
    return text;
  }
  const sourceLines = text.split(/\r?\n/);
  const selected = [];
  for (const range of ranges.split(",")) {
    const match = range.match(/^(\d+)-(\d+)$/);
    if (!match) {
      continue;
    }
    const start = Number(match[1]);
    const end = Number(match[2]);
    selected.push(...sourceLines.slice(start - 1, end));
  }
  return selected.join("\n");
}

const requests = new Map();
for (const file of fs.readdirSync(postsDir)) {
  if (!file.endsWith(".md")) {
    continue;
  }
  const text = fs.readFileSync(path.join(postsDir, file), "utf8");
  const pattern = /\{%\s*github_embed\s+([\s\S]*?)%\}/g;
  let match;
  while ((match = pattern.exec(text)) !== null) {
    const parts = match[1].trim().split(/\s+/);
    const url = parts[0];
    const lang = parts[1] || "text";
    const lines = parts[2] || "";
    requests.set(key(url, lang, lines), { url, lang, lines });
  }
}

const cache = {};
for (const [requestKey, request] of requests.entries()) {
  process.stdout.write(`Fetching ${requestKey}\n`);
  const response = await fetch(request.url);
  if (!response.ok) {
    throw new Error(`Failed to fetch ${request.url}: ${response.status} ${response.statusText}`);
  }
  const text = await response.text();
  cache[requestKey] = {
    ...request,
    code: selectLines(text, request.lines),
  };
}

fs.mkdirSync(path.dirname(cachePath), { recursive: true });
fs.writeFileSync(cachePath, `${JSON.stringify(cache, null, 2)}\n`);
process.stdout.write(`Wrote ${requests.size} embeds to ${path.relative(root, cachePath)}\n`);
