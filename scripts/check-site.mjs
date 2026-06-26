import fs from "node:fs";
import path from "node:path";

const root = process.cwd();
const siteDir = path.join(root, "_site");

function walk(dir) {
  const entries = [];
  for (const name of fs.readdirSync(dir)) {
    const full = path.join(dir, name);
    const stat = fs.statSync(full);
    if (stat.isDirectory()) {
      entries.push(...walk(full));
    } else {
      entries.push(full);
    }
  }
  return entries;
}

function existsSitePath(urlPath) {
  const clean = decodeURI(urlPath.split("#")[0].split("?")[0]);
  if (!clean || clean === "/") {
    return fs.existsSync(path.join(siteDir, "index.html"));
  }
  const withoutSlash = clean.replace(/^\//, "");
  return (
    fs.existsSync(path.join(siteDir, withoutSlash)) ||
    fs.existsSync(path.join(siteDir, withoutSlash, "index.html"))
  );
}

const htmlFiles = walk(siteDir).filter((file) => file.endsWith(".html") || file.endsWith(".xml"));
const failures = [];

for (const file of htmlFiles) {
  const html = fs.readFileSync(file, "utf8");
  const relativeFile = path.relative(root, file);
  const redirectMatch = html.match(/<meta\s+http-equiv=["']refresh["']\s+content=["']0;\s*url=([^"']+)["']/i);
  const isRedirect = Boolean(redirectMatch);
  if (/\{\{\s*[\w'"/.-]/.test(html) || /\{%\s*\w/.test(html)) {
    failures.push(`${relativeFile} contains unrendered template syntax`);
  }
  if (file.endsWith(".html") && html.includes("highlight.min.js")) {
    failures.push(`${relativeFile} includes client-side Highlight.js`);
  }
  if (/\[[^\]\n]+]\[[^\]\n]*]/.test(html)) {
    failures.push(`${relativeFile} contains unresolved Markdown reference links`);
  }
  if (/^#{1,6}\s+\S/m.test(html)) {
    failures.push(`${relativeFile} contains an unrendered Markdown heading`);
  }
  if (/<a\s+id=["'][^"']+["']\s*\/?>/i.test(html)) {
    failures.push(`${relativeFile} contains a legacy line-only anchor tag`);
  }
  if (!isRedirect && /https:\/\/protocols-made-fun\.com\/(?:[^/"'<]+\/)+\d{4}\/\d{2}\/\d{2}\/[^/"'<]+\.html/.test(html)) {
    failures.push(`${relativeFile} contains an absolute old-style post URL`);
  }
  if (isRedirect) {
    const target = redirectMatch[1];
    const canonicalMatch = html.match(/<link\s+rel=["']canonical["']\s+href=["']([^"']+)["']/i);
    if (!canonicalMatch || !canonicalMatch[1].endsWith(target)) {
      failures.push(`${relativeFile} redirect canonical does not match ${target}`);
    }
  }
  const attrPattern = /\b(?:href|src)=["']([^"']+)["']/g;
  let match;
  while ((match = attrPattern.exec(html)) !== null) {
    const value = match[1];
    if (
      value.startsWith("http://") ||
      value.startsWith("https://") ||
      value.startsWith("//") ||
      value.startsWith("mailto:") ||
      value.startsWith("javascript:") ||
      value.startsWith("data:")
    ) {
      continue;
    }
    if (!value.startsWith("/")) {
      continue;
    }
    if (!isRedirect && /^\/(?:[^/"'?]+\/)+\d{4}\/\d{2}\/\d{2}\/[^/"'?]+\.html(?:[#?].*)?$/.test(value)) {
      failures.push(`${relativeFile} links to old-style post URL ${value}`);
    }
    if (!existsSitePath(value)) {
      failures.push(`${relativeFile} links missing local path ${value}`);
    }
  }
}

const index = fs.readFileSync(path.join(siteDir, "index.html"), "utf8");
if (!index.includes("/assets/css/highlight-light.css") || !index.includes("/assets/css/highlight-dark.css")) {
  failures.push("index.html is missing light/dark highlight stylesheet links");
}

if (failures.length > 0) {
  for (const failure of failures) {
    process.stderr.write(`${failure}\n`);
  }
  process.exit(1);
}

process.stdout.write(`Checked ${htmlFiles.length} generated HTML/XML files\n`);
