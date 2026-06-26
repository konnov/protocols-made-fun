import fs from "node:fs";
import path from "node:path";

const siteDir = path.join(process.cwd(), "_site");

if (fs.existsSync(siteDir)) {
  fs.rmSync(siteDir, { recursive: true, force: true });
}
