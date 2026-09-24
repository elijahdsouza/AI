// Copies the single-file build to a friendly name next to the project.
import { copyFile, stat } from "node:fs/promises";
const from = new URL("../dist-single/index.html", import.meta.url);
const to = new URL("../UC-Pro-Group.html", import.meta.url);
await copyFile(from, to);
console.log(`wrote UC-Pro-Group.html  ${Math.round((await stat(to)).size / 1024)} KB`);
