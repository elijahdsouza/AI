// Copies the single-file build to a friendly name next to the project.
// Vite puts the inlined script in <head>; it moves to the end of <body>, after
// <div id="root">, so previewers that add the body after running head scripts
// still find the page's mount point.
import { readFile, writeFile, stat } from "node:fs/promises";
const from = new URL("../dist-single/index.html", import.meta.url);
const to = new URL("../UC-Pro-Group.html", import.meta.url);

let html = await readFile(from, "utf8");
const open = '<script type="module" crossorigin>';
const start = html.indexOf(open);
if (start !== -1) {
  const end = html.indexOf("</script>", start) + "</script>".length;
  const script = '<script type="module">' + html.slice(start + open.length, end);
  html = html.slice(0, start) + html.slice(end);
  const bodyEnd = html.lastIndexOf("</body>");
  html = html.slice(0, bodyEnd) + script + "\n  " + html.slice(bodyEnd);
}
await writeFile(to, html);
console.log(`wrote UC-Pro-Group.html  ${Math.round((await stat(to)).size / 1024)} KB`);
