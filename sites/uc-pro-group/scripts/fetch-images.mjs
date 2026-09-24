// Downloads the Higgsfield photos into src/assets/photos/ so builds use local
// copies and the single-file build works offline.
//   npm run fetch-images
import { readFile, writeFile, readdir } from "node:fs/promises";

const src = await readFile(new URL("../src/images.ts", import.meta.url), "utf8");
const cdn = src.match(/const CDN = "([^"]+)"/)[1];
const entries = [...src.matchAll(/^\s+(\w+): "(hf_[^"]+)",$/gm)];
const dir = new URL("../src/assets/photos/", import.meta.url);

let ok = 0;
for (const [, key, id] of entries) {
  const out = new URL(`${key}.webp`, dir);
  const have = (await readdir(dir)).find((f) => f.replace(/\.[^.]+$/, "") === key);
  if (have) { console.log(`skip  ${key} (have ${have})`); ok++; continue; }
  const res = await fetch(`${cdn}${id}_min.webp`);
  if (!res.ok) { console.error(`fail  ${key}: HTTP ${res.status}`); continue; }
  await writeFile(out, Buffer.from(await res.arrayBuffer()));
  console.log(`saved ${key}.webp`); ok++;
}
console.log(`${ok}/${entries.length} photos in src/assets/photos/`);
