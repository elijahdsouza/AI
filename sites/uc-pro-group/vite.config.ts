import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import tailwindcss from "@tailwindcss/vite";
import { viteSingleFile } from "vite-plugin-singlefile";

// `vite build`                 -> dist/         (upload to Hostinger)
// `vite build --mode single`   -> dist-single/  (one self-contained HTML file)
export default defineConfig(({ mode }) => {
  const single = mode === "single";
  return {
    base: "./",
    plugins: [react(), tailwindcss(), ...(single ? [viteSingleFile()] : [])],
    build: {
      outDir: single ? "dist-single" : "dist",
      // Inline fonts and photos into the single file; keep them as files otherwise.
      assetsInlineLimit: single ? 100_000_000 : 4096,
    },
  };
});
