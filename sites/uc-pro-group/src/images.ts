// Photos. Real UC photos from uncommoncollectiveau.com live in src/assets/ and
// src/assets/photos/ (speaking, games, industry, cowork); the rest were generated
// with Higgsfield (Nano Banana 2) and load from its CDN. Run `npm run fetch-images`
// to download those too, after which every build is fully offline. Drop a file
// with the same name into src/assets/photos/ to replace any image with your own.
import groupPhoto from "./assets/table.jpg";

const CDN = "https://d8j0ntlcm91z4.cloudfront.net/user_3DYZO3a1JqlMj1bd9WwaeBKEITS/";

export const remote: Record<string, string> = {
  dinner: "hf_20260924_025533_cf5437e3-0ac6-44a4-b09b-383d22d7cd06",
  podcast: "hf_20260924_025533_d37ba09a-2e32-4a86-bce0-2cf971302436",
  industry: "hf_20260924_025532_43dff25f-7959-4b95-9ad9-f3493a8ea400",
  cowork: "hf_20260924_025533_7e252194-7712-4e03-a55b-5b1832072aae",
  speaking: "hf_20260924_025533_faf61b24-1333-40eb-af2f-b7934d5f2381",
  games: "hf_20260924_025533_20a7fda5-3c15-4bf3-be2e-70c4585ed7a0",
  video: "hf_20260924_025533_5bf52bed-5488-4c3c-9175-339fd7d4ea10",
  grant: "hf_20260924_025533_97675faa-b38a-4a9d-b729-8945d526faf7",
  marketing: "hf_20260924_025533_1c5d41a5-42e8-4a9c-8fef-149e06c498f9",
  social: "hf_20260924_025533_3ed2bd8a-7959-4a40-99e5-71057e709693",
  legal: "hf_20260924_025532_e736874d-3c3f-4077-8e8b-69bcbdb082f7",
  coaching: "hf_20260924_025534_845f9865-b317-497b-a471-d6387f50a5d4",
  coworkWide: "hf_20260924_025545_3387747e-cf3b-4841-8218-51b608163c82",
  walk: "hf_20260924_025545_a482441a-6df3-4db6-89d0-29179d3a80b0",
  toast: "hf_20260924_025545_bbc43f53-7ac3-4427-95c9-2e74bbe1c6b2",
};

const local = import.meta.glob("./assets/photos/*.{webp,jpg,jpeg,png}", {
  eager: true,
  query: "?url",
  import: "default",
}) as Record<string, string>;

function localFor(key: string): string | undefined {
  const hit = Object.keys(local).find((p) => p.split("/").pop()!.replace(/\.\w+$/, "") === key);
  return hit ? local[hit] : undefined;
}

export function img(key: string): string {
  return localFor(key) ?? `${CDN}${remote[key]}_min.webp`;
}

export const group = groupPhoto;
export { default as crowd } from "./assets/hero-crowd.jpg";
export { default as logoWhite } from "./assets/uc-logo-white.png";
