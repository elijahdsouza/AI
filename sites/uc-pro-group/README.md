# UC Pro Group landing page

The membership landing page for the Uncommon Collective Pro Group.

## Open it on your computer

**Just want to look at it?** Double-click **`UC-Pro-Group.html`**. It opens in
your browser with nothing to install. (The event photos need an internet connection.)

**Want the React version, to run and edit it?**

1. Install **Node.js** once: the **LTS** version from [nodejs.org](https://nodejs.org/en/download).
   Click through the installer with the default options.
2. **Windows:** double-click **`start-windows.bat`** in this folder.
   **Mac:** double-click **`start-mac.command`**. The first time, right-click it and choose Open.
3. The first run installs everything, which takes a minute or two. Then your browser
   opens the site at **http://localhost:5173**. Leave the black window open while you
   use it; closing it stops the site. Edits to `src/content.ts` appear the moment you save.

Prefer a terminal? In this folder: `npm install` once, then `npm run dev`.

**Why double-clicking `index.html` shows a blank page:** the Hostinger build
(`dist/` and `uc-pro-group-dist.zip`) loads its code from separate files, and
browsers block that for pages opened straight from your computer. It works once it's
uploaded to Hostinger. To check it locally first, run `npm run preview`.

---

## Change the words

Every word on the page is in **`src/content.ts`**, in page order. Change it and save.

- `site.waitlistUrl`: paste your form tool's link here (Tally, Typeform, Mailchimp...).
  Every "Join the waitlist" button uses it, and links starting with `http` open in a new tab.
- `site.deadlineISO` / `site.deadlineLabel`: the founding-rate deadline behind the countdown.
- `*word*` in a heading marks the accent word (gold on dark sections, a gold
  highlighter stripe on light ones).
- Anything written `[TBC · ...]` shows on the page as a dashed placeholder tag
  until you replace it.

## Photos

`src/images.ts` maps each photo slot to an image. To use your own photo, drop it
into **`src/assets/photos/`** named after its slot (`.jpg`, `.png` or `.webp`).
A local file always wins over the online one. No code changes needed.

| Slot | Where it appears |
|---|---|
| `dinner`, `podcast`, `industry`, `cowork`, `speaking`, `games` | "Experiences" cards |
| `video`, `grant`, `marketing`, `social`, `legal`, `coaching` | "Growth services" cards |
| `coworkWide` | Beside "What a month inside looks like" |
| `walk` | Above the pricing |
| `toast` | The closing section |

The real group photo is `src/assets/table.jpg`. It carries the hero and the
"What we believe" moment.

To download the current generated photos so every build works offline:

```bash
npm run fetch-images     # saves them into src/assets/photos/
```

## Build

```bash
npm run build          # dist/: the site for Hostinger
npm run build:single   # UC-Pro-Group.html: the one-file version
npm run build:all      # both
npm run preview        # serves dist/ locally to check it
```

## Put it on Hostinger (subdomain)

1. hPanel → **Domains → Subdomains**: create one, for example `pro.uncommoncollectiveau.com`.
   Note the folder it creates (for example `public_html/pro`).
2. Run `npm run build`.
3. hPanel → **File Manager** → open that folder → upload everything **inside** `dist/`
   (or upload `uc-pro-group-dist.zip` and extract it there). `index.html` must sit
   directly in the subdomain folder.
4. Turn on SSL for the subdomain in hPanel if it isn't already.

The build uses relative paths, so it works in any folder with no server setup.

## Motion, on purpose

Most sections use one quiet entrance: a fade and a 14px rise, once. The larger
effects are kept to the places that carry the story:

| Where | Effect |
|---|---|
| Hero | The gold U magnet, the logo's own shape, drawn in particles that follow the cursor. The photo, the magnet and the words move at different depths. |
| The problem, and "What a month inside looks like" | The section holds still while the cards travel in sideways |
| The alternatives, and the testimonials | Cards fly in from past the right edge as you scroll |
| What we believe | The page's signature moment: the belief lights up word by word, then a gold U opens onto the real room |

Visitors who set "reduce motion" on their device get the same page with the
movement removed. The hero has a pause button, so any moving element can be stopped.

To compare the founder story on green instead of gold, add `?story=green` to the address.

## Stack

Vite, React 19, TypeScript, Tailwind CSS 4, Motion (`motion/react`), lucide icons,
self-hosted fonts (Playfair Display, Poppins, IBM Plex Mono). The one-file build
uses `vite-plugin-singlefile`. The design brief lives in
`scrollcraft/builds/uc-pro-group/BRIEF.md` at the repo root.
