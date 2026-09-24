# Installed skills

These are committed to the repo on purpose. Cloud sessions start from a fresh
container, so anything installed under `~/.claude/skills` is gone next time.
Skills in `.claude/skills/` travel with the repo and load in every session
that opens it, with nothing to reinstall.

Each folder is a copy of the upstream skill at the commit below. Every file was
read or pattern-scanned before it was committed (remote fetches, pipe-to-shell,
credential paths, hidden Unicode, instruction-injection phrasing). Nothing
hostile was found.

| Skill | Upstream | Path in repo | Commit | Licence |
|---|---|---|---|---|
| scroll-craft | nateherkai/scroll-craft | (installed earlier) | v0.3.0 | MIT |
| taste-skill | Leonxlnx/taste-skill | skills/taste-skill | c184364c5865 | MIT |
| web-design-guidelines | vercel-labs/agent-skills | skills/web-design-guidelines | 063bee94c3f4 | MIT (README; no LICENSE file upstream) |
| ui-ux-pro-max | nextlevelbuilder/ui-ux-pro-max-skill | .claude/skills/ui-ux-pro-max | dcc40ff5133e | MIT |
| design-system | nextlevelbuilder/ui-ux-pro-max-skill | .claude/skills/design-system | dcc40ff5133e | MIT |
| ccd-create-design-system | bluzir/claude-code-design | .claude/skills/create-design-system | ce68c84edb8b | MIT (README; no LICENSE file upstream) |
| ccd-animated-video | bluzir/claude-code-design | .claude/skills/animated-video | ce68c84edb8b | MIT (README; no LICENSE file upstream) |
| impeccable | pbakaus/impeccable | .claude/skills/impeccable | e0881d2de397 | Apache-2.0 (LICENSE + NOTICE.md carried) |
| emil-design-eng | emilkowalski/skills | skills/emil-design-eng | d16ebe60d09a | MIT |
| text-to-lottie | diffusionstudio/lottie | skills/text-to-lottie | 3c72912fad54 | MIT |
| humanizer | blader/humanizer | (repo root) | 9862685f575c | MIT |
| find-skills | vercel-labs/skills | skills/find-skills | 7407f3893ad4 | MIT |
| design-motion-principles | kylezantos/design-motion-principles | skills/design-motion-principles | 4a9ca879f24a | MIT |
| motion-dev-animations | 199-biotechnologies/motion-dev-animations-skill | (repo root) | 3feedfb4dba8 | MIT |
| framer-motion | mindrally/skills | framer-motion | 97184105b5da | Apache-2.0 (LICENSE file; README says MIT) |

## Local changes

- **Renamed** so the folder matches the `name:` in its frontmatter: `taste-skill`
  (upstream `design-taste-frontend`), `ccd-create-design-system`
  (`create-design-system`), `ccd-animated-video` (`animated-video`). Only the
  `name:` line was edited.
- **Left out**: `.git`, `.github`, test suites, plugin manifests, a stale
  `SKILL.md.backup`. None are read when a skill runs.
- **Added** the upstream LICENSE where the skill folder didn't already ship one.
- **ccd-animated-video and ccd-create-design-system** belong to a larger suite
  (claude-code-design) whose other skills and commands aren't installed. Each
  now opens with a "Local setup (this repo)" table mapping those references to
  what exists here. ccd-animated-video also bundles `starters/animations.jsx`
  from the same upstream commit, and its copy step points at that file.

## What reaches the network when used

- **impeccable** downloads its engine binary from the author's GitHub releases on
  first run each session, checks it against the `.sha256` published beside it,
  and caches it in `~/.impeccable`. The checksum comes from the same release, so
  it catches a corrupted download, not a compromised release.
- **web-design-guidelines** fetches its rule list at use time from
  `raw.githubusercontent.com/vercel-labs/web-interface-guidelines`.
- **find-skills** searches the skills.sh registry, which this environment's
  network policy blocks. `npx skills add owner/repo` still works because it goes
  straight to GitHub.
- **design-system** has a `fetch-background.py` that pulls Pexels stock photos.
  Stock imagery was cut from the UC page, so don't use it there.
- **ccd-animated-video** pages load React and Babel from a CDN. unpkg.com and
  cdn.jsdelivr.net are blocked in the cloud environment (the npm registry is
  not), so previews here need local copies installed from npm.

## Known quirk

`ui-ux-pro-max/SKILL.md` writes its commands as
`python "${CLAUDE_PLUGIN_ROOT}/.claude/skills/ui-ux-pro-max/scripts/search.py"`.
That variable is only set for plugin installs. From the repo root, run
`python3 .claude/skills/ui-ux-pro-max/scripts/search.py "<query>" --domain <domain>`.

## Not installed here, and why

- **21st.dev** is an MCP server that needs an API key, not a skill. Add it as an
  MCP server with your key if you want it.
- **Playwright** is already in the environment (Chromium preinstalled).
- **session-start-hook** is built into Claude Code.

## Updating a skill

Clone the upstream repo at the newer commit, re-run the scan, replace the folder,
reapply the rename if it's one of the three above, and update the commit in the
table.
