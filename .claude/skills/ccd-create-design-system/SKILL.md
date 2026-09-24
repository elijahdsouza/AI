---
name: ccd-create-design-system
description: Extract or build a design system (tokens, components, style guide). Use for "design system", "style guide", "tokens", "UI kit".
argument-hint: <source: codebase path, github URL, "from scratch">
allowed-tools: Read Write Edit Glob Grep Bash(cp:*) Bash(open:*) Bash(mkdir:*) mcp__chrome-devtools__*
---

# Create Design System

## Local setup (this repo)

This skill comes from the claude-code-design suite. Only this skill and
ccd-animated-video are installed here, so resolve its references like this:

| Upstream reference | Use here |
|---|---|
| `/register-asset` and `assets.html` (Phase 3) | Not installed. Skip Phase 3 |
| `/ingest-github` | Not installed. Clone the repo and treat it as a local codebase (source 1) |
| `Skill: frontend-design` | `taste-skill` |
| `/make-deck`, `/interactive-prototype`, `/use-design-system` | Not installed |
| `~/.claude/design-systems/` registry (Phases 0 and 5) | Wiped between cloud sessions. Commit `.claude/design-tokens.json` to the repo instead; that is what persists |

Produce a living HTML style guide with colors, typography, spacing, radii, shadows, and components. Uses `register-asset` to feed `assets.html`.

## Phase 0 — Registry check (avoid re-extracting what you already have)

Before anything else:
1. `Bash(ls ~/.claude/design-systems/ 2>/dev/null)` — list existing org-level design systems
2. If the user's brief mentions a brand matching one of the folder names → **don't extract, load existing**: `Read ~/.claude/design-systems/<name>/tokens.json`, report "Using <name> from registry."
3. If no brand match but registry has items → `AskUserQuestion`: "Use existing system (list them) / Extract new / Decide for me"

Skip Phase 0 only if user explicitly said "create new".

## Phase 1 — Source

Four sources, in order of preference:

**0. Existing registry** — handled in Phase 0. If loaded, jump to Phase 2 (Build) directly.

**1. Local codebase** (path provided):
- `Glob`: `**/theme.{ts,js,json}`, `**/tokens.{css,scss}`, `**/tailwind.config.*`, `**/_variables.*`, `**/colors.*`, `**/styles.css`
- `Read` each; extract:
  - Hex/oklch/rgb colors → name + value + role (primary/secondary/accent/neutral/semantic)
  - Font families + weights + sizes
  - Spacing scale (4px/8px/etc.)
  - Border radii
  - Shadows
- `Read` a few component files to understand patterns

**2. GitHub URL** — delegate to `/ingest-github` first, then continue here with the resulting `artifacts/ingested/*-tokens.json`

**3. From scratch / screenshot / brand** — invoke `Skill: frontend-design`; `AskUserQuestion` about vibe, reference brands, emotional register

## Phase 2 — Build

Create `artifacts/design-system.html` with a section per group. Use `data-design-group` attrs so `register-asset` can pick them up.

```html
<section data-design-group="Colors">
  <h2>Colors</h2>
  <div class="swatch-grid">
    <!-- each swatch has name + hex + role -->
  </div>
</section>
<section data-design-group="Type">
  <h2>Typography</h2>
  <!-- sample text at each level: display, H1, H2, body, small -->
</section>
<section data-design-group="Spacing">
  <!-- visual bars for 4, 8, 12, 16, 24, 32... -->
</section>
<section data-design-group="Components">
  <!-- live-rendered buttons, form elements, cards, badges -->
</section>
<section data-design-group="Brand">
  <!-- logo usage, tone of voice, example composition -->
</section>
```

Use real values from source, not invented ones. Every component is live HTML+CSS, not screenshots.

## Phase 3 — Register

For each section:
```
/register-asset artifacts/design-system.html --group Colors --asset "Brand palette" --subtitle "7 colors, semantic roles"
```

Runs once per group. `assets.html` will show each as a card.

## Phase 4 — Persistent context

Write `.claude/design-tokens.json` for future skills in THIS project to reference:
```json
{
  "name": "brand-slug",
  "colors": { "primary": "#D97757", ... },
  "fonts": { "display": "...", "body": "..." },
  "spacing": [4, 8, 12, 16, 24, 32, 48],
  "radii": { "sm": 4, "md": 8, "lg": 16 }
}
```

Subsequent `/make-deck`, `/interactive-prototype` skills should `Read` this file to auto-apply.

## Phase 5 — Offer registry save (cross-project reuse)

If the system is brand-specific (not generic "minimal monochrome" but e.g. "Acme Corp"), ask:

> "Save to `~/.claude/design-systems/<slug>/` for reuse across projects?"

If yes:
1. `Bash(mkdir -p ~/.claude/design-systems/<slug>)`
2. Copy `tokens.json` and `artifacts/design-system.html` → `~/.claude/design-systems/<slug>/`
3. Report: "Saved to registry. Future projects can `/use-design-system <slug>` or auto-detect via brand keyword in brief."

The registry format:
```
~/.claude/design-systems/
├── acme/
│   ├── tokens.json
│   └── preview.html           # (optional) visual reference
├── company-x/
│   └── tokens.json
└── minimal-mono/
    └── tokens.json
```

Any Claude Code session in any project sees this registry via Phase 0 of workflow skills.
