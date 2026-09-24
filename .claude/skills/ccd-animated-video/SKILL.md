---
name: ccd-animated-video
description: Build animated motion design (explainer, transition reel, product intro). Uses Stage/Sprite timeline from animations.jsx for in-browser compositions or Remotion for full video/MP4 workflows.
argument-hint: <what to animate>
allowed-tools: Read Write Edit Bash(cp:*) Bash(open:*) Bash(mkdir:*) mcp__chrome-devtools__*
---

# Animated Video

Two paths depending on complexity. **Decide first, tell the user which path you're taking.**

## Phase 0 — Context pre-flight (auto-detect, ONE question max)

Before deciding Path A vs B, silently check for context:
1. `Read .claude/design-tokens.json` if exists
2. `Bash(ls ~/.claude/design-systems/ 2>/dev/null)` — brand folder match
3. `Glob` codebase tokens
4. Scan brief for github / Figma / image / PRD attachment → dispatch ingestion skills

If nothing — ONE `AskUserQuestion`: design system / codebase / screenshot / Figma / none / decide. Report "Using <context>. Proceeding."

## Path A — Standalone HTML with Stage/Sprite

For any animation that can live in one HTML file (explainer reel, product intro, transition sequences, hero animations — <60s typical).

Uses the Remotion-compatible in-browser engine in `starters/animations.jsx`. Same mental model as Remotion — different runtime (no build step, runs under Babel standalone).

**Available primitives:**

| Primitive | Role |
|---|---|
| `<Stage duration width height [id] [loop] [showControls]>` | Root composition. Owns one RAF clock, scale-to-fit canvas, scrubber UI, play/pause. Reads/writes position in localStorage. |
| `<Sprite start end [easing]>` | Active only in `[start..end]`ms window. Children can be element or `(localT) => element`. Unmounts when out of range. |
| `useTime({ stopAt? })` | Returns current ms. Inside Stage: reads shared clock (free). Standalone: spawns its own RAF (costlier). |
| `useSprite()` | Returns local t ∈ [0,1] within the current Sprite. |
| `Easing` | `linear`, `inQuad`, `outQuad`, `inOutCubic`, `outQuart`, `inOutExpo`, `spring(stiffness, damping)` |
| `interpolate(t, [in], [out], { clamp?, easing? })` | Piecewise lerp. Supports numbers and hex colors. |
| `<FadeIn>`, `<FadeOut>`, `<SlideIn from=...>`, `<ScaleIn from=...>`, `<Reveal from=...>` | Entry/exit sugar. **Persist after their animation window** (unlike Sprite). |
| `<Transition from to duration>` | Standalone one-shot wrapper (no Stage needed). |

**Steps:**

1. Invoke `Skill: frontend-design` for aesthetic direction
2. Create `artifacts/<slug>.html` with React + Babel + `animations.jsx`
3. `Bash(cp starters/animations.jsx "$(dirname <html>)/")` — copy starter next to the HTML
4. Run `/serve` (required for external `.jsx` CORS)
5. Compose the scene. Pattern:

```jsx
function Scene() {
  const t = useTime();  // Stage-shared clock
  // drive properties via interpolate()
  const bg = interpolate(t, [0, 2000, 5000], ['#fef9f3', '#f3d8a8', '#8a5a22'], { easing: Easing.inOutCubic });
  return (
    <div style={{ position: 'absolute', inset: 0, background: bg }}>
      <FadeIn start={0} duration={500}>
        <h1>Entry stays visible after 500ms</h1>
      </FadeIn>
      <Reveal start={400} duration={700} from="bottom" distance={40}>
        <p>Fade + slide combo</p>
      </Reveal>
      <Sprite start={1500} end={3500} easing={Easing.outQuart}>
        {(local) => <div style={{ opacity: local, transform: `scale(${local})` }}>Bounded — disappears after 3500</div>}
      </Sprite>
    </div>
  );
}

function App() {
  return <Stage duration={5000} width={1920} height={1080} loop={false}><Scene/></Stage>;
}
```

6. `/done http://127.0.0.1:4567/artifacts/<slug>.html` — verify scrubber works, animation plays cleanly, console clean
7. For exporting frames/seeking for PPTX: external tools can send `window.postMessage({ seekMs: N, playing: false }, '*')` — Stage listens and jumps

## Path B — Remotion (MP4 export, multi-scene video)

For long-form (>60s), multi-scene narrative, or MP4-export needs.

1. Delegate to `Skill: remotion-best-practices` — full Remotion workflow
2. Set up `artifacts/<slug>-remotion/` as a separate Remotion project
3. Return a preview HTML and MP4 artifact when done

## When to pick which

| Need | Path |
|---|---|
| Single scene, any length | A |
| Product intro, explainer under a minute | A |
| Multi-scene narrative | B |
| MP4 export required | B |
| Browser-only preview (ship an HTML) | A |
| Exact frame timing (e.g. 30fps video) | B (Remotion is frame-based) |
| Physics / gesture-driven | A with Popmotion `<script src>` fallback, or B |

## Popmotion fallback

For real spring physics, keyframe math, or gesture tracking beyond what `Easing.spring()` supports, add:
```html
<script src="https://unpkg.com/popmotion@11.0.5/dist/popmotion.min.js"></script>
```
and use `window.popmotion` directly.

## Verify

Path A: `/done <url>` — scrubber reaches end, clicking bar seeks, play/pause toggles, console clean. If the user wants PPTX frames of this animation: seek via postMessage before each screenshot.

Path B: Remotion preview server at `localhost:3000` + exported MP4.
