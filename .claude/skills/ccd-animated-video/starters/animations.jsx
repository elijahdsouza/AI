// Remotion-compatible in-browser animation engine.
// Timeline-based composition for motion-design HTML artifacts.
//
// Exports to window:
//   <Stage duration width height [id] [loop] [showControls] [fullscreen]>
//   <Sprite start end [easing]>
//   useTime({ stopAt? })      — global ms since mount (Stage-aware)
//   useSprite()               — local t ∈ [0,1] within current Sprite
//   Easing                    — linear, inOutCubic, outQuart, inOutExpo, spring()
//   interpolate(t, [in], [out], { clamp?, easing? })
//   <Transition from to duration easing>   — single-shot wrap, backward-compat
//   <FadeIn start duration [easing]>       — entry primitive
//   <FadeOut start duration [easing]>      — exit primitive
//   <SlideIn from start duration [distance] [easing]>   (from: 'top'|'bottom'|'left'|'right')
//   <ScaleIn start duration [from] [easing]>            — scale from `from` to 1
//   <Reveal start duration [from] [distance] [easing]>  — Slide + Fade combo
//
// Popmotion fallback: for spring physics, gestures, or keyframe math that this
// engine can't express, add
//   <script src="https://unpkg.com/popmotion@11.0.5/dist/popmotion.min.js"></script>
// and use window.popmotion directly.

(() => {
  const { useState, useEffect, useRef, useContext, createContext, isValidElement, cloneElement, createElement, Fragment } = React;

  // ---------- Easing ----------
  const Easing = {
    linear: (t) => t,
    inQuad: (t) => t * t,
    outQuad: (t) => 1 - (1 - t) * (1 - t),
    inOutCubic: (t) => t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2,
    outQuart: (t) => 1 - Math.pow(1 - t, 4),
    inOutExpo: (t) => t === 0 ? 0 : t === 1 ? 1 : t < 0.5
      ? Math.pow(2, 20 * t - 10) / 2
      : (2 - Math.pow(2, -20 * t + 10)) / 2,
    // Simple underdamped spring approximation. Not a physical integrator.
    // For real spring physics, use Popmotion.
    spring: (stiffness = 100, damping = 10) => (t) => {
      const d = damping / 20;
      const w = Math.sqrt(Math.max(stiffness / 10 - d * d, 0.01));
      const tScaled = t * 3;
      return 1 - Math.exp(-d * tScaled * 6) * (Math.cos(w * tScaled) + (d / w) * Math.sin(w * tScaled));
    },
  };

  // ---------- interpolate ----------
  function interpolate(t, inStops, outStops, options = {}) {
    const { clamp = true, easing = Easing.linear } = options;
    if (!Array.isArray(inStops) || !Array.isArray(outStops)) throw new Error('interpolate: stops must be arrays');
    if (inStops.length !== outStops.length) throw new Error('interpolate: stops length mismatch');
    if (inStops.length < 2) throw new Error('interpolate: need ≥2 stops');

    if (clamp) {
      if (t <= inStops[0]) return outStops[0];
      if (t >= inStops[inStops.length - 1]) return outStops[outStops.length - 1];
    }

    for (let i = 0; i < inStops.length - 1; i++) {
      const a = inStops[i], b = inStops[i + 1];
      if (t >= a && t <= b) {
        const localT = (t - a) / (b - a);
        const eased = easing(localT);
        const oa = outStops[i], ob = outStops[i + 1];
        if (typeof oa === 'number' && typeof ob === 'number') return oa + (ob - oa) * eased;
        if (typeof oa === 'string' && oa.startsWith('#')) return lerpHex(oa, ob, eased);
        return eased < 0.5 ? oa : ob;
      }
    }
    return outStops[outStops.length - 1];
  }

  function hexToRgb(hex) {
    const h = hex.replace('#', '');
    const s = h.length === 3 ? h.split('').map((c) => c + c).join('') : h;
    return { r: parseInt(s.slice(0, 2), 16), g: parseInt(s.slice(2, 4), 16), b: parseInt(s.slice(4, 6), 16) };
  }
  function lerpHex(a, b, t) {
    const pa = hexToRgb(a), pb = hexToRgb(b);
    const r = Math.round(pa.r + (pb.r - pa.r) * t);
    const g = Math.round(pa.g + (pb.g - pa.g) * t);
    const bl = Math.round(pa.b + (pb.b - pa.b) * t);
    return `#${[r, g, bl].map((v) => v.toString(16).padStart(2, '0')).join('')}`;
  }

  // ---------- Context ----------
  const StageContext = createContext(null);
  const SpriteContext = createContext(null);

  // ---------- useTime ----------
  // Inside <Stage>: returns stage.t (shared clock, no extra RAF).
  // Standalone: runs its own RAF loop. Optional { stopAt } halts the loop.
  function useTime({ stopAt = Infinity } = {}) {
    const stage = useContext(StageContext);
    const [t, setT] = useState(0);
    const startRef = useRef(null);

    useEffect(() => {
      if (stage) return; // Stage owns the clock
      let raf;
      const loop = (now) => {
        if (startRef.current == null) startRef.current = now;
        const elapsed = now - startRef.current;
        setT(elapsed);
        if (elapsed >= stopAt) return;
        raf = requestAnimationFrame(loop);
      };
      raf = requestAnimationFrame(loop);
      return () => cancelAnimationFrame(raf);
    }, [stopAt, !!stage]);

    return stage ? stage.t : t;
  }

  // ---------- useSprite ----------
  function useSprite() {
    const sprite = useContext(SpriteContext);
    if (!sprite) {
      console.warn('useSprite() must be used inside <Sprite>');
      return 0;
    }
    return sprite.localT;
  }

  // ---------- Stage ----------
  // Root of a timeline composition. Owns one RAF clock, exposes { t, duration, playing }
  // via context, renders children inside a fixed-aspect canvas (scale-to-fit).
  // Shows a scrubber + play/pause + time readout at the bottom.
  //
  // props:
  //   duration: number (ms)
  //   width, height: number (design canvas size, e.g. 1920x1080)
  //   id?: string — distinguishes multiple stages for localStorage key
  //   loop?: boolean — restart at 0 on reach end (default false)
  //   showControls?: boolean — scrubber visible (default true)
  //   fullscreen?: boolean — position:fixed, inset:0 (default true)
  function Stage({
    duration, width, height,
    id, loop = false, showControls = true, fullscreen = true,
    background = '#ffffff',
    children,
  }) {
    const [t, setT] = useState(0);
    const [playing, setPlaying] = useState(true);
    const storageKey = `__stage_t_${id || (typeof location !== 'undefined' ? location.pathname : 'default')}`;

    // Restore from localStorage
    useEffect(() => {
      try {
        const v = parseFloat(localStorage.getItem(storageKey));
        if (!Number.isNaN(v)) setT(Math.min(v, duration));
      } catch {}
    }, []);

    // RAF loop (owned here)
    useEffect(() => {
      if (!playing) return;
      let raf, lastNow = null;
      const loopFn = (now) => {
        if (lastNow == null) lastNow = now;
        const delta = now - lastNow;
        lastNow = now;
        setT((prev) => {
          let next = prev + delta;
          if (next >= duration) {
            if (loop) next = next % duration;
            else { setPlaying(false); return duration; }
          }
          return next;
        });
        raf = requestAnimationFrame(loopFn);
      };
      raf = requestAnimationFrame(loopFn);
      return () => cancelAnimationFrame(raf);
    }, [playing, duration, loop]);

    // Persist (throttled)
    useEffect(() => {
      const h = setTimeout(() => {
        try { localStorage.setItem(storageKey, String(t)); } catch {}
      }, 100);
      return () => clearTimeout(h);
    }, [t, storageKey]);

    // postMessage seek protocol — lets external tools (export scripts, Stage-host iframes) seek
    //   window.postMessage({ seekMs: 1500 }, '*')
    //   window.postMessage({ playing: false }, '*')
    useEffect(() => {
      const onMsg = (e) => {
        if (!e.data || typeof e.data !== 'object') return;
        if (typeof e.data.seekMs === 'number') {
          setT(Math.max(0, Math.min(duration, e.data.seekMs)));
        }
        if (typeof e.data.playing === 'boolean') setPlaying(e.data.playing);
      };
      window.addEventListener('message', onMsg);
      return () => window.removeEventListener('message', onMsg);
    }, [duration]);

    // Auto-scale to viewport (letterbox)
    const [scale, setScale] = useState(1);
    const [pos, setPos] = useState({ x: 0, y: 0 });
    useEffect(() => {
      if (!fullscreen) return;
      const compute = () => {
        const s = Math.min(window.innerWidth / width, window.innerHeight / height);
        setScale(s);
        setPos({ x: (window.innerWidth - width * s) / 2, y: (window.innerHeight - height * s) / 2 });
      };
      compute();
      window.addEventListener('resize', compute);
      return () => window.removeEventListener('resize', compute);
    }, [width, height, fullscreen]);

    const ctx = { t, duration, playing, setT, setPlaying, stageWidth: width, stageHeight: height };

    const shellStyle = fullscreen
      ? { position: 'fixed', inset: 0, background: '#000', overflow: 'hidden', zIndex: 0 }
      : { position: 'relative', width: '100%', height: '100%', background: '#000', overflow: 'hidden' };

    const canvasStyle = fullscreen
      ? {
          position: 'absolute',
          left: pos.x, top: pos.y,
          width, height, background,
          transform: `scale(${scale})`, transformOrigin: '0 0',
        }
      : { width, height, background, margin: '0 auto' };

    return createElement(StageContext.Provider, { value: ctx },
      createElement('div', { style: shellStyle, 'data-stage': '' },
        createElement('div', { style: canvasStyle, 'data-stage-canvas': '' }, children),
        showControls && createElement(Scrubber, { ctx })
      )
    );
  }

  // ---------- Scrubber ----------
  function Scrubber({ ctx }) {
    const pct = ctx.duration > 0 ? (ctx.t / ctx.duration) * 100 : 0;
    const fmt = (ms) => {
      const s = ms / 1000;
      return `${Math.floor(s / 60)}:${String(Math.floor(s % 60)).padStart(2, '0')}.${String(Math.floor((ms % 1000) / 10)).padStart(2, '0')}`;
    };
    const scrubberStyles = {
      shell: {
        position: 'fixed', bottom: 0, left: 0, right: 0, height: 48,
        background: 'rgba(0,0,0,0.75)', backdropFilter: 'blur(8px)', WebkitBackdropFilter: 'blur(8px)',
        display: 'flex', alignItems: 'center', gap: 12, padding: '0 16px',
        color: '#fff', font: '12px ui-monospace, Menlo, Consolas, monospace',
        zIndex: 9999, userSelect: 'none',
      },
      btn: {
        width: 32, height: 32, borderRadius: '50%',
        background: '#fff', color: '#000', border: 'none', cursor: 'pointer',
        fontSize: 14, display: 'flex', alignItems: 'center', justifyContent: 'center',
        padding: 0, flexShrink: 0,
      },
      time: { opacity: 0.8, minWidth: 70, textAlign: 'center', flexShrink: 0 },
      bar: {
        flex: 1, height: 6, background: 'rgba(255,255,255,0.18)',
        borderRadius: 3, cursor: 'pointer', position: 'relative',
      },
      fill: (p) => ({
        position: 'absolute', left: 0, top: 0, bottom: 0,
        width: `${p}%`, background: '#fff', borderRadius: 3, pointerEvents: 'none',
      }),
    };
    const onBarClick = (e) => {
      const rect = e.currentTarget.getBoundingClientRect();
      const pctX = Math.max(0, Math.min(1, (e.clientX - rect.left) / rect.width));
      ctx.setT(pctX * ctx.duration);
    };
    return createElement('div', { style: scrubberStyles.shell, 'data-stage-controls': '' },
      createElement('button', {
        style: scrubberStyles.btn,
        onClick: () => ctx.setPlaying(!ctx.playing),
        title: ctx.playing ? 'Pause' : 'Play',
      }, ctx.playing ? '⏸' : '▶'),
      createElement('span', { style: scrubberStyles.time }, fmt(ctx.t)),
      createElement('div', { style: scrubberStyles.bar, onClick: onBarClick },
        createElement('div', { style: scrubberStyles.fill(pct) })
      ),
      createElement('span', { style: scrubberStyles.time }, fmt(ctx.duration))
    );
  }

  // ---------- Sprite ----------
  // Active between [start..end]ms of the enclosing Stage. Renders nothing when out of range.
  // Children can be:
  //   - React element(s): rendered as-is while in range
  //   - Function: (localT ∈ [0..1]) => element
  function Sprite({ start = 0, end, easing = Easing.linear, children }) {
    const stage = useContext(StageContext);
    if (!stage) {
      console.warn('<Sprite> must be used inside <Stage>');
      return null;
    }
    const endMs = end == null ? stage.duration : end;
    if (stage.t < start || stage.t > endMs) return null;

    const span = endMs - start;
    const localT = span > 0 ? easing(Math.max(0, Math.min(1, (stage.t - start) / span))) : 1;
    const spriteCtx = { start, end: endMs, localT };

    const rendered = typeof children === 'function' ? children(localT) : children;

    return createElement(SpriteContext.Provider, { value: spriteCtx }, rendered);
  }

  // ---------- Transition (backward compat) ----------
  // Standalone one-shot wrapper — no Stage required.
  function Transition({ from = {}, to = {}, duration = 400, easing = Easing.inOutCubic, children, onDone }) {
    const t = useTime({ stopAt: duration });
    const progress = Math.min(t / duration, 1);
    const eased = easing(progress);
    const doneRef = useRef(false);

    useEffect(() => {
      if (progress >= 1 && !doneRef.current) {
        doneRef.current = true;
        onDone?.();
      }
    }, [progress, onDone]);

    const style = mergeStyles(from, to, eased);
    if (!isValidElement(children)) return children;
    return cloneElement(children, { style: { ...(children.props.style || {}), ...style } });
  }

  function mergeStyles(from, to, eased) {
    const out = {};
    for (const key of new Set([...Object.keys(from), ...Object.keys(to)])) {
      const fv = from[key], tv = to[key];
      if (typeof fv === 'number' && typeof tv === 'number') out[key] = fv + (tv - fv) * eased;
      else if (typeof fv === 'string' && fv.startsWith('#')) out[key] = lerpHex(fv, tv, eased);
      else out[key] = eased >= 1 ? tv : fv;
    }
    return out;
  }

  // ---------- Entry / exit primitives ----------
  // Entry primitives (FadeIn, SlideIn, ScaleIn, Reveal):
  //   before start     → hidden
  //   start..start+dur → animate from initial to final
  //   after start+dur  → stay at final (persists, unlike Sprite)
  // Exit primitives (FadeOut):
  //   before start     → visible at initial (1.0)
  //   start..start+dur → animate to 0
  //   after start+dur  → hidden
  // These read Stage context directly (not Sprite-wrapped) so they persist
  // after their animation window. For bounded range renders use <Sprite> directly.

  function useEntryProgress(start, duration, easing) {
    const stage = useContext(StageContext);
    if (!stage) {
      console.warn('Entry primitives must be inside <Stage>');
      return { visible: false, t: 0 };
    }
    if (stage.t < start) return { visible: false, t: 0 };
    const raw = duration > 0 ? Math.min(1, (stage.t - start) / duration) : 1;
    return { visible: true, t: easing(raw) };
  }

  function FadeIn({ start = 0, duration = 400, easing = Easing.outQuart, children }) {
    const { visible, t } = useEntryProgress(start, duration, easing);
    if (!visible) return null;
    return wrapStyle(children, { opacity: t });
  }

  function FadeOut({ start = 0, duration = 400, easing = Easing.inOutCubic, children }) {
    const stage = useContext(StageContext);
    if (!stage) return children;
    if (stage.t < start) return children;
    if (stage.t >= start + duration) return null;
    const raw = (stage.t - start) / duration;
    return wrapStyle(children, { opacity: 1 - easing(raw) });
  }

  function SlideIn({ from = 'bottom', start = 0, duration = 500, distance = 80, easing = Easing.outQuart, children }) {
    const { visible, t } = useEntryProgress(start, duration, easing);
    if (!visible) return null;
    const axis = from === 'left' || from === 'right' ? 'X' : 'Y';
    const sign = from === 'right' || from === 'bottom' ? 1 : -1;
    const offset = sign * distance * (1 - t);
    return wrapStyle(children, { transform: `translate${axis}(${offset}px)` });
  }

  function ScaleIn({ start = 0, duration = 500, from = 0.9, easing = Easing.outQuart, children }) {
    const { visible, t } = useEntryProgress(start, duration, easing);
    if (!visible) return null;
    const s = from + (1 - from) * t;
    return wrapStyle(children, { transform: `scale(${s})` });
  }

  function Reveal({ start = 0, duration = 600, from = 'bottom', distance = 40, easing = Easing.outQuart, children }) {
    // Slide + fade combo — most common entry pattern
    const { visible, t } = useEntryProgress(start, duration, easing);
    if (!visible) return null;
    const axis = from === 'left' || from === 'right' ? 'X' : 'Y';
    const sign = from === 'right' || from === 'bottom' ? 1 : -1;
    const offset = sign * distance * (1 - t);
    return wrapStyle(children, {
      opacity: t,
      transform: `translate${axis}(${offset}px)`,
    });
  }

  function wrapStyle(children, add) {
    if (!isValidElement(children)) return children;
    return cloneElement(children, {
      style: { ...(children.props.style || {}), ...add },
    });
  }

  Object.assign(window, {
    // Primitives
    Stage, Sprite,
    // Hooks
    useTime, useSprite,
    // Math
    Easing, interpolate,
    // Legacy single-shot wrapper
    Transition,
    // Entry / exit primitives
    FadeIn, FadeOut, SlideIn, ScaleIn, Reveal,
  });
})();
