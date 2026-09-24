import { useEffect, useRef } from "react";
import lottie from "lottie-web/build/player/lottie_light";
import magnet from "../assets/uc-magnet.json";
import { isAmbientPaused, subscribeAmbient } from "./effects";
import { LOTTIE, POLES, markBounds, makeTf, type Pt } from "./ucMark";

// The two pole tips in the Lottie's own 512 x 512 space.
const POLE_COMP: Pt[] = POLES.map(makeTf(markBounds().centre, LOTTIE.centre, LOTTIE.scale));

// Frames in uc-magnet.json: the outline is half drawn at 24 and finished at 60;
// 60-180 is the field's seamless loop.
const HALF = 24, DONE = 60, LOOP = 120;

/**
 * The hero graphic: the UC magnet as a Lottie in gold line art, over a field of
 * dots pulled toward its two poles.
 *
 * It opens half drawn and settles into the finished mark, then its field flows
 * pole to pole. A mouse moving across it (or a finger dragging sideways) draws
 * the outline on and off between half drawn and finished; it leans toward the
 * pointer, its field runs faster near the poles, and a click or tap sends a
 * pulse through the field. Vertical swipes still scroll the page.
 * Stops off-screen and with the page's pause control.
 */
export default function HeroMagnet({ className = "" }: { className?: string }) {
  const hostRef = useRef<HTMLDivElement>(null);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const boxRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const host = hostRef.current!, canvas = canvasRef.current!, box = boxRef.current!;
    const ctx = canvas.getContext("2d")!;
    const reduce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

    const anim = lottie.loadAnimation({
      container: box, renderer: "svg", loop: false, autoplay: false, animationData: magnet,
      rendererSettings: { preserveAspectRatio: "xMidYMid meet" },
    });

    // playback is driven here, frame by frame, so pointer, pulse and loop share one clock
    type Mode = "intro" | "loop" | "scrub" | "settle";
    let mode: Mode = "intro", frame = HALF, introT = 0, loopPos = 0, boost = 0, lastMove = 0, quietUntil = 0;
    let shown = -1;
    const show = (f: number) => { if (Math.abs(f - shown) > 0.01) { anim.goToAndStop(f, true); shown = f; } };
    anim.addEventListener("DOMLoaded", () => { shown = -1; show(frame); });
    show(HALF);

    let w = 0, h = 0, dpr = 1, raf = 0, running = false, t = 0;
    let boxX = 0, boxY = 0, boxS = 0, angle = 0;
    const pointer = { x: -9999, y: -9999, active: false };

    type P = { x: number; y: number; vx: number; vy: number; life: number; size: number; hold: number };
    let parts: P[] = [];

    // pole tips on the canvas, turned with the magnet
    const poles = (): Pt[] => {
      const k = boxS / LOTTIE.size, cx = boxX + boxS / 2, cy = boxY + boxS / 2;
      const a = (angle * Math.PI) / 180, c = Math.cos(a), s = Math.sin(a);
      return POLE_COMP.map(([px, py]) => {
        const x = boxX + px * k - cx, y = boxY + py * k - cy;
        return [cx + x * c - y * s, cy + x * s + y * c];
      });
    };

    const spawn = (p?: P): P => {
      const a = Math.random() * Math.PI * 2;
      const r = Math.max(w, h) * (0.35 + Math.random() * 0.45);
      const q = p ?? ({} as P);
      q.x = w / 2 + Math.cos(a) * r;
      q.y = h / 2 + Math.sin(a) * r * 0.8;
      q.vx = (Math.random() - 0.5) * 0.3;
      q.vy = (Math.random() - 0.5) * 0.3;
      q.life = 0;
      q.hold = 0;
      q.size = 0.8 + Math.random() * 1.4;
      return q;
    };

    const resize = () => {
      const rect = host.getBoundingClientRect();
      dpr = Math.min(window.devicePixelRatio || 1, 2);
      w = rect.width; h = rect.height;
      canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr);
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      boxS = Math.min(w, h) * 1.1;
      boxX = (w - boxS) / 2; boxY = (h - boxS) / 2;
      box.style.width = box.style.height = `${boxS}px`;
      box.style.left = `${boxX}px`; box.style.top = `${boxY}px`;
      const n = Math.round(Math.min(140, Math.max(56, (w * h) / 6400)));
      parts = Array.from({ length: n }, () => spawn());
      parts.forEach((p) => { p.life = Math.random() * 400; });
    };

    const advance = (dt: number, now: number) => {
      const pl = poles();
      // the field runs faster as the pointer nears a pole, and after a tap
      let near = 0;
      if (pointer.active) {
        const dmin = Math.min(...pl.map(([x, y]) => Math.hypot(pointer.x - x, pointer.y - y)));
        near = Math.max(0, 1 - dmin / (boxS * 0.55));
      }
      boost = Math.max(0, boost - dt / 900);
      const speed = (reduce ? 0.6 : 1) * (0.75 + near * 1.9 + boost * 2.6);

      if (mode === "scrub" && (!pointer.active || now - lastMove > 1600)) mode = "settle";
      if (mode === "intro") {
        introT = Math.min(1, introT + dt / 1300);
        const e = 1 - Math.pow(1 - introT, 3);
        frame = HALF + (DONE - HALF) * e;
        if (introT >= 1) { mode = "loop"; loopPos = 0; }
      } else if (mode === "scrub") {
        // left edge of the graphic: half drawn; right edge: finished
        const u = Math.max(0, Math.min(1, (pointer.x - boxX) / boxS));
        const target = HALF + (DONE - HALF) * u;
        frame += (target - frame) * Math.min(1, dt * 0.012);
      } else if (mode === "settle") {
        frame += (DONE - frame) * Math.min(1, dt * 0.008);
        if (DONE - frame < 0.3) { mode = "loop"; loopPos = 0; }
      } else {
        loopPos = (loopPos + (dt / 1000) * 60 * speed) % LOOP;
        frame = DONE + loopPos;
      }
      show(frame);
    };

    const step = (dt: number, now: number) => {
      // the magnet leans toward the pointer; with no pointer it sways a little
      const target = pointer.active
        ? Math.max(-1, Math.min(1, (pointer.x - w / 2) / (w / 2))) * 9
        : Math.sin(t * 0.0009) * 2.2;
      angle += (target - angle) * Math.min(1, dt * 0.006);
      box.style.transform = `rotate(${angle.toFixed(2)}deg)`;
      advance(dt, now);

      const pl = poles();
      const grab = boxS * 0.035;
      for (const p of parts) {
        if (p.hold > 0) { p.hold -= dt; if (p.hold <= 0) spawn(p); continue; }
        let fx = 0, fy = 0;
        for (const [px, py] of pl) {
          const dx = px - p.x, dy = py - p.y;
          const d2 = dx * dx + dy * dy + 900;
          const d = Math.sqrt(d2);
          const f = Math.min(0.09, 260 / d2);
          fx += (dx / d) * f; fy += (dy / d) * f;
          // a tangential swirl, so the dots travel along curved field lines
          fx += (-dy / d) * f * 0.35; fy += (dx / d) * f * 0.35;
          if (d < grab) { p.hold = 400 + Math.random() * 900; p.x = px + (Math.random() - 0.5) * grab; p.y = py + (Math.random() - 0.5) * grab; }
        }
        if (pointer.active) {
          const dx = pointer.x - p.x, dy = pointer.y - p.y;
          const d2 = dx * dx + dy * dy + 400;
          if (d2 < 220 * 220) { const d = Math.sqrt(d2); const f = Math.min(0.12, 420 / d2); fx += (dx / d) * f; fy += (dy / d) * f; }
        }
        p.vx = (p.vx + fx * dt * 0.06) * 0.985;
        p.vy = (p.vy + fy * dt * 0.06) * 0.985;
        p.x += p.vx * dt * 0.06; p.y += p.vy * dt * 0.06;
        p.life += dt;
        if (p.life > 14000 || p.x < -80 || p.x > w + 80 || p.y < -80 || p.y > h + 80) spawn(p);
      }
    };

    const draw = () => {
      ctx.clearRect(0, 0, w, h);
      const link = w < 700 ? 58 : 72, l2 = link * link;
      ctx.lineWidth = 0.7;
      for (let i = 0; i < parts.length; i++) {
        const p = parts[i];
        for (let j = i + 1; j < parts.length; j++) {
          const q = parts[j];
          const dx = p.x - q.x, dy = p.y - q.y, d2 = dx * dx + dy * dy;
          if (d2 < l2) {
            ctx.strokeStyle = `rgba(243,239,230,${(1 - d2 / l2) * 0.13})`;
            ctx.beginPath(); ctx.moveTo(p.x, p.y); ctx.lineTo(q.x, q.y); ctx.stroke();
          }
        }
      }
      for (const p of parts) {
        const sp = Math.min(1, Math.hypot(p.vx, p.vy) / 2.2);
        const fade = Math.min(1, p.life / 900);
        ctx.fillStyle = p.hold > 0 ? "rgba(187,171,105,1)" : `rgba(${sp > 0.45 ? "187,171,105" : "243,239,230"},${(0.32 + sp * 0.6) * fade})`;
        ctx.beginPath(); ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2); ctx.fill();
      }
    };

    let last = 0;
    const tick = (now: number) => {
      const dt = Math.min(48, last ? now - last : 16);
      last = now; t = now;
      step(dt, now); draw();
      if (running) raf = requestAnimationFrame(tick);
    };
    let visible = false;
    const start = () => {
      if (running || !visible || document.hidden || isAmbientPaused()) return;
      running = true; last = 0; raf = requestAnimationFrame(tick);
    };
    const stop = () => { running = false; cancelAnimationFrame(raf); };

    resize();
    for (let i = 0; i < 120; i++) { const s: Mode = mode; step(16, 0); mode = s; }
    frame = HALF; introT = 0; show(HALF);
    draw();

    const io = new IntersectionObserver(([e]) => { visible = e.isIntersecting; if (visible) start(); else stop(); }, { threshold: 0.01 });
    io.observe(host);
    const unsubscribe = subscribeAmbient(() => (isAmbientPaused() ? stop() : start()));
    const ro = new ResizeObserver(() => { resize(); draw(); });
    ro.observe(host);
    const onVis = () => (document.hidden ? stop() : start());
    document.addEventListener("visibilitychange", onVis);

    const place = (e: PointerEvent) => {
      const r = host.getBoundingClientRect();
      pointer.x = e.clientX - r.left; pointer.y = e.clientY - r.top;
    };
    const onMove = (e: PointerEvent) => {
      // a finger only steers while it is down; a mouse steers on hover
      if (e.pointerType !== "mouse" && e.buttons === 0) return;
      place(e); pointer.active = true; lastMove = performance.now();
      if (mode !== "intro" && performance.now() > quietUntil) mode = "scrub";
    };
    const onDown = (e: PointerEvent) => {
      place(e); pointer.active = true; lastMove = performance.now();
      boost = 1; // a pulse through the field
      if (mode === "scrub") mode = "settle";
      quietUntil = performance.now() + 200; // a tap pulses; only a drag steers
      start();
    };
    const onEnd = (e: PointerEvent) => { if (e.type === "pointerleave" || e.pointerType !== "mouse") pointer.active = false; };
    host.addEventListener("pointermove", onMove);
    host.addEventListener("pointerdown", onDown);
    host.addEventListener("pointerup", onEnd);
    host.addEventListener("pointercancel", onEnd);
    host.addEventListener("pointerleave", onEnd);

    return () => {
      stop(); io.disconnect(); ro.disconnect(); unsubscribe(); anim.destroy();
      document.removeEventListener("visibilitychange", onVis);
      host.removeEventListener("pointermove", onMove);
      host.removeEventListener("pointerdown", onDown);
      host.removeEventListener("pointerup", onEnd);
      host.removeEventListener("pointercancel", onEnd);
      host.removeEventListener("pointerleave", onEnd);
    };
  }, []);

  return (
    <div ref={hostRef} className={`touch-pan-y select-none ${className}`} aria-hidden="true">
      <canvas ref={canvasRef} className="absolute inset-0 w-full h-full" />
      <div ref={boxRef} className="absolute will-change-transform" />
    </div>
  );
}
