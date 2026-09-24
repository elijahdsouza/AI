import { useEffect, useRef } from "react";
import lottie from "lottie-web/build/player/lottie_light";
import magnet from "../assets/uc-magnet.json";
import { isAmbientPaused, subscribeAmbient } from "./effects";
import { LOTTIE, POLES, markBounds, makeTf, type Pt } from "./ucMark";

// The two pole tips in the Lottie's own 512 x 512 space.
const POLE_COMP: Pt[] = POLES.map(makeTf(markBounds().centre, LOTTIE.centre, LOTTIE.scale));

/**
 * The hero graphic: the UC magnet as a Lottie (it draws itself on, then its field
 * flows pole to pole), over a field of dots pulled toward the two poles. Nearby
 * dots link into a loose lattice. The magnet leans toward the cursor and its field
 * runs faster as the cursor nears a pole; the cursor also tugs the dots.
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
    let introDone = false;
    anim.addEventListener("complete", () => {
      if (introDone) return;
      introDone = true;
      anim.loop = true;
      anim.playSegments([60, 180], true);
    });

    let w = 0, h = 0, dpr = 1, raf = 0, running = false, t = 0;
    let boxX = 0, boxY = 0, boxS = 0, angle = 0, speed = 1;
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
      q.size = 0.8 + Math.random() * 1.5;
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
      const n = Math.round(Math.min(170, Math.max(64, (w * h) / 5600)));
      parts = Array.from({ length: n }, () => spawn());
      parts.forEach((p) => { p.life = Math.random() * 400; });
    };

    const step = (dt: number) => {
      // the magnet leans toward the cursor; with no cursor it sways a little
      const target = pointer.active
        ? Math.max(-1, Math.min(1, (pointer.x - w / 2) / (w / 2))) * 9
        : Math.sin(t * 0.0009) * 2.2;
      angle += (target - angle) * Math.min(1, dt * 0.006);
      box.style.transform = `rotate(${angle.toFixed(2)}deg)`;

      const pl = poles();
      // the field runs faster as the cursor nears a pole
      let near = 0;
      if (pointer.active) {
        const dmin = Math.min(...pl.map(([x, y]) => Math.hypot(pointer.x - x, pointer.y - y)));
        near = Math.max(0, 1 - dmin / (boxS * 0.55));
      }
      const want = (reduce ? 0.6 : 1) * (0.75 + near * 1.9);
      if (Math.abs(want - speed) > 0.02) { speed += (want - speed) * 0.2; anim.setSpeed(speed); }

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
            ctx.strokeStyle = `rgba(243,239,230,${(1 - d2 / l2) * 0.16})`;
            ctx.beginPath(); ctx.moveTo(p.x, p.y); ctx.lineTo(q.x, q.y); ctx.stroke();
          }
        }
      }
      for (const p of parts) {
        const sp = Math.min(1, Math.hypot(p.vx, p.vy) / 2.2);
        const fade = Math.min(1, p.life / 900);
        ctx.fillStyle = p.hold > 0 ? "rgba(187,171,105,1)" : `rgba(${sp > 0.45 ? "187,171,105" : "243,239,230"},${(0.35 + sp * 0.6) * fade})`;
        ctx.beginPath(); ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2); ctx.fill();
      }
    };

    let last = 0;
    const frame = (now: number) => {
      const dt = Math.min(48, last ? now - last : 16);
      last = now; t = now;
      step(dt); draw();
      if (running) raf = requestAnimationFrame(frame);
    };
    let visible = false, started = false;
    const start = () => {
      if (running || !visible || document.hidden || isAmbientPaused()) return;
      running = true; last = 0; raf = requestAnimationFrame(frame);
      if (!started) { started = true; anim.playSegments([0, 60], true); } else anim.play();
    };
    const stop = () => { running = false; cancelAnimationFrame(raf); anim.pause(); };

    resize();
    for (let i = 0; i < 120; i++) step(16);
    draw();

    const io = new IntersectionObserver(([e]) => { visible = e.isIntersecting; if (visible) start(); else stop(); }, { threshold: 0.01 });
    io.observe(host);
    const unsubscribe = subscribeAmbient(() => (isAmbientPaused() ? stop() : start()));
    const ro = new ResizeObserver(() => { resize(); draw(); });
    ro.observe(host);
    const onVis = () => (document.hidden ? stop() : start());
    document.addEventListener("visibilitychange", onVis);
    const onMove = (e: PointerEvent) => {
      const r = host.getBoundingClientRect();
      pointer.x = e.clientX - r.left; pointer.y = e.clientY - r.top; pointer.active = true;
    };
    const onLeave = () => { pointer.active = false; };
    host.addEventListener("pointermove", onMove);
    host.addEventListener("pointerleave", onLeave);

    return () => {
      stop(); io.disconnect(); ro.disconnect(); unsubscribe(); anim.destroy();
      document.removeEventListener("visibilitychange", onVis);
      host.removeEventListener("pointermove", onMove);
      host.removeEventListener("pointerleave", onLeave);
    };
  }, []);

  return (
    <div ref={hostRef} className={className} aria-hidden="true">
      <canvas ref={canvasRef} className="absolute inset-0 w-full h-full" />
      <div ref={boxRef} className="absolute will-change-transform" />
    </div>
  );
}
