import { useEffect, useRef } from "react";
import { isAmbientPaused, subscribeAmbient } from "./effects";

/**
 * The hero graphic: a U-shaped magnet drawn from the logo's form, pulling a
 * field of dots toward its two poles. Nearby dots link into a loose lattice,
 * and the cursor acts as a second, weaker magnet. Pauses off-screen and with
 * the page's pause control; renders one settled still frame under reduced motion.
 */
export default function MagneticU({ className = "" }: { className?: string }) {
  const ref = useRef<HTMLCanvasElement>(null);

  useEffect(() => {
    const canvas = ref.current!;
    const ctx = canvas.getContext("2d")!;
    const reduce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    let w = 0, h = 0, dpr = 1, raf = 0, running = false, t = 0;
    const pointer = { x: -9999, y: -9999, active: false };

    type P = { x: number; y: number; vx: number; vy: number; life: number; size: number; hold: number };
    let parts: P[] = [];
    let geo = { cx: 0, cy: 0, s: 0, sep: 0, armH: 0, thick: 0 };

    const poles = () => {
      const bob = reduce ? 0 : Math.sin(t * 0.0012) * geo.s * 0.02;
      const top = geo.cy - geo.armH * 0.55 + bob;
      return [
        { x: geo.cx - geo.sep / 2, y: top },
        { x: geo.cx + geo.sep / 2, y: top },
      ];
    };

    const spawn = (p?: P): P => {
      const a = Math.random() * Math.PI * 2;
      const r = Math.max(w, h) * (0.35 + Math.random() * 0.45);
      const q = p ?? ({} as P);
      q.x = geo.cx + Math.cos(a) * r;
      q.y = geo.cy + Math.sin(a) * r * 0.8;
      q.vx = (Math.random() - 0.5) * 0.3;
      q.vy = (Math.random() - 0.5) * 0.3;
      q.life = 0;
      q.hold = 0;
      q.size = 0.8 + Math.random() * 1.6;
      return q;
    };

    const resize = () => {
      const rect = canvas.getBoundingClientRect();
      dpr = Math.min(window.devicePixelRatio || 1, 2);
      w = rect.width; h = rect.height;
      canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr);
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      const s = Math.min(w, h) * (w < 700 ? 0.42 : 0.36);
      geo = { cx: w * 0.5, cy: h * 0.54, s, sep: s * 0.86, armH: s * 0.95, thick: s * 0.26 };
      const n = Math.round(Math.min(190, Math.max(70, (w * h) / 5200)));
      parts = Array.from({ length: n }, () => spawn());
      parts.forEach((p) => { p.life = Math.random() * 400; });
    };

    const step = (dt: number) => {
      const [a, b] = poles();
      for (const p of parts) {
        if (p.hold > 0) { p.hold -= dt; if (p.hold <= 0) spawn(p); continue; }
        let fx = 0, fy = 0;
        for (const pole of [a, b]) {
          const dx = pole.x - p.x, dy = pole.y - p.y;
          const d2 = dx * dx + dy * dy + 900;
          const d = Math.sqrt(d2);
          const f = Math.min(0.09, 260 / d2);
          fx += (dx / d) * f; fy += (dy / d) * f;
          // tangential swirl, so the dots travel along curved field lines
          fx += (-dy / d) * f * 0.35; fy += (dx / d) * f * 0.35;
          if (d < geo.thick * 0.45) { p.hold = 400 + Math.random() * 900; p.x = pole.x + (Math.random() - 0.5) * geo.thick * 0.5; p.y = pole.y + (Math.random() - 0.5) * 8; }
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

    const drawMagnet = () => {
      const { cx, cy, sep, armH, thick } = geo;
      const bob = reduce ? 0 : Math.sin(t * 0.0012) * geo.s * 0.02;
      const r = sep / 2;
      const top = cy - armH * 0.55 + bob;
      const bottom = cy + armH * 0.45 + bob - r;
      ctx.save();
      ctx.lineCap = "round";
      // soft glow under the U
      const g = ctx.createRadialGradient(cx, bottom, 0, cx, bottom, geo.s * 1.4);
      g.addColorStop(0, "rgba(187,171,105,0.18)");
      g.addColorStop(1, "rgba(187,171,105,0)");
      ctx.fillStyle = g;
      ctx.fillRect(0, 0, w, h);
      // body: a thick U traced as a single stroke
      const path = () => {
        ctx.beginPath();
        ctx.moveTo(cx - r, top);
        ctx.lineTo(cx - r, bottom);
        ctx.arc(cx, bottom, r, Math.PI, 0, true);
        ctx.lineTo(cx + r, top);
      };
      ctx.lineWidth = thick; ctx.strokeStyle = "rgba(243,239,230,0.10)"; path(); ctx.stroke();
      ctx.lineWidth = thick - 3; ctx.strokeStyle = "#171510"; path(); ctx.stroke();
      ctx.lineWidth = 1.2; ctx.strokeStyle = "rgba(243,239,230,0.55)";
      // outer and inner outline, like the logo's double line
      ctx.beginPath(); ctx.moveTo(cx - r - thick / 2, top); ctx.lineTo(cx - r - thick / 2, bottom);
      ctx.arc(cx, bottom, r + thick / 2, Math.PI, 0, true); ctx.lineTo(cx + r + thick / 2, top); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(cx - r + thick / 2, top); ctx.lineTo(cx - r + thick / 2, bottom);
      ctx.arc(cx, bottom, r - thick / 2, Math.PI, 0, true); ctx.lineTo(cx + r - thick / 2, top); ctx.stroke();
      // gold pole caps
      for (const x of [cx - r, cx + r]) {
        ctx.fillStyle = "#bbab69";
        ctx.beginPath();
        ctx.roundRect(x - thick / 2, top - thick * 0.05, thick, thick * 0.42, [thick * 0.12]);
        ctx.fill();
      }
      ctx.restore();
    };

    const draw = () => {
      ctx.clearRect(0, 0, w, h);
      // faint field arcs between the poles
      const [a, b] = poles();
      ctx.save();
      ctx.setLineDash([2, 7]);
      ctx.lineWidth = 1;
      for (let k = 1; k <= 5; k++) {
        ctx.strokeStyle = `rgba(187,171,105,${0.3 - k * 0.04})`;
        ctx.beginPath();
        ctx.moveTo(a.x, a.y);
        ctx.bezierCurveTo(a.x - k * geo.s * 0.25, a.y - k * geo.s * 0.32, b.x + k * geo.s * 0.25, b.y - k * geo.s * 0.32, b.x, b.y);
        ctx.stroke();
      }
      ctx.restore();

      // lattice links
      const link = w < 700 ? 58 : 72;
      const l2 = link * link;
      ctx.lineWidth = 0.7;
      for (let i = 0; i < parts.length; i++) {
        const p = parts[i];
        for (let j = i + 1; j < parts.length; j++) {
          const q = parts[j];
          const dx = p.x - q.x, dy = p.y - q.y;
          const d2 = dx * dx + dy * dy;
          if (d2 < l2) {
            ctx.strokeStyle = `rgba(243,239,230,${(1 - d2 / l2) * 0.16})`;
            ctx.beginPath(); ctx.moveTo(p.x, p.y); ctx.lineTo(q.x, q.y); ctx.stroke();
          }
        }
      }
      drawMagnet();
      // dots
      for (const p of parts) {
        const speed = Math.min(1, Math.hypot(p.vx, p.vy) / 2.2);
        const fade = Math.min(1, p.life / 900);
        ctx.fillStyle = p.hold > 0 ? "rgba(187,171,105,1)" : `rgba(${speed > 0.45 ? "187,171,105" : "243,239,230"},${(0.35 + speed * 0.6) * fade})`;
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
    let visible = false;
    const start = () => { if (running || reduce || !visible || isAmbientPaused()) return; running = true; last = 0; raf = requestAnimationFrame(frame); };
    const stop = () => { running = false; cancelAnimationFrame(raf); };

    resize();
    if (reduce) { for (let i = 0; i < 260; i++) step(16); draw(); }

    const io = new IntersectionObserver(([e]) => { visible = e.isIntersecting; if (visible) start(); else stop(); }, { threshold: 0.01 });
    const unsubscribe = subscribeAmbient(() => (isAmbientPaused() ? stop() : start()));
    io.observe(canvas);
    const ro = new ResizeObserver(() => { resize(); if (reduce) { for (let i = 0; i < 260; i++) step(16); draw(); } });
    ro.observe(canvas);
    const onVis = () => (document.hidden ? stop() : start());
    document.addEventListener("visibilitychange", onVis);
    const host = canvas.parentElement!;
    const onMove = (e: PointerEvent) => {
      const r = canvas.getBoundingClientRect();
      pointer.x = e.clientX - r.left; pointer.y = e.clientY - r.top; pointer.active = true;
    };
    const onLeave = () => { pointer.active = false; };
    host.addEventListener("pointermove", onMove);
    host.addEventListener("pointerleave", onLeave);

    return () => {
      stop(); io.disconnect(); ro.disconnect(); unsubscribe();
      document.removeEventListener("visibilitychange", onVis);
      host.removeEventListener("pointermove", onMove);
      host.removeEventListener("pointerleave", onLeave);
    };
  }, []);

  return <canvas ref={ref} className={className} aria-hidden="true" />;
}
