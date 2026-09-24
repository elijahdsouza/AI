import {
  useEffect, useLayoutEffect, useRef, useState, useSyncExternalStore,
  type ReactNode, type RefObject,
} from "react";
import {
  motion, useScroll, useTransform, useInView, animate, useReducedMotion, AnimatePresence,
  useMotionValue, useSpring, cubicBezier, type MotionValue,
} from "motion/react";
import { Pause, Play } from "lucide-react";

/*
  Motion system, agreed across the skills used on this build
  (scroll-craft, design-motion-principles, emil-design-eng, motion-dev-animations):
  - one strong ease-out for anything arriving, one ease-in-out for things moving on screen
  - entrances: fade from 0, rise 14px, sharpen from a 4px blur, 620ms, staggered 60ms,
    once only, fired a little inside the viewport so the reader is looking
  - scroll-scrubbed motion is reserved for the immersive moments; everything else
    is triggered once and runs on its own clock
  - "reduce motion" softens rather than strips: the scroll-driven moments, the logo
    strips and the hero keep running (the visitor's own scroll drives most of them),
    while parallax drift, slide-in offsets and the pointer lean are dropped. Anything
    that moves on its own can be stopped with the pause control.
*/
export const EASE_OUT = [0.23, 1, 0.32, 1] as const;
export const EASE_IN_OUT = [0.77, 0, 0.175, 1] as const;
const easeOutFn = cubicBezier(...EASE_OUT);

const VIEW = { once: true, margin: "0px 0px -12% 0px" } as const;

/* ---------- scroll progress ---------- */

type Offset = NonNullable<Parameters<typeof useScroll>[0]>["offset"];

/**
 * Scroll progress through a section, kept on Motion's JavaScript path.
 * The identity transform opts out of the native ScrollTimeline acceleration:
 * that path builds keyframes only for the mapped range, so past the range the
 * browser eases back to the element's resting value (the peak's words crept
 * back and the room faded out in Chrome). Safari always takes the JS path, so
 * this also makes every browser behave the same.
 */
export function useSectionProgress(target: RefObject<HTMLElement | null>, offset: Offset) {
  const { scrollYProgress } = useScroll({ target: target as RefObject<HTMLElement>, offset });
  return useTransform(scrollYProgress, (v) => v);
}

/* ---------- ambient motion pause (WCAG 2.2.2: moving content can be paused) ---------- */

let ambientPaused = false;
const ambientListeners = new Set<() => void>();
export function setAmbientPaused(v: boolean) {
  ambientPaused = v;
  document.documentElement.dataset.ambient = v ? "paused" : "running";
  ambientListeners.forEach((l) => l());
}
export function useAmbientPaused() {
  return useSyncExternalStore(
    (l) => { ambientListeners.add(l); return () => ambientListeners.delete(l); },
    () => ambientPaused,
    () => false,
  );
}
export function isAmbientPaused() { return ambientPaused; }
export function subscribeAmbient(l: () => void) { ambientListeners.add(l); return () => { ambientListeners.delete(l); }; }

/** Pauses the hero field, the rotating headline and the logo strips. */
export function PauseToggle({ className = "" }: { className?: string }) {
  const paused = useAmbientPaused();
  return (
    <button
      type="button"
      className={`pause ${className}`}
      aria-pressed={paused}
      onClick={() => setAmbientPaused(!paused)}
    >
      {paused ? <Play size={14} aria-hidden="true" /> : <Pause size={14} aria-hidden="true" />}
      <span>{paused ? "Play motion" : "Pause motion"}</span>
    </button>
  );
}

/* ---------- entrances ---------- */

const itemVariants = {
  hidden: { opacity: 0, y: 14, filter: "blur(4px)" },
  show: { opacity: 1, y: 0, filter: "blur(0px)", transition: { duration: 0.62, ease: EASE_OUT } },
};

type Tag = "div" | "ul" | "ol" | "li" | "section" | "article" | "p" | "h1" | "h2" | "h3" | "figure" | "span";

/** Stagger container: its Item children arrive in reading order, once. */
export function In({
  children, className = "", stagger = 0.06, as = "div", delay = 0,
}: { children: ReactNode; className?: string; stagger?: number; as?: Tag; delay?: number }) {
  const M = motion[as] as typeof motion.div;
  return (
    <M
      className={className}
      initial="hidden"
      whileInView="show"
      viewport={VIEW}
      variants={{ hidden: {}, show: { transition: { staggerChildren: stagger, delayChildren: delay } } }}
    >
      {children}
    </M>
  );
}

/** One arriving element inside an In container. */
export function Item({ children, className = "", as = "div" }: { children: ReactNode; className?: string; as?: Tag }) {
  const M = motion[as] as typeof motion.div;
  return <M className={className} variants={itemVariants}>{children}</M>;
}

/* ---------- numbers ---------- */

/** Counts up from zero once, when half of it is on screen. Hard ease-out, 1.5s. */
export function CountUp({ value, prefix = "", suffix = "", className = "" }: { value: number; prefix?: string; suffix?: string; className?: string }) {
  const ref = useRef<HTMLSpanElement>(null);
  const inView = useInView(ref, { once: true, amount: 0.5 });
  const [n, setN] = useState(0);
  useEffect(() => {
    if (!inView) return;
    const c = animate(0, value, { duration: 1.5, ease: EASE_OUT, onUpdate: (v) => setN(Math.round(v)) });
    return () => c.stop();
  }, [inView, value]);
  return (
    <span ref={ref} className={`tabular-nums ${className}`} aria-label={`${prefix}${value.toLocaleString("en-AU")}${suffix}`}>
      <span aria-hidden="true">{prefix}{n.toLocaleString("en-AU")}{suffix}</span>
    </span>
  );
}

/* ---------- loops ---------- */

/** Infinite horizontal logo strip. The list is rendered twice for a seamless loop. */
export function Marquee({ items, speed = 38 }: { items: string[]; speed?: number }) {
  return (
    <div className="marquee" role="list" aria-label="Organisations">
      <div className="marquee__track" style={{ animationDuration: `${speed}s` }}>
        <div className="flex">{items.map((t) => <span role="listitem" key={t} className="marquee__item">{t}</span>)}</div>
        <div className="flex" aria-hidden="true">{items.map((t) => <span key={t} className="marquee__item">{t}</span>)}</div>
      </div>
    </div>
  );
}

/** Cycles the end of a headline. Stops when paused; with reduced motion the phrases crossfade in place. */
export function Rotator({ phrases, interval = 2800 }: { phrases: string[]; interval?: number }) {
  const paused = useAmbientPaused();
  const [i, setI] = useState(0);
  useEffect(() => {
    if (paused) return;
    const t = setInterval(() => setI((v) => (v + 1) % phrases.length), interval);
    return () => clearInterval(t);
  }, [paused, phrases.length, interval]);
  return (
    <span className="relative grid" style={{ gridTemplateAreas: "'s'" }}>
      {/* the longest phrase, invisible, reserves the space so the layout never jumps */}
      <span className="invisible" style={{ gridArea: "s" }} aria-hidden="true">
        {phrases.reduce((a, b) => (b.length > a.length ? b : a))}
      </span>
      <AnimatePresence mode="popLayout" initial={false}>
        <motion.em
          key={i}
          aria-hidden="true"
          className="accent"
          style={{ gridArea: "s" }}
          initial={{ y: "0.5em", opacity: 0, filter: "blur(6px)" }}
          animate={{ y: 0, opacity: 1, filter: "blur(0px)", transition: { duration: 0.6, ease: EASE_OUT } }}
          exit={{ y: "-0.3em", opacity: 0, filter: "blur(4px)", transition: { duration: 0.32, ease: EASE_OUT } }}
        >
          {phrases[i]}
        </motion.em>
      </AnimatePresence>
      <span className="sr-only">{phrases[0]}</span>
    </span>
  );
}

/* ---------- pan: vertical scroll, lateral travel (pinned) ---------- */

/**
 * The section pins and scrolling down slides the rail in from beyond the right
 * edge. Used for a range or a timeline. The visitor's scroll drives it, so it
 * runs with reduced motion too.
 */
export function HScroll({ intro, children }: { intro?: ReactNode; children: ReactNode }) {
  const outer = useRef<HTMLDivElement>(null);
  const track = useRef<HTMLDivElement>(null);
  const [m, setM] = useState({ dist: 0, start: 0 });

  useLayoutEffect(() => {
    const measure = () => {
      if (!track.current) return;
      const vw = document.documentElement.clientWidth;
      const trackW = track.current.scrollWidth;
      // measure the untransformed parent; the track itself is moving
      const left = track.current.parentElement!.getBoundingClientRect().left;
      const room = vw - left;
      // the first card peeks in from the right edge, the rest arrive with the scroll
      const start = room * 0.42;
      const dist = Math.max(0, trackW - room + Math.min(64, vw * 0.06));
      setM({ dist, start });
    };
    measure();
    const ro = new ResizeObserver(measure);
    if (track.current) ro.observe(track.current);
    window.addEventListener("resize", measure);
    return () => { ro.disconnect(); window.removeEventListener("resize", measure); };
  }, []);

  const progress = useSectionProgress(outer, ["start start", "end end"]);
  const x = useTransform(progress, [0.04, 0.94], [m.start, -m.dist]);

  // pacing: about 1.5px of scroll per px of travel, so the rail reads as a drawer, not a flick
  const travel = m.start + m.dist;
  return (
    <div ref={outer} style={{ height: `calc(100vh + ${Math.round(travel * 1.5)}px)` }} className="relative">
      <div className="sticky top-0 h-screen overflow-hidden flex items-center">
        <div className="wrap w-full">
          {intro && <div className="mb-10 md:mb-14">{intro}</div>}
          <motion.div ref={track} style={{ x }} className="flex gap-5 w-max will-change-transform">
            {children}
          </motion.div>
        </div>
      </div>
    </div>
  );
}

/** A rail item. It settles in from the right as it crosses into view; the first is already present. */
export function HCard({ children, className = "", width = 360, first = false }: { children: ReactNode; className?: string; width?: number; first?: boolean }) {
  return (
    <motion.div
      className={`shrink-0 snap-start ${className}`}
      style={{ width: `min(${width}px, 82vw)` }}
      initial={first ? false : { opacity: 0.5, x: 60 }}
      whileInView={{ opacity: 1, x: 0 }}
      viewport={{ amount: 0.4, once: true }}
      transition={{ duration: 0.7, ease: EASE_OUT }}
    >
      {children}
    </motion.div>
  );
}

/* ---------- arrival: items fly in from beyond the right edge, scrubbed, no pin ---------- */

/** Progress for a block whose items arrive while its top travels up the viewport. */
export function useArrive<T extends HTMLElement>() {
  const ref = useRef<T>(null);
  const progress = useSectionProgress(ref, ["start end", "start 25%"]);
  return { ref, progress };
}

export function ArriveItem({
  progress, i, n, children, className = "",
}: { progress: MotionValue<number>; i: number; n: number; children: ReactNode; className?: string }) {
  const s = (i / Math.max(1, n)) * 0.34;
  const e = Math.min(1, s + 0.6);
  const x = useTransform(progress, [s, e], ["64vw", "0vw"], { ease: easeOutFn });
  const opacity = useTransform(progress, [s, s + (e - s) * 0.7], [0, 1]);
  return <motion.div className={className} style={{ x, opacity }}>{children}</motion.div>;
}

/* ---------- words that light up with the scroll ---------- */

/** Each word brightens across its slice of [from, to] of the given progress. */
export function ScrubWords({
  text, progress, from = 0, to = 1, className = "", floor = 0.14,
}: { text: string; progress: MotionValue<number>; from?: number; to?: number; className?: string; floor?: number }) {
  const words = text.split(" ");
  const span = (to - from) / words.length;
  return (
    <p className={className} aria-label={text.replace(/\*/g, "")}>
      {words.map((w, i) => (
        <Word key={i} progress={progress} range={[from + i * span, from + (i + 1.6) * span]} word={w} floor={floor} />
      ))}
    </p>
  );
}

function Word({ progress, range, word, floor }: { progress: MotionValue<number>; range: [number, number]; word: string; floor: number }) {
  const opacity = useTransform(progress, range, [floor, 1]);
  const isAccent = word.includes("*");
  return (
    <motion.span aria-hidden="true" style={{ opacity }} className={isAccent ? "accent" : undefined}>
      {word.replace(/\*/g, "")}{" "}
    </motion.span>
  );
}

/* ---------- depth ---------- */

/** Vertical drift for a layer while its section scrolls past. Subtle: total travel is `amount` px. */
export function useDrift(target: RefObject<HTMLElement | null>, amount: number) {
  const reduce = useReducedMotion();
  const progress = useSectionProgress(target, ["start end", "end start"]);
  return useTransform(progress, [0, 1], reduce ? [0, 0] : [-amount / 2, amount / 2]);
}

/* ---------- pointer ---------- */

/**
 * The primary call to action leans toward the pointer (strength 0.28, springy,
 * never more than a few pixels). Fine pointers only, off under reduced motion.
 */
export function Magnetic({ children, strength = 0.28 }: { children: ReactNode; strength?: number }) {
  const ref = useRef<HTMLSpanElement>(null);
  const reduce = useReducedMotion();
  const mx = useMotionValue(0);
  const my = useMotionValue(0);
  const x = useSpring(mx, { stiffness: 300, damping: 20, mass: 0.6 });
  const y = useSpring(my, { stiffness: 300, damping: 20, mass: 0.6 });
  const [fine, setFine] = useState(false);
  useEffect(() => { setFine(window.matchMedia("(hover: hover) and (pointer: fine)").matches); }, []);
  if (reduce || !fine) return <>{children}</>;
  return (
    <motion.span
      ref={ref}
      className="inline-block"
      style={{ x, y }}
      onPointerMove={(e) => {
        const r = ref.current!.getBoundingClientRect();
        mx.set((e.clientX - (r.left + r.width / 2)) * strength);
        my.set((e.clientY - (r.top + r.height / 2)) * strength);
      }}
      onPointerLeave={() => { mx.set(0); my.set(0); }}
    >
      {children}
    </motion.span>
  );
}
