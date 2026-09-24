import { useLayoutEffect, useRef } from "react";
import { motion, useTransform, useReducedMotion, useMotionValue, cubicBezier, type MotionValue } from "motion/react";
import { ScrubWords, useSectionProgress, EASE_IN_OUT } from "../components/effects";
import { OUTLINE, DOMES, BAND, markBounds, makeTf, pathData, type Pt } from "../components/ucMark";
import { group } from "../images";
import { belief } from "../content";

/*
  The peak, and the page's signature move.

  The belief statement lights up word by word on a quiet black stage. The words
  clear, and the UC magnet (the logo's own outline, in gold) appears with the
  real photo of the community showing through it. Then the view flies into the
  magnet's band until the room fills the frame. The last line lands under it.

  Tell-someone sentence: "it's the site where the sentence about not building
  alone lights up, and then you fly through the gold magnet into a room full of
  real founders."

  It gets the largest scroll span on the page (360vh) and the page's best asset.
  The visitor's scroll drives all of it, so it also runs with reduced motion;
  only the photo's slow push-in and the text drift are dropped there.
*/

const { width: MW, height: MH, centre: MC } = markBounds();
const easeZoom = cubicBezier(...EASE_IN_OUT);

/** The view at zoom t: 0 is the whole mark centred in the frame, 1 is inside its band. */
function view(t: number, fw: number, fh: number) {
  const s0 = (0.62 * fh) / Math.max(MW, MH);
  // the band is about 171 logo units either side of its middle; keep the frame's corners inside that
  const s1 = Math.hypot(fw, fh) / 2 / 150;
  const s = s0 * Math.pow(s1 / s0, t);
  // slide the anchor from the mark's centre to the band so the band point glides to the middle
  const u = 1 - (s0 / s) * (1 - t) * (1 - t);
  const anchor: Pt = [MC[0] + (BAND[0] - MC[0]) * u, MC[1] + (BAND[1] - MC[1]) * u];
  return { tf: makeTf(anchor, [fw / 2, fh / 2], s), s };
}

const frameClass = "relative w-[min(1180px,92vw)] aspect-[4/3] md:aspect-[2.35/1] rounded-[22px] overflow-hidden";

export function Peak() {
  const ref = useRef<HTMLElement>(null);
  const frame = useRef<HTMLDivElement>(null);
  const reduce = useReducedMotion();
  const p = useSectionProgress(ref, ["start start", "end end"]);

  // the frame's size, for the magnet's path
  const fw = useMotionValue(1180);
  const fh = useMotionValue(502);
  useLayoutEffect(() => {
    const el = frame.current!;
    const ro = new ResizeObserver(() => { fw.set(el.clientWidth); fh.set(el.clientHeight); });
    ro.observe(el);
    return () => ro.disconnect();
  }, [fw, fh]);

  // A: the statement lights up (0.06 to 0.40). B: the second line arrives and holds,
  // then the words clear before the room begins (authored silence at ~0.53).
  const line2 = useTransform(p, [0.3, 0.38], [0, 1]);
  const textOut = useTransform(p, [0.45, 0.54], [1, 0]);
  const textY = useTransform(p, [0.45, 0.54], reduce ? [0, 0] : [0, -48]);
  // C: the magnet appears with the room inside it, then the view flies into its band.
  const roomIn = useTransform(p, [0.52, 0.58], [0, 1]);
  const zoom = useTransform(p, [0.56, 0.86], [0, 1], { ease: easeZoom });
  const at = (build: (tf: ReturnType<typeof view>["tf"], s: number) => string) =>
    ([t, w, h]: number[]) => { const v = view(t, w, h); return build(v.tf, v.s); };
  const clip = useTransform([zoom, fw, fh] as MotionValue<number>[], at((tf, s) => `path("${pathData(OUTLINE, tf, s, true)}")`));
  const outlineD = useTransform([zoom, fw, fh] as MotionValue<number>[], at((tf, s) => pathData(OUTLINE, tf, s, true)));
  const domeL = useTransform([zoom, fw, fh] as MotionValue<number>[], at((tf, s) => pathData(DOMES[0], tf, s, false)));
  const domeR = useTransform([zoom, fw, fh] as MotionValue<number>[], at((tf, s) => pathData(DOMES[1], tf, s, false)));
  const edgeOpacity = useTransform(p, [0.54, 0.6, 0.8, 0.88], [0, 1, 1, 0]);
  const photoScale = useTransform(p, [0.54, 0.9], reduce ? [1, 1] : [1.22, 1]);
  const fill = useTransform(p, [0.8, 0.9], [0, 1]);
  // D: the last line lands under the room and holds to the end.
  const line3 = useTransform(p, [0.88, 0.94], [0, 1]);
  const line3Y = useTransform(p, [0.88, 0.94], reduce ? [0, 0] : [14, 0]);

  return (
    <section ref={ref} className="g g-black grain relative" style={{ height: "360vh" }} aria-label={belief.eyebrow}>
      <div className="sticky top-0 h-screen overflow-hidden">
        <div aria-hidden="true" className="absolute inset-0" style={{ background: "radial-gradient(60% 50% at 50% 55%, rgba(var(--gold-rgb),.10), transparent 70%)" }} />

        <motion.div style={{ opacity: textOut, y: textY }} className="absolute inset-0 flex items-center">
          <div className="wrap max-w-[1040px] text-center">
            <p className="eyebrow">{belief.eyebrow}</p>
            <ScrubWords
              text={belief.statement}
              progress={p}
              from={0.06}
              to={0.4}
              className="serif font-bold text-[clamp(2.1rem,5.2vw,4.4rem)] leading-[1.06] tracking-[-.015em] m-0 text-balance"
            />
            <motion.p style={{ opacity: line2 }} className="mt-10 text-[clamp(1.1rem,1.8vw,1.45rem)] c-bone font-light">
              {belief.line2}
            </motion.p>
          </div>
        </motion.div>

        <motion.div style={{ opacity: roomIn }} className="absolute inset-0 flex flex-col items-center justify-center gap-8">
          <div ref={frame} className={frameClass}>
            {/* the room, seen through the magnet */}
            <motion.div className="absolute inset-0" style={{ clipPath: clip }}>
              <motion.img src={group} alt="" className="absolute inset-0 w-full h-full object-cover object-[50%_40%]" style={{ scale: photoScale }} />
            </motion.div>
            {/* the room, whole, once the view is inside the band */}
            <motion.img
              src={group}
              alt="Members of the Uncommon Collective community together at a Melbourne cafe"
              className="absolute inset-0 w-full h-full object-cover object-[50%_40%]"
              style={{ opacity: fill, scale: photoScale }}
            />
            {/* the logo's gold outline, travelling with the window */}
            <motion.svg aria-hidden="true" className="absolute inset-0 w-full h-full pointer-events-none" style={{ opacity: edgeOpacity }}>
              {[outlineD, domeL, domeR].map((d, i) => (
                <motion.path key={i} d={d} fill="none" stroke="var(--gold)" strokeWidth={1.6} strokeLinecap="round" strokeLinejoin="round" />
              ))}
            </motion.svg>
          </div>
          <motion.p style={{ opacity: line3, y: line3Y }} className="wrap text-center serif italic c-gold text-[clamp(1.25rem,2.2vw,1.8rem)] leading-snug max-w-[720px]">
            {belief.line3}
          </motion.p>
        </motion.div>
      </div>
    </section>
  );
}
