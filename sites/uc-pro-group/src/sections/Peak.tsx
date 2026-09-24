import { useRef } from "react";
import { motion, useTransform, useReducedMotion, useMotionTemplate } from "motion/react";
import { ScrubWords, useSectionProgress } from "../components/effects";
import { Accent } from "../components/ui";
import { group } from "../images";
import { belief } from "../content";

/*
  The peak, and the page's signature move.

  The belief statement lights up word by word on a quiet black stage. Then a
  gold U, the magnet from the logo and the hero, opens as a window onto the
  real photo of the community and keeps opening until the room fills the
  frame. The last line lands under it and holds.

  Tell-someone sentence: "it's the site where the sentence about not building
  alone lights up, and then a gold magnet opens into a room full of real founders."

  It gets the largest scroll span on the page (360vh) and the page's best asset.
  Reduced motion shows the finished state as an ordinary section.
*/

// Centre line of the U, in a 100 x 100 box. Stroke 22 gives the arms their weight.
const U = "M22 13 V52 A28 28 0 0 0 78 52 V13";
const U_MASK = `url("data:image/svg+xml,${encodeURIComponent(
  `<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'><path d='${U}' fill='none' stroke='white' stroke-width='22' stroke-linecap='round'/></svg>`,
)}")`;
// The outer and inner edges of that stroke, drawn as the logo's double line.
const U_EDGES = [
  "M11 13 V52 A39 39 0 0 0 89 52 V13",
  "M33 13 V52 A17 17 0 0 0 67 52 V13",
  "M11 13 A11 11 0 0 1 33 13",
  "M67 13 A11 11 0 0 1 89 13",
];

const frameClass = "relative w-[min(1180px,92vw)] aspect-[4/3] md:aspect-[2.35/1] rounded-[22px] overflow-hidden";

export function Peak() {
  const reduce = useReducedMotion();
  return reduce ? <PeakStill /> : <PeakScroll />;
}

function PeakScroll() {
  const ref = useRef<HTMLElement>(null);
  const p = useSectionProgress(ref, ["start start", "end end"]);

  // A: the statement lights up (0.06 to 0.40). B: the second line arrives and holds,
  // then the words clear completely before the room begins (authored silence at ~0.53).
  const line2 = useTransform(p, [0.3, 0.38], [0, 1]);
  const textOut = useTransform(p, [0.45, 0.54], [1, 0]);
  const textY = useTransform(p, [0.45, 0.54], [0, -48]);
  // C: the U window opens onto the room.
  const roomIn = useTransform(p, [0.52, 0.6], [0, 1]);
  const size = useTransform(p, [0.54, 0.84], [24, 150]);
  const maskSize = useMotionTemplate`${size}% auto`;
  const edgeScale = useTransform(size, (v) => v / 100);
  const edgeOpacity = useTransform(p, [0.54, 0.6, 0.78, 0.86], [0, 1, 1, 0]);
  const photoScale = useTransform(p, [0.54, 0.9], [1.22, 1]);
  const fill = useTransform(p, [0.74, 0.86], [0, 1]);
  // D: the last line lands under the room and holds to the end.
  const line3 = useTransform(p, [0.86, 0.93], [0, 1]);
  const line3Y = useTransform(p, [0.86, 0.93], [14, 0]);

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
          <div className={frameClass}>
            {/* the room, seen through the U */}
            <motion.div className="absolute inset-0" style={{
              WebkitMaskImage: U_MASK, maskImage: U_MASK,
              WebkitMaskRepeat: "no-repeat", maskRepeat: "no-repeat",
              WebkitMaskPosition: "50% 55%", maskPosition: "50% 55%",
              WebkitMaskSize: maskSize, maskSize,
            }}>
              <motion.img src={group} alt="" className="absolute inset-0 w-full h-full object-cover object-[50%_40%]" style={{ scale: photoScale }} />
            </motion.div>
            {/* the room, whole, once the U has opened */}
            <motion.img
              src={group}
              alt="Members of the Uncommon Collective community together at a Melbourne cafe"
              className="absolute inset-0 w-full h-full object-cover object-[50%_40%]"
              style={{ opacity: fill, scale: photoScale }}
            />
            {/* the gold magnet's edges, travelling with the window */}
            <motion.svg
              viewBox="0 0 100 100"
              aria-hidden="true"
              className="absolute left-1/2 top-[55%] w-full aspect-square pointer-events-none"
              style={{ translate: "-50% -55%", transformOrigin: "50% 55%", scale: edgeScale, opacity: edgeOpacity }}
            >
              {U_EDGES.map((d) => (
                <path key={d} d={d} fill="none" stroke="var(--gold)" strokeWidth="1.5" vectorEffect="non-scaling-stroke" strokeLinecap="round" />
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

function PeakStill() {
  return (
    <section className="g g-black grain sec" aria-label={belief.eyebrow}>
      <div className="wrap max-w-[1040px] text-center">
        <p className="eyebrow">{belief.eyebrow}</p>
        <p className="serif font-bold text-[clamp(2.1rem,5.2vw,4.4rem)] leading-[1.06] tracking-[-.015em] m-0 text-balance"><Accent text={belief.statement} /></p>
        <p className="mt-10 text-[clamp(1.1rem,1.8vw,1.45rem)] c-bone font-light">{belief.line2}</p>
      </div>
      <div className="mt-14 flex flex-col items-center gap-8">
        <div className={frameClass}>
          <img src={group} alt="Members of the Uncommon Collective community together at a Melbourne cafe" className="absolute inset-0 w-full h-full object-cover object-[50%_40%]" />
        </div>
        <p className="wrap text-center serif italic c-gold text-[clamp(1.25rem,2.2vw,1.8rem)] leading-snug max-w-[720px]">{belief.line3}</p>
      </div>
    </section>
  );
}
