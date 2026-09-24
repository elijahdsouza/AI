import { useEffect, useRef, useState } from "react";
import { motion, useTransform, useReducedMotion } from "motion/react";
import { Disc, Head, Section, Cta, Accent } from "../components/ui";
import {
  CountUp, Marquee, Rotator, HScroll, HCard, In, Item, Magnetic, PauseToggle, useArrive, ArriveItem, useSectionProgress,
} from "../components/effects";
import HeroMagnet from "../components/HeroMagnet";
import { group, crowd, logoWhite } from "../images";
import { site, nav, hero, stats, logosTop, problem, callout, alternatives } from "../content";

export function Header() {
  const [scrolled, setScrolled] = useState(false);
  useEffect(() => {
    const on = () => setScrolled(window.scrollY > 40);
    on(); window.addEventListener("scroll", on, { passive: true });
    return () => window.removeEventListener("scroll", on);
  }, []);
  return (
    <header className={`bar ${scrolled ? "scrolled" : ""}`}>
      <div className="wrap bar__in">
        <a href="#top" className="flex items-center no-underline" aria-label="Uncommon Collective, back to top">
          <Logo className="h-[30px] lg:h-[34px]" />
        </a>
        <nav aria-label="Sections" className="hidden lg:flex gap-7">
          {nav.map((n) => <a key={n.href} href={n.href}>{n.label}</a>)}
        </nav>
        <Cta small />
      </div>
    </header>
  );
}

/** The Uncommon Collective logo (magnet mark and wordmark), white, from the live site. */
export function Logo({ className = "" }: { className?: string }) {
  return <img src={logoWhite} alt="" width={534} height={147} className={`w-auto ${className}`} />;
}

function useCountdown(iso: string) {
  const target = new Date(iso).getTime();
  const [now, setNow] = useState(() => Date.now());
  useEffect(() => { const t = setInterval(() => setNow(Date.now()), 1000); return () => clearInterval(t); }, []);
  const d = Math.max(0, target - now);
  return { days: Math.floor(d / 864e5), hrs: Math.floor(d / 36e5) % 24, min: Math.floor(d / 6e4) % 60, sec: Math.floor(d / 1e3) % 60 };
}

const faces = ["-43px -50px", "-135px -71px", "-280px -52px", "-354px -63px", "-488px -50px", "-658px -71px"];

/**
 * Hero, built as three planes that separate as you scroll away: the real room
 * far back (slowest), the magnetic field in the middle, the words in front at 1x.
 */
export function Hero() {
  const c = useCountdown(site.deadlineISO);
  const ref = useRef<HTMLElement>(null);
  const reduce = useReducedMotion();
  const scrollYProgress = useSectionProgress(ref, ["start start", "end start"]);
  const farY = useTransform(scrollYProgress, [0, 1], reduce ? [0, 0] : [0, 90]);
  const midY = useTransform(scrollYProgress, [0, 1], reduce ? [0, 0] : [0, 70]);
  const midFade = useTransform(scrollYProgress, [0, 0.8], reduce ? [1, 1] : [1, 0.35]);
  return (
    <section ref={ref} id="top" className="g g-black grain relative overflow-hidden">
      <div className="relative overflow-hidden">
      {/* far plane: a real UC night from the live site, under an even dark overlay */}
      <motion.div aria-hidden="true" style={{ y: farY }} className="absolute inset-x-0 top-[-10%] bottom-[-10%]">
        <img src={crowd} alt="" className="w-full h-full object-cover object-[50%_40%]" />
      </motion.div>
      <div aria-hidden="true" className="hero-overlay absolute inset-0" />

      <div className="relative wrap grid lg:grid-cols-[1.25fr_1fr] items-center gap-6 min-h-[100svh] pt-[110px] pb-10">
        <In className="relative z-10 max-w-[720px]" stagger={0.08}>
          <Item as="p" className="eyebrow">{hero.eyebrow}</Item>
          <Item as="h1" className="h1">
            {hero.stem}{" "}
            <Rotator phrases={hero.rotating} />
          </Item>
          <Item as="p" className="lede text-[1.08rem]">{hero.sub}</Item>
          <Item className="mt-9 flex flex-wrap items-center gap-x-7 gap-y-4">
            <Magnetic><Cta /></Magnetic>
            <a className="link" href="#pricing">{hero.secondary}</a>
          </Item>
          <Item as="p" className="mt-5 text-sm fg2"><a className="link fg2" href={site.freeUrl}>{hero.freeLink}</a></Item>
          <Item className="mt-9 pt-7 border-t b-line flex items-center gap-4">
            <div className="flex">
              {faces.map((p, i) => (
                <span key={i} className="block w-9 h-9 rounded-full border-2 b-black -ml-2 first:ml-0"
                  style={{ backgroundImage: `url(${group})`, backgroundSize: "735px 234px", backgroundPosition: p, backgroundColor: "#2a2620" }} />
              ))}
            </div>
            <p className="text-[13px] leading-snug fg2 max-w-[300px]">{hero.proof}</p>
          </Item>
        </In>
        {/* middle plane: the magnetic field */}
        <motion.div style={{ y: midY, opacity: midFade }} className="relative h-[46vh] min-h-[320px] lg:h-[74vh] -mx-[var(--gutter)] lg:mx-0">
          <HeroMagnet className="absolute inset-0" />
          <PauseToggle className="absolute bottom-3 right-4 lg:right-0" />
        </motion.div>
      </div>
      </div>

      <div className="relative border-t b-line">
        <div className="wrap flex flex-wrap items-center justify-between gap-4 py-4">
          <p className="flex items-center gap-3 mono text-[11px] tracking-[.16em] uppercase fg2">
            <span className="w-1.5 h-1.5 rounded-full bg-gold" aria-hidden="true" />
            {hero.countdownLabel} {site.deadlineLabel}
          </p>
          <div className="flex gap-2" role="timer" aria-label={`${c.days} days ${c.hrs} hours left`}>
            {[[c.days, "days"], [c.hrs, "hrs"], [c.min, "min"], [c.sec, "sec"]].map(([v, l]) => (
              <span key={l} className="mono text-[11px] tracking-[.12em] uppercase px-3 py-2 rounded-md bg-[rgba(243,239,230,.06)] border b-line c-bone tabular-nums">
                <b className="c-gold font-medium">{String(v).padStart(2, "0")}</b> {l}
              </span>
            ))}
          </div>
        </div>
      </div>
      <div className="relative border-t b-line">
        <In className="wrap grid grid-cols-2 md:grid-cols-5" stagger={0.05}>
          {hero.benefits.map((b, i) => (
            <Item key={b.title} className={`py-7 pr-4 ${i > 0 ? "md:pl-6 md:border-l b-line" : ""}`}>
              <Disc name={b.icon} className="!w-10 !h-10" />
              <p className="mt-4 serif font-bold text-[1.02rem]">{b.title}</p>
              <p className="mt-1 text-[13px] leading-snug fg2">{b.body}</p>
            </Item>
          ))}
        </In>
      </div>
    </section>
  );
}

export function Stats() {
  return (
    <Section ground="black" tight className="border-t b-line grain">
      <In className="wrap grid grid-cols-2 lg:grid-cols-4 gap-y-10 gap-x-6" stagger={0.07}>
        {stats.map((s) => (
          <Item key={s.label}>
            <CountUp className="block serif font-bold text-[clamp(2.4rem,4.5vw,3.6rem)] leading-none c-gold" value={s.value} prefix={s.prefix} suffix={s.suffix} />
            <p className="mt-3 text-[13px] fg2 max-w-[220px]">{s.label}</p>
          </Item>
        ))}
      </In>
    </Section>
  );
}

export function LogosTop() {
  return (
    <Section ground="white" tight>
      <div className="wrap"><p className="mono text-[11px] tracking-[.18em] uppercase fg2 text-center m-0">{logosTop.label}</p></div>
      <div className="mt-6"><Marquee items={logosTop.names} /></div>
      <div className="wrap mt-6 text-center"><span className="tbc">{logosTop.tbc}</span></div>
    </Section>
  );
}

/** Pan: the four points arrive sideways while the section holds still. */
export function Problem() {
  return (
    <section id="problem" className="g g-white">
      <HScroll intro={<Head title={problem.h2} className="max-w-[760px]" />}>
        {problem.points.map((p, i) => (
          <HCard key={p.title} width={380} first={i === 0}>
            <article className="card p-8 h-full min-h-[300px] flex flex-col">
              <Disc name={p.icon} />
              <h3 className="h3 mt-8">{p.title}</h3>
              <p className="body">{p.body}</p>
            </article>
          </HCard>
        ))}
      </HScroll>
    </section>
  );
}

/** Sits across the seam between the problem and the alternatives. */
export function Callout() {
  return (
    <div className="relative z-20 h-0">
      <div className="wrap">
        <div className="g g-gold -translate-y-1/2 rounded-[22px] px-8 py-9 md:px-14 md:py-12 text-center shadow-[0_30px_80px_-30px_rgba(60,48,12,.55)]">
          <In><Item as="p" className="serif font-bold text-[clamp(1.5rem,3vw,2.4rem)] leading-tight text-balance m-0"><Accent text={callout} /></Item></In>
        </div>
      </div>
    </div>
  );
}

/** Arrival: the options fly in from beyond the right edge as you scroll, no pin. */
export function Alternatives() {
  const { ref, progress } = useArrive<HTMLDivElement>();
  const n = alternatives.cards.length + 1;
  return (
    <section id="alternatives" className="g g-grey overflow-x-clip pt-[150px] md:pt-[180px] pb-[clamp(80px,11vw,150px)]">
      <div className="wrap grid lg:grid-cols-[minmax(300px,420px)_1fr] gap-10 lg:gap-14 items-start">
        <In className="lg:sticky lg:top-28">
          <Item as="h2" className="h2 !text-[clamp(1.7rem,2.6vw,2.4rem)]"><Accent text={alternatives.h2} /></Item>
        </In>
        <div ref={ref} className="grid sm:grid-cols-2 gap-4">
          {alternatives.cards.map((c, i) => (
            <ArriveItem key={c.title} progress={progress} i={i} n={n}>
              <article className="card p-7 h-full">
                <Disc name={c.icon} />
                <h3 className="h3 mt-6">{c.title}</h3>
                <p className="body">{c.body}</p>
              </article>
            </ArriveItem>
          ))}
          <ArriveItem progress={progress} i={n - 1} n={n} className="sm:col-span-2">
            <article className="g g-gold rounded-[18px] p-8 md:p-10">
              <h3 className="h3 !text-[1.6rem]">{alternatives.final.title}</h3>
              <p className="body fg2 !text-[1rem]">{alternatives.final.body}</p>
            </article>
          </ArriveItem>
        </div>
      </div>
    </section>
  );
}
