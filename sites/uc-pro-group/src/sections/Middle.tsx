import { useRef, useState } from "react";
import { AnimatePresence, motion } from "motion/react";
import { Check, X, Minus } from "lucide-react";
import { Disc, Head, Section, Cta, Accent, Copy, Photo } from "../components/ui";
import { Marquee, HScroll, HCard, In, Item, Typewriter, useDrift, EASE_OUT } from "../components/effects";
import { img, proGroupPhoto } from "../images";
import { proGroup, expect, rhythm, logosBottom, pricing, anchor, compare, type Period } from "../content";

/** Opens under the gold bridge callout, hence the deep top padding. The photo takes the right-hand page. */
export function ProGroup() {
  return (
    <Section id="pro-group" ground="green" className="grain !pt-[clamp(150px,14vw,200px)]">
      <div className="wrap">
        <div className="grid lg:grid-cols-[1.08fr_1fr] gap-10 lg:gap-16 items-center">
          <In>
            <Item as="p" className="eyebrow">{proGroup.eyebrow}</Item>
            <Item as="h2" className="h2 !text-[clamp(2.1rem,4.2vw,3.5rem)]">
              {proGroup.stem}{" "}
              <Typewriter phrases={proGroup.rotating} still={proGroup.still} />
            </Item>
            <Item as="p" className="lede">{proGroup.lede}</Item>
          </In>
          <In><Item><Photo src={proGroupPhoto} alt={proGroup.photoAlt} label="community meetup" className="aspect-[4/3] lg:aspect-square" /></Item></In>
        </div>
        <In className="mt-16 grid sm:grid-cols-2 lg:grid-cols-5 gap-x-6 gap-y-10 border-t b-line pt-12" stagger={0.05}>
          {proGroup.pillars.map((p) => (
            <Item key={p.title}>
              <Disc name={p.icon} />
              <h3 className="h3 mt-5 !text-[1.05rem]">{p.title}</h3>
              <Copy text={p.body} className="body !text-[.88rem]" />
            </Item>
          ))}
        </In>
        <In className="mt-16 grid sm:grid-cols-2 lg:grid-cols-4 gap-x-8 gap-y-10" stagger={0.05}>
          {proGroup.tiles.map((t) => (
            <Item key={t.title} as="article" className="border-t-2 border-[var(--gold)] pt-5">
              <h3 className="h3 !text-[1.1rem]">{t.title}</h3>
              <p className="body !text-[.9rem]">{t.body}</p>
            </Item>
          ))}
        </In>
      </div>
    </Section>
  );
}

export function Expect() {
  return (
    <Section id="expect" ground="white">
      <div className="wrap">
        <Head center title={expect.h2} lede={expect.lede} />

        <h3 className="serif font-bold text-[1.5rem] mt-20 mb-6">{expect.experiencesTitle}</h3>
        <In className="grid grid-cols-2 lg:grid-cols-3 gap-4 md:gap-5" stagger={0.07}>
          {expect.experiences.map((e) => (
            <Item key={e.title}>
              <Photo src={img(e.img)} alt={e.title} label={e.title} className="aspect-[4/5]">
                <p className="serif font-bold text-[1.15rem] md:text-[1.35rem] leading-tight">{e.title}</p>
                <p className="body !mt-1 !text-[.86rem] hidden sm:block">{e.body}</p>
              </Photo>
            </Item>
          ))}
        </In>

        <h3 className="serif font-bold text-[1.5rem] mt-20 mb-6"><Accent text={expect.servicesTitle} /></h3>
        {/* on phones the cards are too narrow for the discount chip, so it's said once here instead */}
        <p className="sm:hidden -mt-3 mb-5"><span className="inline-block rounded-full px-3 py-1.5 text-[12px] font-semibold bg-gold text-[#16140f]">{expect.memberDeal}</span></p>
        <In className="grid grid-cols-2 lg:grid-cols-3 gap-4 md:gap-5" stagger={0.07}>
          {expect.services.map((s) => (
            <Item key={s.title}>
              <Photo src={img(s.img)} alt={s.title} label={s.title} className="aspect-[4/3]">
                <p className="serif font-bold text-[1.05rem] md:text-[1.25rem] leading-tight">{s.title}</p>
                <p className="mt-2.5 m-0 hidden sm:block"><span className="inline-block rounded-full px-2.5 py-1 text-[10.5px] md:text-[11.5px] leading-snug font-semibold bg-gold text-[#16140f]">{expect.memberDeal}</span></p>
              </Photo>
            </Item>
          ))}
        </In>

        <In className="mt-20 grid md:grid-cols-[1fr_1.1fr] gap-8 md:gap-12 items-center">
          <Item className="aspect-[16/10] rounded-[18px] border border-dashed b-line bg-[#f7f5ef] grid place-items-center p-6 text-center">
            <span className="tbc">{expect.tools.placeholder}</span>
          </Item>
          <Item>
            <h3 className="serif font-bold text-[1.7rem]">{expect.tools.title}</h3>
            <p className="lede !mt-3">{expect.tools.body}</p>
          </Item>
        </In>
      </div>
    </Section>
  );
}

export function Rhythm() {
  return (
    <section id="rhythm" className="g g-black">
      <HScroll
        intro={
          <div className="grid md:grid-cols-[1fr_1fr] gap-8 items-end">
            <Head title={rhythm.h2} lede={rhythm.lede} />
            <Photo src={img("coworkWide")} alt="Members working side by side at a coworking day" label="coworking day" className="aspect-[16/8] hidden md:block" />
          </div>
        }
      >
        {rhythm.cards.map((c, i) => (
          <HCard key={c.title} width={300} first={i === 0}>
            <article className="card p-7 h-full min-h-[250px]">
              <Disc name={c.icon} />
              <p className="mono text-[11px] tracking-[.16em] uppercase c-gold mt-6">{c.when}</p>
              <h3 className="h3 mt-2">{c.title}</h3>
              <p className="body !text-[.9rem]">{c.body}</p>
            </article>
          </HCard>
        ))}
      </HScroll>
    </section>
  );
}

export function LogosBottom() {
  return (
    <Section ground="white" tight className="border-b b-line">
      <div className="wrap"><p className="mono text-[11px] tracking-[.18em] uppercase fg2 text-center m-0">{logosBottom.label}</p></div>
      <div className="mt-6"><Marquee items={logosBottom.names} speed={46} /></div>
    </Section>
  );
}

/** A wide photo whose picture drifts a little inside its frame as the page scrolls past. */
export function DriftPhoto({ src, alt, className = "" }: { src: string; alt: string; className?: string }) {
  const ref = useRef<HTMLElement>(null);
  const y = useDrift(ref, 70);
  return (
    <figure ref={ref} className={`photo m-0 ${className}`}>
      <span className="photo-fallback">{alt}</span>
      <motion.img src={src} alt={alt} loading="lazy" decoding="async" onError={(e) => { e.currentTarget.style.visibility = "hidden"; }} style={{ y, scale: 1.14 }} className="!transition-none" />
    </figure>
  );
}

type Tier = (typeof pricing.tiers)[number];

function TierCard({ t, period }: { t: Tier; period: Period }) {
  const dark = "dark" in t && t.dark;
  const price = "price" in t && t.price ? t.price[period] : undefined;
  return (
    <motion.article
      layout
      initial={{ opacity: 0, y: 16 }}
      animate={{ opacity: 1, y: 0 }}
      exit={{ opacity: 0, y: -10 }}
      transition={{ duration: 0.45, ease: EASE_OUT }}
      className={`g ${dark ? "g-black" : "g-white"} relative rounded-[20px] border p-7 flex flex-col ${dark ? "border-[rgba(187,171,105,.35)] shadow-[0_30px_70px_-35px_rgba(0,0,0,.6)]" : "b-line"}`}
    >
      {"badge" in t && t.badge && (
        <span className="self-start mono text-[10px] tracking-[.16em] uppercase px-3 py-1.5 rounded-full bg-gold text-[#16140f] font-medium mb-4">{t.badge}</span>
      )}
      <h3 className="serif font-bold text-[1.6rem] leading-tight">{t.name}</h3>
      <p className="serif italic font-bold c-acc mt-1 text-[1.2rem] leading-snug">{t.tagline}</p>
      <p className="body !text-[.88rem]">{t.intro}</p>

      {t.id === "free" && (
        <div className="mt-6">
          <p className="serif font-bold text-[3rem] leading-none c-acc">Free <span className="text-[.9rem] font-normal fg2" style={{ fontFamily: "var(--text)" }}>forever</span></p>
          <p className="text-[12px] fg2 mt-2">No card required</p>
        </div>
      )}
      {price && (
        <div className="mt-6">
          <p className="flex items-baseline gap-2">
            <s className="fg2 text-[1.1rem]">${price.was}</s>
            <span className={`serif font-bold text-[3.2rem] leading-none ${dark ? "c-gold" : ""}`}>${price.now}</span>
            <span className="fg2 text-sm">/mo</span>
          </p>
          <p className="text-[12px] fg2 mt-2">{price.billed}</p>
        </div>
      )}
      {"chip" in t && t.chip && <p className="mt-4 text-[12px] font-medium rounded-lg px-3 py-2 bg-chip">{t.chip}</p>}
      {price && <p className="mt-4 text-[12px] font-medium rounded-lg px-3 py-2 bg-chip">{price.chip}</p>}
      {"qualify" in t && t.qualify && (
        <div className="mt-5 rounded-xl border border-dashed border-[rgba(187,171,105,.55)] p-4">
          <p className="mono text-[10px] tracking-[.14em] uppercase c-gold">{t.qualify.title}</p>
          <ul className="mt-2 space-y-1 text-[13px]">{t.qualify.items.map((q) => <li key={q}>{q}</li>)}</ul>
        </div>
      )}
      {"bespoke" in t && t.bespoke && <p className="mt-5 text-[13px] leading-relaxed rounded-xl p-4 bg-chip">{t.bespoke}</p>}
      {"guarantee" in t && t.guarantee && <p className="mt-3 text-[12px] font-medium flex items-center gap-2"><Check size={14} className="c-acc" /> {t.guarantee}</p>}

      <Cta className="mt-6 w-full" />

      <p className="mt-7 text-[12px] font-semibold c-acc-sm">{t.listTitle}</p>
      <ul className="mt-3 space-y-2.5">
        {t.items.map((it) => (
          <li key={it} className="flex gap-2.5 text-[13.5px] leading-snug"><Check size={16} className="check" />{it}</li>
        ))}
      </ul>
    </motion.article>
  );
}

export function Pricing() {
  const [period, setPeriod] = useState<Period>("monthly");
  const tiers = pricing.tiers.filter((t) => t.show.includes(period));
  return (
    <Section id="pricing" ground="white">
      <div className="wrap">
        <Head center eyebrow={pricing.eyebrow} title={pricing.h2} lede={pricing.lede} />
        <DriftPhoto src={img("walk")} alt="Founders walking together along the river at golden hour" className="mt-12 h-[200px] md:h-[260px]" />

        <div className="mt-12 flex flex-col items-center">
          <div role="tablist" aria-label="Billing period" className="inline-flex p-1.5 rounded-full border b-line bg-white shadow-sm">
            {pricing.periods.map((p) => (
              <button
                key={p.id}
                role="tab"
                aria-selected={period === p.id}
                onClick={() => setPeriod(p.id)}
                className="relative px-5 py-2.5 rounded-full text-[14px] font-medium transition-colors"
                style={{ color: period === p.id ? "#fff" : "var(--fg)" }}
              >
                {period === p.id && <motion.span layoutId="period-pill" className="absolute inset-0 rounded-full bg-[#16140f]" transition={{ type: "spring", stiffness: 420, damping: 34 }} />}
                <span className="relative">{p.label}{"note" in p && p.note ? <span className="opacity-70"> · {p.note}</span> : null}</span>
              </button>
            ))}
          </div>
          <p className="mt-3 text-[13px] fg2">{pricing.periodNotes[period]}</p>
        </div>

        <In><Item>
          <motion.div layout className={`mt-10 grid gap-5 items-start ${tiers.length === 4 ? "md:grid-cols-2 xl:grid-cols-4" : "md:grid-cols-3 max-w-[1080px] mx-auto"}`}>
            <AnimatePresence mode="popLayout" initial={false}>
              {tiers.map((t) => <TierCard key={t.id} t={t} period={period} />)}
            </AnimatePresence>
          </motion.div>
        </Item></In>
        {/* risk reversal, straight under the decision */}
        <In className="mt-12 grid sm:grid-cols-2 lg:grid-cols-4 gap-px bg-[var(--line)] rounded-[20px] border b-line overflow-hidden" stagger={0.06}>
          {pricing.assurances.map((a) => (
            <Item key={a.title} className="bg-white p-5 sm:p-6 md:p-7 flex gap-4 sm:block">
              <Disc name={a.icon} className="!w-10 !h-10" />
              <div>
                <h3 className="h3 sm:mt-4 !text-[1.05rem]">{a.title}</h3>
                <p className="body !text-[.88rem] !mt-1.5">{a.body}</p>
              </div>
            </Item>
          ))}
        </In>
      </div>
    </Section>
  );
}

export function Anchor() {
  return (
    <Section ground="gold" tight className="on-gold-white">
      <In className="wrap flex flex-wrap items-center justify-center gap-x-12 gap-y-4 text-center">
        {anchor.prices.map((p) => (
          <Item as="p" key={p.value} className="flex items-baseline gap-2">
            <span className="serif font-bold text-[2.4rem] leading-none">{p.value}</span>
            <span className="text-[13px] opacity-90">{p.unit}</span>
          </Item>
        ))}
        <Item as="p" className="serif font-bold text-[1.35rem] max-w-[380px] leading-snug">{anchor.line}</Item>
      </In>
    </Section>
  );
}

const Mark = ({ k }: { k: string }) =>
  k === "y" ? <Check size={15} className="text-[#2f7a4f] shrink-0 mt-0.5" /> :
  k === "n" ? <X size={15} className="text-[#b0413e] shrink-0 mt-0.5" /> :
  k === "t" ? null :
  <Minus size={15} className="text-[#9a8a55] shrink-0 mt-0.5" />;

// The first column stays put while the rest scrolls sideways: it sits above the moving
// cells (the gold header is positioned too, so without a z-index it painted over it),
// carries a hairline edge, and is narrower on phones to leave room for the comparison.
const pinned = "sticky left-0 z-[2] bg-white p-4 w-[150px] min-w-[150px] md:w-[190px] md:min-w-[190px] shadow-[inset_-1px_0_0_rgba(22,20,15,.1)]";

export function Compare() {
  return (
    <Section id="compare" ground="grey">
      {/* wider than the other sections so seven columns fit without scrolling on a laptop */}
      <div className="wrap max-w-[1360px]">
        <Head center eyebrow={compare.eyebrow} title={compare.h2} lede={compare.lede} />
        <In><Item className="mt-14 relative">
          <div className="overflow-x-auto rounded-[20px] bg-white no-scrollbar">
          <table className="w-full min-w-[1100px] border-collapse text-left">
            <caption className="sr-only">UC Pro Group compared with Art of Mondays, Entrepreneurship Dinner Club, accelerators, studios, coaches and free online groups</caption>
            <thead>
              <tr>
                <th className={`${pinned} text-[12px] font-medium fg2 align-bottom`}>What you actually get</th>
                {compare.columns.map((c, i) => (
                  <th key={c.name} className={`p-4 align-bottom ${i === 0 ? "g g-gold on-gold-white border-b border-b-white" : ""}`}>
                    <span className="block serif font-bold text-[1rem]">{c.name}</span>
                    <span className={`block text-[11.5px] mt-1 ${i === 0 ? "opacity-90" : "fg2"} font-normal`}>{c.sub}</span>
                  </th>
                ))}
              </tr>
            </thead>
            <tbody>
              {compare.rows.map((r) => (
                <tr key={r.q} className="border-t b-line">
                  <th scope="row" className={`${pinned} text-[12.5px] md:text-[13.5px] font-medium`}>{r.q}</th>
                  {r.cells.map(([k, v], i) => (
                    <td key={i} className={`p-4 text-[13px] leading-snug ${i === 0 ? "bg-[rgba(187,171,105,.1)] font-medium" : "fg2"}`}>
                      {k === "t" ? <span className="tbc !text-[10px]">{v}</span> : <span className="flex gap-2"><Mark k={k} />{v}</span>}
                    </td>
                  ))}
                </tr>
              ))}
            </tbody>
          </table>
          </div>
          {/* The frame is drawn above the table. On phones with fractional pixel ratios the
              scrolling cells show through as a one-pixel sliver along the pinned column's left
              edge (and the gold header's white foot does the same job at the header seam);
              the frame's inner white edge covers it. Outward shadows on table cells aren't painted. */}
          <span aria-hidden="true" className="pointer-events-none absolute inset-0 z-[3] rounded-[20px] shadow-[inset_3px_0_0_#fff,inset_0_0_0_1px_var(--line)]" />
        </Item></In>
        <p className="mt-4 text-center"><span className="tbc">{compare.tbc}</span></p>
      </div>
    </Section>
  );
}
