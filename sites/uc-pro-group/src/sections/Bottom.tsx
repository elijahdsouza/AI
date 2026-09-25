import { ChevronDown, Check, X } from "lucide-react";
import { Head, Section, Cta, Accent, Copy } from "../components/ui";
import { In, Item, useArrive, ArriveItem } from "../components/effects";
import { Logo } from "./Top";
import { DriftPhoto } from "./Middle";
import { img, localPhoto } from "../images";
import { site, how, research, proof, standard, story, futures, faq, close, footer } from "../content";

/** Steps read top to bottom beside the heading, numbered because the order matters here. */
export function How() {
  return (
    <Section id="how" ground="white">
      <div className="wrap grid lg:grid-cols-[1fr_1.15fr] gap-12 lg:gap-20 items-start">
        <div className="lg:sticky lg:top-28">
          <Head title={how.h2} />
          <In className="mt-10"><Item><Cta /></Item></In>
        </div>
        <In as="ol" className="list-none p-0 m-0 border-t b-line" stagger={0.08}>
          {how.steps.map((s, i) => (
            <Item as="li" key={s.title} className="grid grid-cols-[64px_1fr] md:grid-cols-[96px_1fr] gap-4 py-8 border-b b-line">
              <span className="serif font-bold text-[3.2rem] md:text-[4rem] leading-none text-[rgba(var(--gold-rgb),.85)]" aria-hidden="true">{i + 1}</span>
              <div>
                <h3 className="h3"><span className="sr-only">Step {i + 1}: </span>{s.title}</h3>
                <Copy text={s.body} />
              </div>
            </Item>
          ))}
        </In>
      </div>
    </Section>
  );
}

/** Initials in a gold ring, or a headshot if one is dropped into src/assets/photos/ under `photo`. */
function Avatar({ initials, photo, size }: { initials: string; photo: string; size: number }) {
  const src = localPhoto(photo);
  const box = { width: size, height: size };
  return src
    ? <img src={src} alt="" className="shrink-0 rounded-full object-cover border border-[rgba(var(--gold-rgb),.6)]" style={box} />
    : (
      <span aria-hidden="true" style={{ ...box, fontSize: size * (initials.length > 2 ? 0.3 : 0.36) }}
        className="shrink-0 grid place-items-center rounded-full border border-[rgba(var(--gold-rgb),.6)] bg-[rgba(var(--gold-rgb),.12)] serif font-bold c-gold tracking-[.02em]">
        {initials}
      </span>
    );
}

/** One quote leads; the other two sit beside it. The figures follow on a hairline. */
export function Research() {
  const [lead, ...rest] = research.quotes;
  return (
    <Section id="research" ground="black" className="grain">
      <div className="wrap">
        <Head center title={research.h2} lede={research.lede} />
        <In className="mt-14 grid lg:grid-cols-[1.35fr_1fr] gap-5" stagger={0.08}>
          <Item as="figure" className="card p-9 md:p-12 m-0 flex flex-col">
            <blockquote className="m-0 serif text-[clamp(1.6rem,2.6vw,2.2rem)] leading-[1.25]">“{lead.q}”</blockquote>
            <figcaption className="mt-auto pt-9 flex items-center gap-4 text-[13px]">
              <Avatar initials={lead.initials} photo={lead.photo} size={56} />
              <span><b className="font-semibold block text-[14px]">{lead.who}</b><span className="fg2">{lead.role}</span></span>
            </figcaption>
          </Item>
          <div className="grid gap-5">
            {rest.map((q) => (
              <Item as="figure" key={q.who} className="card p-8 m-0">
                <blockquote className="m-0 serif text-[1.12rem] leading-snug">“{q.q}”</blockquote>
                <figcaption className="pt-6 flex items-center gap-3.5 text-[13px]">
                  <Avatar initials={q.initials} photo={q.photo} size={44} />
                  <span><b className="font-semibold block">{q.who}</b><span className="fg2">{q.role}</span></span>
                </figcaption>
              </Item>
            ))}
          </div>
        </In>
        <In className="mt-14 grid grid-cols-2 lg:grid-cols-4 gap-x-6 gap-y-10 border-t b-line pt-12" stagger={0.06}>
          {research.stats.map((s) => (
            <Item key={s.big}>
              <p className="serif font-bold text-[2.6rem] leading-none c-gold">{s.big}</p>
              <p className="mt-3 text-[13px] leading-relaxed fg2">{s.body}</p>
            </Item>
          ))}
        </In>
        <p className="mt-10 text-center"><span className="tbc">{research.tbc}</span></p>
      </div>
    </Section>
  );
}

// On phones the rows below become swipe rails; from desktop up they're plain grids.
const rail = "flex lg:grid gap-4 overflow-x-auto lg:overflow-visible snap-x snap-mandatory no-scrollbar -mx-[var(--gutter)] px-[var(--gutter)] scroll-px-[var(--gutter)] lg:mx-0 lg:px-0";

/** Compact: the reviews arrive in one row from beyond the right edge, then the results do the same. */
export function Proof() {
  const { ref: quotesRef, progress: quotesIn } = useArrive<HTMLDivElement>();
  const { ref: casesRef, progress: casesIn } = useArrive<HTMLDivElement>();
  return (
    <section id="proof" className="g g-grey sec overflow-x-clip">
      <div className="wrap">
        <Head title={proof.h2} lede={proof.lede} className="max-w-[780px] [&_.h2]:text-[clamp(1.9rem,3.2vw,2.8rem)]" />
        <div ref={quotesRef} className={`mt-12 lg:grid-cols-4 ${rail}`}>
          {proof.quotes.map((q, i) => (
            <ArriveItem key={q.role} progress={quotesIn} i={i} n={proof.quotes.length} className="shrink-0 w-[80vw] sm:w-[46vw] lg:w-auto snap-start">
              <figure className="card p-6 m-0 h-full flex flex-col">
                <span className="block w-[22px] h-[2px] bg-gold" aria-hidden="true" />
                <blockquote className="m-0 mt-4 serif text-[1.04rem] leading-[1.5]">“{q.q}”</blockquote>
                <figcaption className="mt-auto pt-5">
                  <span className="block text-[12.5px] leading-snug fg2">{q.role}</span>
                  <span className="inline-block mt-3 mono text-[9.5px] tracking-[.12em] uppercase px-2.5 py-1 rounded-full border b-line">{q.tag}</span>
                </figcaption>
              </figure>
            </ArriveItem>
          ))}
        </div>

        <In className="mt-20"><Item as="h3" className="h2 !text-[clamp(1.6rem,2.6vw,2.2rem)]"><Accent text={proof.casesTitle} /></Item></In>
        <div ref={casesRef} className={`mt-8 lg:grid-cols-3 ${rail}`}>
          {proof.cases.map((c, i) => (
            <ArriveItem key={c.who} progress={casesIn} i={i} n={proof.cases.length} className="shrink-0 w-[84vw] sm:w-[60vw] lg:w-auto snap-start">
              <article className="card p-6 md:p-7 h-full flex flex-col">
                <p className="mono text-[10.5px] tracking-[.14em] uppercase fg2 m-0">{c.who}</p>
                <div className="mt-5 grid grid-cols-3 gap-3">
                  {c.stats.map(([v, l]) => (
                    <div key={l}><p className="serif font-bold text-[1.4rem] leading-none m-0 whitespace-nowrap">{v}</p><p className="mt-1.5 text-[11px] leading-snug fg2 m-0">{l}</p></div>
                  ))}
                </div>
                <p className="mt-auto pt-5 serif italic text-[.98rem] leading-relaxed m-0"><span className="block border-t b-line pt-5">“{c.q}”</span></p>
              </article>
            </ArriveItem>
          ))}
        </div>
      </div>
    </section>
  );
}

export function Standard() {
  return (
    <Section id="standard" ground="grey">
      <div className="wrap">
        <Head center title={standard.h2} lede={standard.lede} />
        <In className="mt-14 grid md:grid-cols-2 gap-5 max-w-[1040px] mx-auto" stagger={0.08}>
          <Item className="card p-8">
            <h3 className="h3">{standard.forTitle}</h3>
            <ul className="mt-5 space-y-3.5">{standard.forItems.map((i) => <li key={i} className="flex gap-3 text-[14.5px] leading-snug"><Check size={18} className="check" />{i}</li>)}</ul>
          </Item>
          <Item className="card p-8 flex flex-col">
            <h3 className="h3">{standard.notTitle}</h3>
            <ul className="mt-5 space-y-3.5">{standard.notItems.map((i) => <li key={i} className="flex gap-3 text-[14.5px] leading-snug fg2"><X size={18} className="shrink-0 mt-[3px] text-[#9a4a42]" />{i}</li>)}</ul>
            <p className="mt-auto pt-6 text-[13.5px] leading-snug"><a className="link" href={site.freeUrl}>{standard.notFoot}</a></p>
          </Item>
        </In>
      </div>
    </Section>
  );
}

/** Dark green with white text. Add ?story=gold to the address to compare the gold version. */
export function Story() {
  const gold = typeof window !== "undefined" && new URLSearchParams(window.location.search).get("story") === "gold";
  const white = { "--fg": "#fff", "--fg2": "rgba(255,255,255,.84)" } as React.CSSProperties;
  return (
    <Section id="story" ground={gold ? "gold" : "green"} style={gold ? undefined : white}>
      <div className="wrap grid md:grid-cols-[1fr_1.15fr] gap-10 md:gap-16 items-center">
        <In><Item className={`aspect-[4/5] rounded-[20px] border border-dashed grid place-items-center p-8 text-center ${gold ? "border-[rgba(22,20,15,.3)] bg-white/10" : "border-white/25 bg-white/[.04]"}`}>
          <span className="tbc">{story.photo}</span>
        </Item></In>
        <div>
          <Head title={story.h2} />
          <In className="mt-6 space-y-4" stagger={0.06}>
            {story.paras.map((p, i) => (
              <Item key={i}><Copy text={p} className={`m-0 text-[1rem] leading-[1.75] ${i === 3 ? "serif italic !text-[1.3rem] fg" : "fg2"}`} /></Item>
            ))}
            <Item as="p" className="!mt-8"><b className="font-semibold">{story.name}</b><br /><span className="text-[13px] fg2">{story.role}</span></Item>
          </In>
        </div>
      </div>
    </Section>
  );
}

/** Compact: the heading holds on the left while the two futures slide in from the right. */
export function Futures() {
  const { ref, progress } = useArrive<HTMLDivElement>();
  return (
    <Section id="futures" ground="blue" className="overflow-x-clip !py-[clamp(72px,8vw,112px)]">
      <div className="wrap grid lg:grid-cols-[minmax(280px,380px)_1fr] gap-10 lg:gap-14 items-center">
        <Head title={futures.h2} lede={futures.sub} className="[&_.h2]:text-[clamp(1.9rem,3vw,2.6rem)]" />
        <div ref={ref} className="grid sm:grid-cols-2 gap-4">
          <ArriveItem progress={progress} i={0} n={2}>
            <div className="rounded-[18px] p-6 md:p-7 h-full border border-white/15 bg-black/15">
              <h3 className="h3 !text-[1.12rem]">{futures.alone.title}</h3>
              <ul className="mt-4 space-y-2.5">{futures.alone.items.map((i) => <li key={i} className="text-[14px] leading-snug fg2">{i}</li>)}</ul>
            </div>
          </ArriveItem>
          <ArriveItem progress={progress} i={1} n={2}>
            <div className="rounded-[18px] p-6 md:p-7 h-full border border-[rgba(var(--gold-rgb),.95)] bg-white/10">
              <h3 className="h3 !text-[1.12rem]">{futures.room.title}</h3>
              <ul className="mt-4 space-y-2.5">{futures.room.items.map((i) => <li key={i} className="text-[14px] leading-snug">{i}</li>)}</ul>
            </div>
          </ArriveItem>
        </div>
      </div>
      <div className="wrap mt-12 lg:mt-14">
        <In className="pt-10 border-t b-line flex flex-col lg:flex-row items-center justify-between gap-7 text-center lg:text-left" stagger={0.07}>
          <Item as="p" className="serif text-[clamp(1.1rem,1.6vw,1.35rem)] leading-snug max-w-[680px] m-0">
            {futures.closeLead}:{" "}
            <span className="italic font-bold c-acc">{futures.closeWords.join(" · ")}</span>
          </Item>
          <Item className="shrink-0"><Cta /></Item>
        </In>
      </div>
    </Section>
  );
}

/** Administrative: short stagger, no ceremony. */
export function Faq() {
  return (
    <Section id="faq" ground="off">
      <div className="wrap max-w-[860px]">
        <Head center title={faq.h2} />
        <In className="mt-12 border-t b-line" stagger={0.03}>
          {faq.items.map((f, i) => (
            <Item key={f.q}>
              <details className="group border-b b-line" open={i === 0}>
                <summary className="flex items-center justify-between gap-6 py-6 serif font-bold text-[1.12rem]">
                  {f.q}
                  <ChevronDown size={20} aria-hidden="true" className="shrink-0 c-acc transition-transform duration-200 ease-[cubic-bezier(.23,1,.32,1)] group-open:rotate-180" />
                </summary>
                <div className="pb-6 -mt-1"><Copy text={f.a} className="body !text-[.98rem] max-w-[68ch] !mt-0" /></div>
              </details>
            </Item>
          ))}
        </In>
        <p className="mt-8 text-center text-[13px] fg2">{faq.still} <a className="link" href={`mailto:${site.email}`}>{site.email}</a></p>
      </div>
    </Section>
  );
}

/** The ending resolves and holds: one line, one action, the room at the table. */
export function Close() {
  return (
    <Section id="close" ground="black" className="grain overflow-hidden">
      <div className="wrap grid lg:grid-cols-[1.12fr_1fr] gap-10 lg:gap-14 items-center">
        <div>
          <Head title={close.h2} className="[&_.h2]:text-[clamp(2.4rem,5vw,4rem)]" />
          <In className="mt-6" stagger={0.08}>
            <Item as="p" className="serif italic text-[clamp(1.3rem,2.2vw,1.8rem)] c-gold m-0">{close.line1}</Item>
            <Item as="p" className="lede !mt-4 max-w-[46ch]">{close.line2}</Item>
            <Item className="mt-9 flex flex-wrap items-center gap-3">
              <Cta />
              <a className="btn btn-ghost" href={site.walkUrl}>{site.walk}</a>
            </Item>
            <Item as="p" className="mt-7 mono text-[11px] tracking-[.14em] uppercase fg2">{close.seats}</Item>
          </In>
        </div>
        <In><Item><DriftPhoto src={img("toast")} alt="Founders raising a toast at a long communal dinner table" className="aspect-[4/3]" /></Item></In>
      </div>
    </Section>
  );
}

export function Footer() {
  return (
    <footer className="g g-black border-t b-line">
      <div className="wrap pt-14">
        <p className="serif italic text-[clamp(1.1rem,1.8vw,1.4rem)] leading-snug max-w-[780px] c-bone m-0">{footer.mission}</p>
      </div>
      <div className="wrap pt-10 pb-14 grid md:grid-cols-3 gap-10 text-[13px]">
        <div>
          <Logo className="h-[34px]" /><span className="sr-only">{footer.org}</span>
          <p className="mt-3 fg2">{footer.place}<br /><a className="link fg2" href={`mailto:${site.email}`}>{site.email}</a></p>
        </div>
        <div>
          <p>{footer.noteLead} <a className="link c-gold" href={site.freeUrl}>{footer.noteLink}</a></p>
          <p className="mt-2 fg2">{footer.noteBody}</p>
          <p className="mt-4 flex gap-5">{footer.links.map((l) => <a key={l} className="link fg2" href="#">{l}</a>)}</p>
        </div>
        <p className="fg2 md:text-right">{footer.legal}</p>
      </div>
    </footer>
  );
}
