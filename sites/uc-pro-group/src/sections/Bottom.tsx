import { ChevronDown, Check, X } from "lucide-react";
import { Disc, Head, Section, Cta, Accent, Copy } from "../components/ui";
import { In, Item, useArrive, ArriveItem } from "../components/effects";
import { LogoMark } from "./Top";
import { DriftPhoto } from "./Middle";
import { img } from "../images";
import { site, risk, how, research, proof, standard, story, futures, faq, close, footer } from "../content";

/** Four promises as plain type on the blue, split by hairlines rather than boxed in cards. */
export function Risk() {
  return (
    <Section id="risk" ground="blue">
      <div className="wrap">
        <Head center title={risk.h2} />
        <In className="mt-14 grid sm:grid-cols-2 lg:grid-cols-4 gap-y-10" stagger={0.06}>
          {risk.points.map((p, i) => (
            <Item key={p.title} className={`sm:px-6 ${i > 0 ? "lg:border-l b-line" : ""} ${i % 2 === 1 ? "sm:border-l lg:border-l" : ""}`}>
              <Disc name={p.icon} />
              <h3 className="h3 mt-6 !text-[1.12rem]">{p.title}</h3>
              <p className="body !text-[.92rem]">{p.body}</p>
            </Item>
          ))}
        </In>
      </div>
    </Section>
  );
}

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
            <figcaption className="mt-auto pt-8 text-[13px]"><b className="font-semibold">{lead.who}</b><span className="fg2"> · {lead.role}</span></figcaption>
          </Item>
          <div className="grid gap-5">
            {rest.map((q) => (
              <Item as="figure" key={q.who} className="card p-8 m-0">
                <blockquote className="m-0 serif text-[1.12rem] leading-snug">“{q.q}”</blockquote>
                <figcaption className="pt-5 text-[13px]"><b className="font-semibold">{q.who}</b><span className="fg2"> · {q.role}</span></figcaption>
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

/** The reviews fly in from beyond the right edge beside the heading; the results read as rows. */
export function Proof() {
  const { ref, progress } = useArrive<HTMLDivElement>();
  return (
    <section id="proof" className="g g-white sec overflow-x-clip">
      <div className="wrap grid lg:grid-cols-[minmax(300px,400px)_1fr] gap-10 lg:gap-14 items-start">
        <div className="lg:sticky lg:top-28">
          <Head title={proof.h2} lede={proof.lede} className="[&_.h2]:text-[clamp(1.9rem,2.8vw,2.6rem)]" />
        </div>
        <div ref={ref} className="grid md:grid-cols-2 gap-5">
          {proof.quotes.map((q, i) => (
            <ArriveItem key={q.role} progress={progress} i={i} n={proof.quotes.length}>
              <figure className="card p-8 m-0 h-full flex flex-col">
                <span className="block w-[22px] h-[2px] bg-gold" aria-hidden="true" />
                <blockquote className="m-0 mt-5 serif text-[1.2rem] leading-[1.45]">“{q.q}”</blockquote>
                <figcaption className="mt-auto pt-6 flex flex-wrap items-center justify-between gap-3">
                  <span className="text-[13px] fg2">{q.role}</span>
                  <span className="mono text-[10px] tracking-[.12em] uppercase px-3 py-1.5 rounded-full border b-line whitespace-nowrap">{q.tag}</span>
                </figcaption>
              </figure>
            </ArriveItem>
          ))}
        </div>
      </div>

      <div className="wrap mt-24">
        <In><Item as="h3" className="h2 text-center !text-[clamp(1.7rem,3vw,2.4rem)]"><Accent text={proof.casesTitle} /></Item></In>
        <In className="mt-10 border-t b-line" stagger={0.08}>
          {proof.cases.map((c) => (
            <Item as="article" key={c.who} className="grid lg:grid-cols-[220px_1.1fr_1fr] gap-6 lg:gap-10 py-9 border-b b-line items-start">
              <p className="mono text-[11px] tracking-[.14em] uppercase fg2 m-0 pt-1">{c.who}</p>
              <div className="grid grid-cols-3 gap-4">
                {c.stats.map(([v, l]) => (
                  <div key={l}><p className="serif font-bold text-[1.7rem] leading-none m-0">{v}</p><p className="mt-2 text-[11.5px] leading-snug fg2">{l}</p></div>
                ))}
              </div>
              <p className="serif italic text-[1.08rem] leading-relaxed m-0">“{c.q}”</p>
            </Item>
          ))}
        </In>
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
          <Item className="card p-8">
            <h3 className="h3">{standard.notTitle}</h3>
            <ul className="mt-5 space-y-3.5">{standard.notItems.map((i) => <li key={i} className="flex gap-3 text-[14.5px] leading-snug fg2"><X size={18} className="shrink-0 mt-[3px] text-[#9a4a42]" />{i}</li>)}</ul>
          </Item>
        </In>
      </div>
    </Section>
  );
}

/** Gold by default. Add ?story=green to the address to compare the green version. */
export function Story() {
  const green = typeof window !== "undefined" && new URLSearchParams(window.location.search).get("story") === "green";
  return (
    <Section id="story" ground={green ? "green" : "gold"}>
      <div className="wrap grid md:grid-cols-[1fr_1.15fr] gap-10 md:gap-16 items-center">
        <In><Item className="aspect-[4/5] rounded-[20px] border border-dashed border-[rgba(22,20,15,.3)] bg-white/10 grid place-items-center p-8 text-center">
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

export function Futures() {
  return (
    <Section id="futures" ground="blue">
      <div className="wrap">
        <Head center title={futures.h2} lede={futures.sub} />
        <In className="mt-14 grid md:grid-cols-2 gap-5 max-w-[1040px] mx-auto" stagger={0.12}>
          <Item className="rounded-[20px] p-8 border border-white/15 bg-black/15">
            <h3 className="h3">{futures.alone.title}</h3>
            <ul className="mt-5 space-y-3">{futures.alone.items.map((i) => <li key={i} className="text-[14.5px] leading-snug fg2">{i}</li>)}</ul>
          </Item>
          <Item className="rounded-[20px] p-8 border border-[rgba(var(--gold-rgb),.95)] bg-white/10">
            <h3 className="h3">{futures.room.title}</h3>
            <ul className="mt-5 space-y-3">{futures.room.items.map((i) => <li key={i} className="text-[14.5px] leading-snug">{i}</li>)}</ul>
          </Item>
        </In>
        <In className="mt-16 text-center" stagger={0.07}>
          <Item as="p" className="serif text-[clamp(1.25rem,2vw,1.6rem)] max-w-[720px] mx-auto leading-snug">{futures.closeLead}:</Item>
          <Item as="p" className="mt-5 flex flex-wrap justify-center gap-x-3 gap-y-2 serif font-bold italic c-acc text-[clamp(1.3rem,2.4vw,2rem)]">
            {futures.closeWords.map((w, i) => <span key={w}>{w}{i < futures.closeWords.length - 1 && <span aria-hidden="true" className="text-white/40 not-italic font-normal"> · </span>}</span>)}
          </Item>
          <Item className="mt-10"><Cta /></Item>
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
      <div className="wrap grid lg:grid-cols-[1fr_1.1fr] gap-10 lg:gap-16 items-center">
        <div>
          <Head title={close.h2} className="[&_.h2]:text-[clamp(2.4rem,5vw,4rem)]" />
          <In className="mt-6" stagger={0.08}>
            <Item as="p" className="serif italic text-[clamp(1.3rem,2.2vw,1.8rem)] c-gold m-0">{close.line1}</Item>
            <Item as="p" className="lede !mt-4 max-w-[46ch]">{close.line2}</Item>
            <Item className="mt-9 flex flex-wrap items-center gap-x-7 gap-y-4">
              <Cta />
              <a className="link" href={site.dinnerUrl}>{close.dinner}</a>
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
      <div className="wrap py-14 grid md:grid-cols-3 gap-10 text-[13px]">
        <div>
          <div className="flex items-center gap-3"><LogoMark size={26} /><b className="font-semibold">{footer.org}</b></div>
          <p className="mt-3 fg2">{footer.place}<br /><a className="link fg2" href={`mailto:${site.email}`}>{site.email}</a></p>
        </div>
        <div>
          <p>{footer.noteLead} <a className="link c-gold" href={site.waitlistUrl}>{footer.noteLink}</a></p>
          <p className="mt-2 fg2">{footer.noteBody}</p>
          <p className="mt-4 flex gap-5">{footer.links.map((l) => <a key={l} className="link fg2" href="#">{l}</a>)}</p>
        </div>
        <p className="fg2 md:text-right">{footer.legal}</p>
      </div>
    </footer>
  );
}
