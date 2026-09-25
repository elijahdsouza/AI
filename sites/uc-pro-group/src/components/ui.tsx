import type { ReactNode } from "react";
import {
  Users, KeyRound, TrendingUp, ChartColumn, HeartHandshake, Coins, Flag, Calendar, CalendarCheck, User, Megaphone,
  Laptop, Sparkles, Dices, Wine, Footprints, ShieldCheck, Handshake, Gift,
  type LucideIcon,
} from "lucide-react";
import { site } from "../content";
import { In, Item } from "./effects";

const icons: Record<string, LucideIcon> = {
  users: Users, key: KeyRound, trending: TrendingUp, chart: ChartColumn, belong: HeartHandshake, coins: Coins,
  flag: Flag, calendar: Calendar, calendarCheck: CalendarCheck, user: User, megaphone: Megaphone, laptop: Laptop,
  sparkles: Sparkles, dice: Dices, wine: Wine, footprints: Footprints, shield: ShieldCheck, handshake: Handshake,
  gift: Gift,
};

/** White glyph on a gold disc, the one icon treatment used outside the hero. */
export function Disc({ name, className = "" }: { name: string; className?: string }) {
  const I = icons[name] ?? Sparkles;
  return (
    <span className={`disc ${className}`} aria-hidden="true">
      <I />
    </span>
  );
}

/** Renders *word* as the gold accent word. */
export function Accent({ text }: { text: string }) {
  const parts = text.split(/(\*[^*]+\*)/g);
  return (
    <>
      {parts.map((p, i) =>
        p.startsWith("*") && p.endsWith("*") ? (
          <em key={i} className="accent">{p.slice(1, -1)}</em>
        ) : (
          <span key={i}>{p}</span>
        ),
      )}
    </>
  );
}

/** Text that may contain a [TBC · ...] placeholder, shown as a dashed tag. */
export function Copy({ text, className = "body" }: { text: string; className?: string }) {
  const m = text.match(/^\[(TBC[^\]]*)\]$/);
  if (m) return <p className={className}><span className="tbc">{m[1]}</span></p>;
  return <p className={className}>{text}</p>;
}

/** Section heading. Its parts arrive in reading order, once, as the section comes into view. */
export function Head({
  eyebrow, title, lede, center = false, className = "",
}: { eyebrow?: string; title: string; lede?: string; center?: boolean; className?: string }) {
  return (
    <In className={`${center ? "head-center" : ""} ${className}`}>
      {eyebrow && <Item as="p" className="eyebrow">{eyebrow}</Item>}
      <Item as="h2" className="h2"><Accent text={title} /></Item>
      {lede && <Item as="p" className="lede">{lede}</Item>}
    </In>
  );
}

export function Section({
  id, ground, tight = false, className = "", children, style,
}: { id?: string; ground: string; tight?: boolean; className?: string; children: ReactNode; style?: React.CSSProperties }) {
  return (
    <section id={id} className={`g g-${ground} ${tight ? "sec-tight" : "sec"} ${className}`} style={style}>
      {children}
    </section>
  );
}

export function Cta({ className = "", small = false, label = site.cta }: { className?: string; small?: boolean; label?: string }) {
  const external = site.waitlistUrl.startsWith("http");
  return (
    <a
      className={`btn ${small ? "btn-sm" : ""} ${className}`}
      href={site.waitlistUrl}
      {...(external ? { target: "_blank", rel: "noopener" } : {})}
    >
      {label}
    </a>
  );
}

export function Photo({
  src, alt, className = "", children, label,
}: { src: string; alt: string; className?: string; children?: ReactNode; label?: string }) {
  return (
    <figure className={`photo m-0 ${className}`}>
      <span className="photo-fallback">{label ?? "photo"}</span>
      <img src={src} alt={alt} loading="lazy" decoding="async" />
      {children && (
        <>
          <span className="scrim" />
          <figcaption className="over">{children}</figcaption>
        </>
      )}
    </figure>
  );
}
