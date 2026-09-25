import { MotionConfig } from "motion/react";
import { Header, Hero, Stats, LogosTop, Problem, Callout, Alternatives } from "./sections/Top";
import { Peak } from "./sections/Peak";
import { ProGroup, Expect, Rhythm, LogosBottom, Pricing, Anchor, Compare } from "./sections/Middle";
import { How, Research, Proof, Standard, Story, Futures, Faq, Close, Footer } from "./sections/Bottom";
import { callouts } from "./content";

export default function App() {
  return (
    <MotionConfig reducedMotion="user">
      <a href="#main" className="sr-only focus:not-sr-only focus:fixed focus:top-3 focus:left-3 focus:z-[100] btn btn-sm">Skip to content</a>
      <Header />
      <main id="main">
        <Hero />
        <Stats />
        <LogosTop />
        <Problem />
        <Callout {...callouts.broken} />
        <Alternatives />
        <Callout {...callouts.turn} />
        <Peak />
        <Callout {...callouts.bridge} />
        <ProGroup />
        <Expect />
        <Rhythm />
        <LogosBottom />
        <Pricing />
        <Anchor />
        <Compare />
        <How />
        <Proof />
        <Research />
        <Story />
        <Standard />
        <Futures />
        <Faq />
        <Close />
      </main>
      <Footer />
    </MotionConfig>
  );
}
