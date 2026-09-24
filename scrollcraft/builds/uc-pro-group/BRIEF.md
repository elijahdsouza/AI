# UC Pro Group — BRIEF

**Status:** interviewed. **Superseded in part, see "Direction change" below.** Answers below are the user's, from the AskUserQuestion
round and their follow-up message. Authored decisions are labelled as such.

**Source of truth for messaging:** the signed-off narrative handover v1.0
(*UC Pro Group: narrative framework & page flow*). Where this brief and the
narrative doc disagree, the narrative doc wins.

---

## The eight topics

### 1. Vibe, and references

Editorial. Subtle and bold together, vertical and horizontal. "$10k website."

References given:
- **House of Stewards** (Instagram) — real photograph, large high-contrast
  serif set over it, italic on the emphasis, a conversational first-person
  quote as the headline. *This is the closest reference to the hero we are
  building.*
- The user's own **Uncommon Collective Partner Overview** 2-pager: bone and
  near-black split panels, olive-mustard display serif, geometric sans body,
  black pill buttons, indigo pill CTAs.
- Two further Instagram accounts supplied as links. **Not seen** — Instagram is
  blocked by this environment's egress proxy. Screenshots requested.

### 2. The scroll journey, section by section

Taken from the narrative doc's fifteen sections, which the user has already
signed off, compressed into nine chapters. See the map below.

### 3. The energy curve

Not stated explicitly. **Authored:** quiet open, tightening through the problem,
release at the third space, steady and concrete through the month and the
standard, firm at the decision, quiet at the close. Loud the whole way is as
flat as quiet the whole way.

### 4. Feeling, stage by stage, and the ONE moment

See *The feeling curve* below. The peak is chapter 03.

### 5. One thing no other site does

**Authored, from the brand's own metaphor.** The narrative spine is "The Table".
So: the page seats you at it while you read. See *Signature move*.

### 6. How far from premium-minimal

**Editorial**, explicitly. Not premium-minimal, not brutalist, not maximalist.

### 7. One unbroken world, or distinct scenes?

**Distinct scenes.** Chapters that cut hard. The user chose chaptered editorial
(A) and split stage (B), both of which are cut-based; neither is a world.

### 8. What assets already exist

- **One genuinely authentic photograph:** a group of ~17 founders outside a
  Melbourne café, diverse, warm, unposed enough to be true. 1750×558.
  This is the only real image and it is strong.
- Five stock photographs on the current page (laptop on a desk, an empty
  conference hall, two coworking scenes). **Cut.** They are the "could sit on a
  coach's page" failure the narrative doc warns against.
- Two white-on-transparent logo PNGs.
- The partner 2-pager, which supplies the real palette, type and partner logos.
- Everything else is generated as minimal outlined / dotted illustration, per
  the user's explicit direction: *"images that weren't necessarily
  photorealistic... minimalistic, outlined dotted illustrations and minor
  abstract artifacts... educational and social environments."*

---

## The tell-someone sentence

> It's the site where **you watch the table fill up as you read, and by the end
> there are two seats left.**

An experience, not a device name.

---

## The feeling curve

Written before the acts. One line per chapter: the emotion, then what on screen
causes it.

| Ch | Feeling | What causes it |
|---|---|---|
| 00 | **Recognised** | The founder's own sentence, set large, next to a photograph of a real room. They see themselves before they see an offer. |
| 01 | **Seen** | Calibre strip, then three pressures named in second person with no hedging. |
| 02 | **Named** | The four alternatives fail one by one. The spread splits and the two halves disagree. Deliberately quieter than 03. |
| 03 | **Lift — THE PEAK** | The third space. The gutter travels to the edge and the photograph takes the whole spread. The room they have been reading about arrives at full size. |
| 04 | **Reassured** | A real month, travelling sideways. Frequency is the proof when testimonials do not exist yet. |
| 05 | **Respected** | Who we're for, who we're not. The split returns, but now it reads as a door rather than a wound. |
| 06 | **Resolved** | Pricing, the founding offer, and all three risk reversals stated together. |
| 07 | **Answered** | FAQ, led by "there are no members yet, why join now". |
| 08 | **Committed** | Mission quietly. CTA as a line of running text, not a button island. |

No two adjacent chapters carry the same feeling. Chapter 02 is authored quiet so
that 03 has somewhere to go.

### The peak, as a sentence a visitor would say

> "There's a bit where the page splits apart and this photo of all these people
> just takes over the whole screen, and you realise that's the room."

Chapter 03. It gets the largest span on the page by a visible margin, the asset
budget, and the silence before it.

### Authored silence

Chapter 02 ends on roughly half a viewport of empty bone with only the gutter
rule and one line. **This is deliberate, not dead scroll.** It is the intake of
breath before the peak. The verification pass must not flag it as a defect.

---

## Grammar: "The Spread"

A new grammar, authored for this build. Permitted under uniqueness.md §2
("a new grammar is allowed when its navigation, sequence, ending, and explicit
bans describe a different structure"). It is **not** a blend of chaptered
editorial and split stage; it takes the folio's chrome and chapter units and
makes the split the page's recurring internal device, with its own bans.

- **Unit** — the chapter, and each chapter is a *spread*: left page, right page,
  a gutter between.
- **Nav** — no fixed bar. A rotated folio in the left margin, 11px mono, chapter
  number and title, updating as chapters pass. The gutter rule is the second
  piece of chrome. Both clickable.
- **Hero** — a split spread. Left page: the founder's sentence in the display
  serif, italic on the turn. Right page: the real photograph, ungraded, bleeding
  to the right edge.
- **Sequence** — chapters cut hard, no crossfade drift. Two chapters travel
  horizontally; the rest are vertical spreads.
- **Close** — a colophon plate, small type, CTA as running text.

### Bans

- No media *behind* type. Media owns its own page of the spread. (This is the
  rule that fixes the current page's worst defect.)
- No card grids.
- No centred hero copy.
- No pinned crossfade type acts.
- No magnetic CTA.
- No continuous drift gradient.
- No "scroll" cue, arrow or mouse icon.
- No eyebrow above every section heading.
- No em dash anywhere visible.
- No full-bleed video hero.

---

## Signature move — "The Table Fills"

A thin rule runs down the gutter for the whole page. It is the table's edge.

Every chapter the visitor passes **seats one more person at it**: a small
outlined seat mark stamps onto the rule and stays there. The marks accumulate,
so by the founding-offer chapter the gutter is a table with a room around it.
It doubles as navigation, because each seat is a link back to its chapter.

By the test in uniqueness.md §3: it is not a recoloured spotlight or a retuned
tilt. It accumulates state, it is tied to the brand's central metaphor, and it
is real navigation. Coded in the page off `--sc-p`; the engine is untouched.

Two seats stay empty at the end, which is the founding offer stated as geometry
rather than as a sentence.

---

## Score

| Ch | Beat | Device | Why this one |
|---|---|---|---|
| 00 | Recognition | `flow` + `in`, split spread | A hard-cut title spread. The photograph is a page, not a backdrop. |
| 01 | Problem | `reveal` per pointer | A wipe per pressure reads as three separate recognitions, not a list. |
| 02 | Alternatives fail | `pin`, divider driven from `--sc-p` | The frame holds while the two halves argue. The only pin before the peak. |
| 03 | **The third space** | `reveal` + gutter travel, **PEAK** | A change of state is what this beat is, and the gutter opening *is* the change. |
| 04 | A month | `pan` | Lateral travel reads as cadence. Vertical would read as an argument. |
| 05 | The standard | `flow`, split spread | Returns to the page's own rhythm, which is what makes it read as a door. |
| 06 | The decision | `flow` + `count` (real figures only) | Quiet and legible. Nothing clever at the moment of the ask. |
| 07 | FAQ | `flow` + `in` | It is a document here, deliberately. |
| 08 | Close | `pin`, short span | Holds and resolves. No fade to footer. |

Checks: five device families, none twice in a row, zero `scrub` acts (no ffmpeg
in this container, and the grammar bans video anyway), one peak with the largest
span, act count and length outside the 6–7 acts at 13.6–13.8vh band.

---

## Narrative section map

All fifteen sections of the signed-off doc land somewhere.

| Ch | Narrative sections |
|---|---|
| 00 | §1 Hero |
| 01 | §2 Credibility strip · §3 The problem, in their words |
| 02 | §4 Why the alternatives fail |
| 03 | §5 The third space |
| 04 | §6 What a month looks like · §7 The four pillars |
| 05 | §8 Who we're for. Who we're not. |
| 06 | §9 Pricing · §10 Growth services · §11 Founding offer · §12 Risk reversal |
| 07 | §13 FAQ |
| 08 | §14 Mission · §15 Final CTA and footer |

---

## Brand system

Read off the partner 2-pager. To be replaced by the user's swatch list.

| Role | Value |
|---|---|
| Accent, primary | olive-mustard `#8A7328` |
| Ink / dark ground | near-black `#1A1A1A` |
| Canvas | bone `#F2F0EA` |
| Surface | page grey `#E9E9E9` |
| CTA only | indigo `#3B48A8` |

Gold owns the editorial voice: headings, rules, the folio. Indigo owns exactly
one role, the primary CTA, and appears nowhere else. Two accents on a conversion
page split attention unless one is scoped to a single job.

**Mission, official wording:** "To cultivate, equip, and empower the next
generation of founders, operators, and creators to build momentum and growth
beyond programs, while levelling the playing field for migrants."

---

## Asset style preamble

Reused **verbatim** in every generation prompt. Paraphrasing it is what makes a
set look like eight prompts instead of one hand.

> Minimal editorial line illustration. Single consistent hairline stroke weight,
> no fills except fine dot-stipple shading. Monochrome olive-mustard (#8A7328)
> line work on a deep near-black (#1A1A1A) ground. Flat and orthographic,
> generous negative space, composition reads clearly at small size. Restrained,
> engineered, editorial, architectural drawing sensibility. NOT photorealistic,
> NOT 3D render, NOT clay, NOT watercolour, no gradients, no glow, no drop
> shadows, no lettering, no text, no numbers, no watermark, no signature.

Generated through Higgsfield. `api.kie.ai` is refused by this environment's
egress policy, so the skill's own kie.mjs pipeline is unavailable here.

---

## Known limits

- **No ffmpeg** in this container, so no video acts. The grammar bans them, so
  nothing is lost, but it is a real constraint and not a preference.
- **No real phone.** Headless Chrome cannot reproduce an iPhone's decoder,
  autoplay policy or touch scrolling. There is no video on this page, which
  removes the usual failure mode, but a device test has not been done.
- **Instagram references unseen.** Two of the three supplied references could
  not be opened from this container.

## Open, blocking final copy

1. Exact pricing, billing period, and the post-founding rate the lock-in is
   measured against.
2. The intake date, so the countdown counts to something true.
3. Whether the waitlist threshold is stated publicly or held internally.
4. Entry criteria wording now that small businesses are explicitly in scope.
5. Stats wording. The current page claims "2,300+ members already"; the partner
   deck says "2,000+ community members". The deck's numbers and labels are used
   here, framed as the wider Uncommon Collective community and kept visibly
   distinct from Pro Group membership, because chapter 07 opens by admitting
   there are no members yet.


---

# Direction change · v3

The "Spread" grammar in this brief was built, reviewed and **rejected**: it read
as a book. The archived build is `archive/spread-v1.html`. Two further things in
this brief are now factually wrong and are corrected here.

## What replaced it

**Media company crossed with a startup community page.** Heading at the top, full
width. Sticky bar with nav and one CTA. No folio, no chapters, no gutter rule.

**Three grounds, and the rule is not alternation for its own sake:**

| Ground | Value | Carries |
|---|---|---|
| Dark | `#0E0D0B` | Hero, the third space, the standard, the close. Where they feel. |
| Light | `#F2F0EA` | Problem, pillars, proof, comparison, pricing, FAQ. Where they read and compare. |
| Gold | `#7A6522` | The founding offer, and the two callout cards. The moment of commitment, rationed. |

**On the gold.** The raw brand gold `#8A7328` cannot carry body text on any
ground: it is mid-luminance, so it measures 3.78 against near-black and 3.86
against bone, both under the 4.5 floor. As a *ground* it was first lifted to
`#A98B33` with dark ink, then deepened to `#7A6522` so that **white** clears at
5.64, which is what was asked for. The brand gold survives untouched wherever it
is an accent rather than a text ground.

Two further two-stop tokens exist for the same reason:
`--acc` is display weight (3:1 is enough), `--acc-text` is body weight. On light,
`--acc-text` is `#6F5C1F`, because the brand gold at 10px measures 4.04.

## The hero graphic

The avatar-style figure glyph was rejected as amateur. It is replaced by a **3D
node lattice**: points in real 3D, rotated by the pointer, perspective projected,
edges between near neighbours with depth falloff, and pulses travelling the
lattice. Two modes: over the photograph, or on the bare ground.

## Correction: proof

This brief said **"With no testimonials yet, frequency is the proof."** That was
wrong. Testimonials and case studies exist, from free community members and
clients. They are used **anonymised at the user's instruction**: role and market
only, figures as stated, free-member status labelled on its face.

The "no members yet" honesty is retained where it is still true, and only there:
there are no *paid Pro Group* members, which is what the FAQ's opening entry
answers.

## Correction: section count

All fifteen narrative sections are built, plus the v19 comparison table and the
new proof section. The section inventory is in the commit message for this build.

## Conversion rules now honoured

From the messaging handover, Part One:

1. One primary CTA label everywhere: `Join the founding waitlist`.
2. One transitional CTA: `Come to the next dinner`.
3. Proof adjacency: no CTA sits more than one screen from a number or a name.
4. Specificity over adjectives.
5. Scarcity is real: 50 seats, a true countdown to 3 October 2026.
6. **Sticky CTA in the mobile thumb zone**, appearing only once the hero's own
   CTAs have left the screen so the page never shows two live copies of the
   same button.

## Still unconfirmed

Pricing is drafted from v19 ($49 Momentum, $159 Inner Circle) and is labelled
"draft pricing, not confirmed" on the page itself. Seats taken (13) is a
placeholder. The intake date 3 October 2026 comes from v19 and drives a live
countdown; the narrative doc says late October, so these disagree and the page
currently follows v19.

---

# Direction change · v4 (React build, shipped)

**Status:** interviewed across several rounds. The React build in
`sites/uc-pro-group` replaces the v3 HTML page as the live candidate. Messaging
is the user's section-by-section copy (hero, "What we believe", Two futures,
close) as approved in conversation. Quotes below are the user's words; anything
not quoted is an authored decision.

## What the user asked for, in their words

- "I want to avoid ai native slop.."
- "Because I want to design a website that has both subtle entrance animations and immersive experiences"
- "Obviously only where it makes sense and don't overuse it as I also don't want to use too many credits unnecessarily"
- "Yes the website needs to look expensive and fit for wealthy people to buy from"
- Hero eyebrow: "Meet entrepreneurs in your city". Every button gold, every label "Join the waitlist".
- Board notes (paraphrased from the marked-up screenshots): magnetic U lattice in the hero that reads as the logo; logos scroll infinitely; stats count up; problem, alternatives and testimonials come in sideways from off the page; the "old way" callout overlaps two sections; one gold, `#BBAB69`, with dark text on it.

## Grammar

**Editorial landing (media × community).** Sticky translucent bar with anchor nav
and one CTA. Sections cut on distinct grounds (black, white, grey, gold, green,
blue), each ground doing one job. Flow + one quiet entrance is the resting state;
immersive devices are rationed to five places.

## Feeling curve

| Act | Feeling | What causes it |
|---|---|---|
| Hero | **Invited** | "Meet entrepreneurs in your city", real faces, the gold magnet pulling particles into the logo's U |
| Stats, logos | **Reassured** | Real figures counting up once, partner names drifting past |
| Problem (pan) | **Seen** | Four pressures arrive one at a time while the frame holds still |
| Callout, alternatives | **Named, then turned** | "The old way... is broken"; the options fly in and fall short; the gold card says it doesn't need to stay that way |
| **What we believe (PEAK)** | **Lift, belonging** | The belief lights up word by word, the stage empties, then a gold U opens onto the real room |
| Pro Group, what to expect | **Clear** | Quiet flow straight after the peak: what it is, what you get |
| A month (pan) | **Assured** | A real month travels sideways; frequency as proof |
| Pricing, anchor, compare | **Respected** | A clean ladder, the value anchor, an honest comparison |
| Risk, how it works | **Safe** | No gamble, three steps |
| Research, proof, standard | **Convinced, selected** | Evidence, testimonials flying in, "This isn't for everyone" |
| Story, two futures | **Moved** | The founder's why; "You didn't come this far to be average." |
| FAQ, close | **Committed** | Answers, then "Your dream business could start here." |

## The peak

"The line about not building alone lit up word by word, and then the gold U from
the logo opened like a window into a room full of real founders." Lives in
**What we believe**, 360vh, the largest span on the page (the next largest, the
month pan, measures 310vh at 1440 wide; the problem pan 256vh).

**Tell-someone sentence:** It's the site where the sentence about not building
alone lights up, and then a gold magnet opens into a room full of real founders.

**Authored silence:** peak progress 0.45 to 0.54. The words clear to an empty
black stage before the room begins. Deliberate; not dead scroll.

## Score

| Section | Device |
|---|---|
| Hero | `pointer` (magnet canvas) + `drift` (three planes) + `in` |
| Stats | `count` |
| Logos (twice) | `marquee`, paused by the ambient pause control |
| Problem | `pan`, pinned |
| Callout | overlap across the seam + `in` |
| Alternatives | `arrival`, scrubbed from past the right edge, no pin |
| What we believe | `pin`: scrubbed words, silence, U mask reveal (**PEAK**, signature move) |
| Pro Group, Expect, Anchor, Compare, Risk, How, Research, Standard, Story, Futures, FAQ | `flow` + `in` (resting state) |
| A month | `pan`, pinned |
| Pricing | `drift` photo + layout toggle |
| Proof | `arrival` |
| Close | `drift` photo + `in` |

Nine families; no immersive device twice in a row; no video scrubs.

## Kept bans

No looping attention motion (no pulse, no bounce, no scroll cue), no section
counters, eyebrows on five of 23 sections only (city, belief, product, pricing, comparison), hover only on fine pointers,
no em dashes in visible copy, gold never carries text on light grounds,
testimonials without star ratings. Reduced motion keeps fades and drops
movement; the pinned sections become ordinary sections.

## Verification

Desktop 1440×900 (27,991px), 390×844 (35,460px), reduced motion (22,727px):
no horizontal overflow, no page errors. Peak checked at nine progress points on
desktop and phone. Contrast measured on the render. **Not covered:** a real
phone, and the 15 Higgsfield photos, whose CDN this environment cannot reach
(they show as dark placeholders in the screenshots and load in a normal browser).
