// Every word on the page lives here, so copy changes never touch layout.
// *words* mark the gold accent in a heading (it can run over several words).
// Anything in [brackets] starting with TBC is a placeholder to fill later.

export const site = {
  // Paste your form tool’s link here (Tally, Typeform, Mailchimp...).
  waitlistUrl: "#waitlist-form-tbc",
  walkUrl: "#founders-walk-tbc",
  freeUrl: "#forever-free-tbc",
  // 11:59pm in Melbourne on 29 October, which is daylight saving time (UTC+11).
  deadlineISO: "2026-10-29T23:59:00+11:00",
  deadlineLabel: "29 October 2026, 11:59pm AEST",
  cta: "Join the waitlist",
  walk: "Come to the Founders Walk",
  email: "contact@uncommoncollectiveau.com",
};

export const nav = [
  { label: "The problem", href: "#problem" },
  { label: "The Pro Group", href: "#pro-group" },
  { label: "What to expect", href: "#expect" },
  { label: "The rhythm", href: "#rhythm" },
  { label: "Pricing", href: "#pricing" },
  { label: "Proof", href: "#proof" },
  { label: "FAQ", href: "#faq" },
];

export const hero = {
  eyebrow: "Meet Driven Melbourne Builders",
  stem: "Making it easier, and more common, to build",
  // Typed one after another. The first is what shows before anything moves.
  rotating: [
    "the life behind the business.",
    "real growth.",
    "with the right access.",
    "friendships that last.",
  ],
  sub: "The place between work, home and play — for founders, operators and creators, from small businesses to high-growth startups looking for more. Bringing together the people, access, systems and rhythms for undeniable momentum.",
  plans: "See the plans",
  free: { before: "Not ready to commit? Become a ", bold: "Forever Free", after: " member instead." },
  proof: "With 2,300+ driven founders, creators and leaders in tech and impact.",
  countdownLabel: "Founding rate closes",
  benefits: [
    { icon: "users", title: "Key connections" },
    { icon: "key", title: "Unlock opportunities" },
    { icon: "trending", title: "Build momentum" },
    { icon: "chart", title: "Gain growth" },
    { icon: "belong", title: "Migrant friendly, not migrant exclusive" },
  ],
};

export const statsTitle = "Across Uncommon Collective";

export const stats = [
  { value: 2300, suffix: "+", label: "driven founders, operators and creators" },
  { value: 1100, suffix: "+", label: "attendees and clients served" },
  { value: 60, suffix: "%+", label: "first-generation migrants engaged" },
  { value: 60, prefix: "$", suffix: "K+", label: "reinvested or subsidised" },
];

export const logosTop = {
  label: "From leading startup communities and coworking spaces, backed by investors, studios and ecosystem organisations",
  names: ["YGAP", "Stone & Chalk", "CSIRO", "Square Peg", "Hyper", "Antler", "Inspire9", "LaunchVic", "Startmate", "Blackbird"],
  tbc: "TBC · real logo files needed, these are wordmarks",
};

export const problem = {
  eyebrow: "You’re driven and getting results.",
  h2: "Your friends *cheer.* But they can’t *help*, *inspire*, or *call you higher.*",
  points: [
    { icon: "users", title: "You’ve outgrown your circle.", body: "The people who knew you at the start can’t follow where you’re going, and you’re not in the rooms where the next ones are." },
    { icon: "coins", title: "You’re burning time and money on things that don’t work.", body: "Programs, memberships and groups full of content and noise, and short on people worth knowing." },
    { icon: "chart", title: "Your confidence is leaking.", body: "Your ability hasn’t changed. You’re just building without the connections, opportunities and vehicles that make the next level reachable." },
    { icon: "flag", title: "You’re ready for a circle who gets it.", body: "A place you can keep climbing, with people building at your level who want you to get there." },
  ],
};

// The three gold callouts that sit across the seams between sections.
export const callouts = {
  broken: { text: "The *old way* of building *momentum without life experiences* is *broken.*" },
  turn: { text: "But it doesn’t have to *stay that way.*", sub: "Build momentum in a community that backs you beyond business success." },
  bridge: { text: "That’s why we created the *UC Pro Group.*" },
};

export const alternatives = {
  h2: "Effort got you here. The right network, real systems, and *rhythms that grow with you* get you further.",
  cards: [
    { icon: "calendar", title: "Programs and accelerators", body: "A plan with an end date. Momentum stops when the cohort does." },
    { icon: "user", title: "Coaches and consultants", body: "Expensive, rigid, and limited to one person’s view and network." },
    { icon: "megaphone", title: "Free groups and online communities", body: "Anyone can join, so the good people are hard to find." },
    { icon: "laptop", title: "Coworking", body: "Hit and miss when it comes to making real work friends. You sit near people, but nobody makes the introductions." },
  ],
};

export const belief = {
  eyebrow: "What we believe",
  statement: "Every *builder* builds better, goes further, and faster in community.",
  line2: "Building momentum and growth doesn’t need to be draining.",
  line3: "Growth is more fun with people who get you and inspire you.",
};

export const proGroup = {
  eyebrow: "A movement, not a membership",
  stem: "Build",
  rotating: ["real business friendships.", "systems that back you.", "undeniable momentum."],
  // What screen readers, link previews and no-JavaScript visitors get after "Build".
  still: "real business friendships, systems that back you, and undeniable momentum.",
  lede: "It picks up where programs and coworking spaces stop. We bring the right people together and help you build momentum, find your way and go further — without the anxiety, overwhelm and loneliness of doing it alone.",
  photoAlt: "Uncommon Collective members together outside a Melbourne community meetup",
  pillars: [
    { icon: "users", title: "Community and belonging", body: "Dinners, coworking and walks with people who become friends." },
    { icon: "trending", title: "Momentum and growth", body: "Done-for-you support and growth services that move the number." },
    { icon: "megaphone", title: "Visibility and media", body: "Podcast features, documented content and promo reels." },
    { icon: "key", title: "Access and opportunity", body: "Investor intros, grants and partner perks." },
    { icon: "coins", title: "Investment capital", body: "Investor introductions where there’s a fit, seed through Series A–C." },
  ],
  tiles: [
    { title: "It grows with you", body: "It changes as your business does, from service business to high-growth startup. There’s no 12-week end date." },
    { title: "Beyond coworking and programs", body: "The place between work, home and play — built around people you want to see again." },
    { title: "Real life, in person", body: "Dinners, coworking, walks and retreats that build you personally as well as professionally." },
    { title: "Migrant friendly, not migrant exclusive", body: "Everyone building something real is welcome at the table." },
  ],
};

export const expect = {
  eyebrow: "What you can expect",
  h2: "Experiences first. Then the *services* that do the heavy lifting.",
  lede: "Membership is a rhythm of real-life experiences, with growth services on member terms when you need them.",
  experiencesTitle: "Experiences",
  experiences: [
    { img: "dinner", title: "Member-only events", body: "Dinners and nights for members only." },
    { img: "podcast", title: "Podcast appearances", body: "2 to 3 features a year, from Momentum." },
    { img: "industry", title: "Industry events", body: "UC events at 20 to 60% off." },
    { img: "cowork", title: "Coworking", body: "Monthly coworking days, side by side." },
    { img: "speaking", title: "Speaking", body: "Speaking slots at partner events." },
    { img: "games", title: "Social events", body: "Games, drinks and the Founders Walk." },
  ],
  servicesTitle: "Growth *services*",
  memberDeal: "5–15% off, or $50–400 off, for members",
  services: [
    { img: "video", title: "Photo and video production" },
    { img: "grant", title: "Grant support and opportunity report" },
    { img: "marketing", title: "Marketing" },
    { img: "social", title: "Social media" },
    { img: "legal", title: "Legal" },
    { img: "coaching", title: "Coaching and consulting" },
  ],
  tools: {
    title: "Tools and perks",
    body: "Discounted and early access to the software, events and services you were buying anyway, in one place.",
    placeholder: "TBC · screenshot of the perks dashboard",
  },
};

export const rhythm = {
  eyebrow: "The rhythm",
  h2: "What a *month* inside looks like.",
  lede: "It repeats and compounds, and it doesn’t stop when a cohort does. Months vary by tier, and growth services sit on top.",
  cards: [
    { when: "Week one", icon: "sparkles", title: "Coworking day + AI ask-me-anything", body: "A full day side by side, then a build-together session. Ask anything about AI and leave with it working." },
    { when: "Week three", icon: "dice", title: "Coworking and games", body: "Games after the work is done, because nobody becomes friends across a boardroom table." },
    { when: "Week four", icon: "wine", title: "Drinks and dinner", body: "The long table. Two seats stay open because the room is still being built." },
    { when: "Week four or five", icon: "footprints", title: "The Founders Walk", body: "Nine kilometres, shoulder to shoulder, which is where the honest conversations happen." },
    { when: "Always on", icon: "key", title: "Early access and member pricing", body: "On the tools, events and services you were buying anyway." },
  ],
};

export const logosBottom = {
  label: "Partners, clients and collaborators",
  names: ["Square Peg", "LaunchVic", "Startmate", "HYPER", "Blackbird", "Catalysr", "YGAP", "ACU", "Study Melbourne", "Press Play", "Deakin", "Swinburne", "CSIRO", "Stone & Chalk", "Scape"],
};

export type Period = "monthly" | "quarterly" | "yearly";

export const pricing = {
  eyebrow: "Founding member pricing",
  h2: "Be part of the *community with early access* & lock in your *founding rate for 12 months.*",
  lede: "Our wider community is already 2,300+ strong. Paid membership is new: the first 50 founding members lock in these rates for 12 months, and shape the room everyone after them joins. Founding rates close 29 October 2026. Prices in AUD, including GST.",
  periods: [
    { id: "monthly" as Period, label: "Monthly" },
    { id: "quarterly" as Period, label: "Quarterly", note: "save 10%" },
    { id: "yearly" as Period, label: "Yearly", note: "save 20%" },
  ],
  periodNotes: {
    monthly: "Inner Circle and Ascend appear under quarterly and yearly billing.",
    quarterly: "Quarterly saves 10% versus paying monthly.",
    yearly: "Yearly saves 20% versus paying monthly, our best value.",
  } as Record<Period, string>,
  // One confident block straight under the pricing decision.
  assurances: [
    { icon: "gift", title: "First event free", body: "Come to one before you pay a cent." },
    { icon: "calendarCheck", title: "14-day trial", body: "Two weeks to see if the room is right for you." },
    { icon: "shield", title: "30-day money-back guarantee", body: "No lock-in contracts. Cancel or change tier anytime." },
    { icon: "handshake", title: "We’ll tell you if it’s not a fit", body: "Your first chat finds the right tier, or tells you honestly that none are right yet." },
  ],
  tiers: [
    {
      id: "free",
      name: "Forever Free",
      show: ["monthly"] as Period[],
      tagline: "Belong to the room without the ask.",
      intro: "Community from day one, no card required.",
      chip: "Community member from day one",
      listTitle: "Community membership essentials:",
      items: [
        "The fortnightly Uncommon founder newsletter",
        "Access to the community Slack channel",
        "Discounts on community events",
        "A chance to be featured in the newsletter",
        "3 to 4 partner perks and tools to start with",
      ],
    },
    {
      id: "insider",
      name: "Insider",
      show: ["monthly", "quarterly", "yearly"] as Period[],
      tagline: "Compound tiny savings into serious runway.",
      intro: "Get inside the room and start stacking the perks that pay for the membership many times over.",
      price: {
        monthly: { now: 19, was: 39, billed: "Billed monthly · $19/mo", chip: "Founding rate, save $20/mo vs regular" },
        quarterly: { now: 17, was: 35, billed: "Billed $51 every 3 months", chip: "Save $2/mo vs monthly · founding rate locked for 12 months" },
        yearly: { now: 15, was: 31, billed: "Billed $180 per year", chip: "Save $4/mo vs monthly · founding rate locked for 12 months" },
      },
      listTitle: "Everything in Forever Free, plus:",
      items: [
        "15 to 20 partner perks, tools and platforms",
        "Community support and free Founders Walks",
        "Free monthly drinks-night events",
        "Priority discounted growth services",
        "UC events at 20 to 60% off",
      ],
    },
    {
      id: "momentum",
      name: "Momentum",
      badge: "Most popular",
      dark: true,
      show: ["monthly", "quarterly", "yearly"] as Period[],
      tagline: "Keep moving, even when nothing else is working.",
      intro: "For founders actively building, the growth engine tier with real support behind every next step.",
      price: {
        monthly: { now: 49, was: 79, billed: "Billed monthly · $49/mo", chip: "Founding rate, save $30/mo vs regular" },
        quarterly: { now: 44, was: 71, billed: "Billed $132 every 3 months", chip: "Save $5/mo vs monthly · founding rate locked for 12 months" },
        yearly: { now: 39, was: 63, billed: "Billed $468 per year", chip: "Save $10/mo vs monthly · founding rate locked for 12 months" },
      },
      listTitle: "Everything in Insider, plus:",
      items: [
        "Monthly dinners, drinks and coworking days",
        "One free 45-minute 1:1 coaching session",
        "Grant opportunity analysis within a week",
        "AI automation and integration AMA group calls",
        "2 to 3 podcast features a year — personal brand, SEO, PR and credibility",
        "Done-for-you promo reel for $60 after your podcast",
      ],
    },
    {
      id: "inner",
      name: "Inner Circle",
      badge: "By application",
      show: ["quarterly", "yearly"] as Period[],
      tagline: "Open the doors most founders never get to knock on.",
      intro: "For scaling founders who want the rooms that move things: investors, retreats and warm intros.",
      bespoke: "Bespoke pricing. Higher-touch delivery and a smaller room, priced after a short fit call so it fits your stage.",
      guarantee: "30-day money-back guarantee",
      listTitle: "Everything in Momentum, plus:",
      items: [
        "Warm intros to APAC investors, 2-week turnaround",
        "Business retreats and member-only events",
        "Speaking opportunities at partner events",
        "A free personalised business coaching session",
        "Priority grant opportunity analysis",
      ],
    },
    {
      id: "ascend",
      name: "Ascend",
      badge: "By invitation",
      dark: true,
      show: ["quarterly", "yearly"] as Period[],
      tagline: "A full growth and automation partner, without hiring one.",
      intro: "Intensive strategy, automation and content support for founders scaling toward the next round.",
      qualify: { title: "To qualify, you meet at least two of:", items: ["$250K+ annual revenue", "2+ years trading", "3+ team members"] },
      bespoke: "By invitation only. A small number of seats, opened to founders we know we can move the needle for. We start with a short fit call.",
      guarantee: "30-day money-back guarantee",
      listTitle: "Everything in Inner Circle, plus:",
      items: [
        "4 hours of business strategy and go-to-market consulting a month, with email support",
        "Done-for-you AI workflow automation, built and managed for you — saves 10+ hours or $1K+ a month",
        "2 to 3 podcast features a year, plus 3 free post-podcast reels",
        "An article write-up",
        "2 Instagram, LinkedIn and TikTok carousels every 6 months",
      ],
    },
  ],
};

export const anchor = {
  prices: [
    { value: "$19", unit: "/month · Insider" },
    { value: "$49", unit: "/month · Momentum" },
  ],
  line: "Build your business for the price of a few meals a month.",
};

export const compare = {
  eyebrow: "There are alternatives, but",
  h2: "Here’s how we *stack up.*",
  lede: "We’re not the cheapest way to meet people. We’re the only option here that organises the room for you, with no end date and no equity.",
  columns: [
    { name: "UC Pro Group", sub: "From $15/mo founding rate" },
    { name: "Art of Mondays", sub: "WhatsApp groups, self-run" },
    { name: "Entrepreneurship Dinner Club", sub: "WhatsApp groups, self-run" },
    { name: "Startup accelerator", sub: "3 to 6% equity plus $20K to $60K" },
    { name: "Startup studio", sub: "15 to 40% equity, co-founder role" },
    { name: "Solo coach", sub: "$300 to $500 per hour" },
    { name: "Free Slack or Discord", sub: "Free" },
  ],
  // y = yes, p = partial, n = no, t = to be confirmed
  rows: [
    { q: "Keeps going after a program ends", cells: [["y", "Always on, no end date"], ["p", "Ongoing, run by attendees"], ["p", "Ongoing, run by attendees"], ["n", "Cohort-based, ends"], ["p", "Long term, but equity locked"], ["p", "While the engagement runs"], ["p", "Online only, low signal"]] },
    { q: "Growth services and grant help", cells: [["y", "From Momentum, grant analysis within a week"], ["n", "Not offered"], ["n", "Not offered"], ["p", "Mentor-matched, program limited"], ["p", "Studio partners"], ["y", "Yes, the whole offer"], ["n", "Do it yourself"]] },
    { q: "Visibility: podcast, newsletter, speaking", cells: [["y", "2 to 3 podcast features a year, newsletter features, speaking slots"], ["n", "Not offered"], ["n", "Not offered"], ["p", "Demo day only"], ["p", "Portfolio PR"], ["n", "Not typical"], ["n", "No"]] },
    { q: "Warm APAC investor introductions", cells: [["y", "Yes, in Inner Circle"], ["n", "Not offered"], ["n", "Not offered"], ["p", "Demo day only"], ["p", "Studio network"], ["p", "The coach’s network"], ["n", "Rare or cold"]] },
    { q: "In the room every month", cells: [["y", "UC organises monthly dinners and events"], ["p", "Attendees organise their own events"], ["p", "Attendees organise their own events"], ["p", "Program events only"], ["p", "Studio hosted"], ["n", "None"], ["n", "None"]] },
    { q: "Peers at your level", cells: [["y", "Peers we actually check"], ["p", "Open WhatsApp group"], ["p", "Open WhatsApp group"], ["p", "Cohort only"], ["p", "Portfolio only"], ["p", "One to one only"], ["n", "Noisy, nobody checks"]] },
    { q: "Cost per year", cells: [["y", "$180 to $588"], ["t", "TBC"], ["t", "TBC"], ["n", "Equity plus $20K to $60K"], ["n", "15 to 40% equity"], ["n", "$14K to $26K at 1 hour a month"], ["y", "$0"]] },
    { q: "Change your mind, risk free", cells: [["y", "14-day trial and money-back guarantee"], ["p", "Not applicable"], ["p", "Not applicable"], ["n", "No"], ["n", "No"], ["p", "Case by case"], ["p", "Not applicable"]] },
  ] as { q: string; cells: [string, string][] }[],
  tbc: "Pricing is draft · check the Art of Mondays and Dinner Club details before launch",
};

export const how = {
  eyebrow: "How it works",
  h2: "Ready to *stop guessing* and see *momentum?*",
  steps: [
    { title: "Join the founding waitlist", body: "It takes two minutes, and there’s no payment to put your hand up." },
    { title: "Book a 15-minute call", body: "Once there’s enough of us, we’ll invite you to a short call to find your tier." },
    { title: "Take a founding seat", body: "Your founding rate stays locked for 12 months." },
  ],
};

export const research = {
  eyebrow: "Why community is the unfair advantage",
  h2: "The most *successful founders* don’t build *alone.*",
  lede: "Behavioural research, and founders like Steven Bartlett, Daniel Priestley and Patrick Bet-David, point the same way.",
  // photo: drop a headshot named after this key into src/assets/photos/ to replace the initials.
  quotes: [
    { q: "I learnt very early in my life that you are who you surround yourself with.", who: "Steven Bartlett", role: "Founder, The Diary of a CEO", initials: "SB", photo: "bartlett" },
    { q: "Your work is always a product of your environment. You must become part of an environment that normalizes what you are trying to do.", who: "Daniel Priestley", role: "Author, Key Person of Influence", initials: "DP", photo: "priestley" },
    { q: "Your circle is a direct reflection of you. You attract who you relate to.", who: "Patrick Bet-David", role: "Founder, Valuetainment", initials: "PBD", photo: "betdavid" },
  ],
  stats: [
    { big: "76%", body: "of people who share weekly progress with an accountability partner achieve their goals, versus 43% who don’t." },
    { big: "65%", body: "higher chance of completing a goal when you commit to another person, rising to 95% with a scheduled check-in." },
    { big: "2×", body: "the survival rate for startups inside an accelerator or founder community, compared with those building alone." },
    { big: "75 yr", body: "Harvard’s longitudinal study found relationship quality, more than wealth, is the strongest predictor of a long, happy life." },
  ],
  tbc: "TBC · confirm sources and figures, and licensed headshots for the three quotes",
};

export const proof = {
  eyebrow: "In their words",
  h2: "The Pro Group is new. The *community around it is not.*",
  lede: "People from the wider Uncommon Collective community, most of whom have never paid us a cent. Names withheld at their request, with roles and results as stated.",
  quotes: [
    { q: "I came for the grant analysis and stayed for the people. UC found me a grant I didn’t know existed, and the coaching session helped me restructure my pricing in one afternoon.", role: "Founder, e-commerce · Melbourne", tag: "Free community member" },
    { q: "The podcast feature put my work in front of an audience I’d been chasing for a year, and the $60 promo reel out-performed everything I’d made myself.", role: "Content creator and podcaster · Melbourne", tag: "Free community member" },
    { q: "I’m not a founder, I run ops for one. The dinners and coworking days are where I’ve met every mentor I now lean on.", role: "Operations lead, SaaS scale-up · Melbourne", tag: "Free community member" },
    { q: "UC’s warm intros are the highest signal-to-noise deal flow I get. The founders arrive prepared, coached and backed by a real community.", role: "Angel investor, APAC early-stage", tag: "Community partner" },
  ],
  casesTitle: "What it’s *already done* for *people.*",
  cases: [
    { who: "Co-founder, AI tools startup", stats: [["$520K", "raised in pre-seed"], ["$18K", "monthly recurring revenue"], ["5→12", "team in 12 months"]], q: "The investor intros got us in front of the right people. Knowing I could lean on the community during the tough months kept me going." },
    { who: "Founder, SaaS for nonprofits", stats: [["3×", "annual revenue growth"], ["180+", "paying customers"], ["2", "partnerships from UC"]], q: "The podcast feature alone brought in 40 customers. The real win was the grant analysis — UC found us $50K we’d never have found on our own." },
    { who: "Founder, edtech platform", stats: [["250K", "monthly active users"], ["Series A", "investor-approved metrics"], ["2 yr", "in the community"]], q: "The rooms UC put me in changed what I thought was possible for this business, well before the numbers caught up." },
  ],
};

export const standard = {
  eyebrow: "Be honest with yourself",
  h2: "This isn’t for *everyone.*",
  lede: "We actually check, because the rooms only stay good if the right people are in them. The bar is simple: a business underway, revenue or traction, and somewhere you’re going.",
  forTitle: "In the room",
  forItems: [
    "Service businesses with real revenue and a small team",
    "Small businesses growing on purpose, not by accident",
    "High-growth tech, product and service startups",
    "Operators and creators building something of their own",
    "People who want the business and the life",
  ],
  notTitle: "Not in the room",
  notItems: [
    "Grifters, and anyone who justifies grifting",
    "Anyone who exploits people with sharky business practices",
    "Anyone not building something yet",
    "Anyone after a cheap desk",
    "Anyone who wants a program with an end date",
  ],
  notFoot: "Not you yet? Stay close as a Forever Free member, and come back at the right stage.",
};

export const story = {
  eyebrow: "My story",
  h2: "Why I started *UC.*",
  paras: [
    "I’ve spent my career in rooms that don’t usually meet: tech, community services, law and the startup scene.",
    "[TBC · one line about your own starting point]",
    "In every one of those rooms I saw the same thing. Capable people stalling because they didn’t have the right people around them. No one to call, no one opening doors, no one telling them honestly where they stood.",
    "The founders who break through rarely have more talent. They have a better room.",
    "UC Pro Group is that room: the community, access and systems I wish more founders had from day one, especially the ones building without an inherited network.",
  ],
  name: "Eli D’Souza",
  role: "Founder, Uncommon Collective",
  photo: "TBC · a candid photo of Eli at a UC dinner or Founders Walk, not a headshot",
};

export const futures = {
  eyebrow: "The cost of staying put",
  h2: "You didn’t come *this far* to be *average.*",
  sub: "Nothing changes if nothing changes. Six months from now, one of these will be true.",
  alone: { title: "Still building alone", items: ["Still pitching, and still not hearing why investors passed.", "A full week, and a business that feels about the same.", "The good intros going to people who already know people."] },
  room: { title: "Building with a room behind you", items: ["You know your numbers cold, and what investors think.", "Your month has a rhythm, and the business moved because of it.", "The intros come to you, because someone in the room made them."] },
  closeLead: "Surround yourself with the people and systems that bring you uncommon",
  closeWords: ["Momentum", "Growth", "Connections", "Community and lifelong friendships"],
};

export const faq = {
  eyebrow: "Before you decide",
  h2: "Everything else you might be *weighing up.*",
  items: [
    { q: "There are no members yet — why join now?", a: "Because that’s exactly what you’re buying. The Pro Group opens with its founding intake, and the first 50 people set the standard at the door, the rhythm of the month and the culture of the room. The wider Uncommon Collective community is 2,300+ people and six years old, so the room isn’t being built from nothing. If you’d rather join something finished, join later and pay the later rate." },
    { q: "Am I the right stage? I run a small business, not a startup.", a: "Yes. This isn’t a tech-only room. It’s for service businesses with real revenue and a small team, small businesses growing on purpose, high-growth startups, and operators and creators building something of their own. What matters is that something is underway." },
    { q: "How much time does it take?", a: "Realistically, one evening and one working day a month gets you most of the value. Everything is optional and nothing is graded. The people who get the most out of it show up in person." },
    { q: "What if I can’t make the events?", a: "The month repeats, so missing one isn’t missing your chance. If you can never make anything in person, this honestly isn’t the right spend for you." },
    { q: "How is this different from coworking or a program?", a: "Coworking gives you people in the room, not people in your corner. A program gives you a plan with an end date. We put the room together and keep it together, and it doesn’t stop when a cohort does." },
    { q: "What’s included in Forever Free?", a: "The fortnightly founder newsletter, the community Slack, discounts on community events, a chance to be featured, and a few partner perks to start with. No card required, and you can move up whenever you’re ready." },
    { q: "Can I cancel?", a: "Yes. There’s a 14-day trial, no lock-in contracts and a 30-day money-back guarantee. Cancel anytime, or move up or down a tier whenever your needs change." },
    { q: "What does the founding rate actually mean?", a: "The prices on this page are for the first 50 founding members and close on 29 October 2026, 11:59pm AEST. Join in that window and your rate stays locked for 12 months, even if prices rise." },
    { q: "What happens after I join the waitlist?", a: "Three steps. You join the founding waitlist. Once there’s enough of us, we invite you to a 15-minute call to find your tier. Then you take a founding seat, with your rate locked for 12 months." },
  ],
  still: "Still unsure? Email",
};

export const close = {
  eyebrow: "Uncommon and proud",
  h2: "Be part of the *movement.*",
  line1: "Your people are out there, and they’re looking for you too.",
  line2: "2,300+ founders, operators and creators are already in the community. The first 50 founding members lock their rate for 12 months.",
  seats: "50 founding seats · rate locked for 12 months · closes 29 October 2026",
};

export const footer = {
  org: "Uncommon Collective",
  place: "Melbourne, Australia",
  mission: "Making the uncommon common, for the founders, operators and leaders coming up next. Migrant friendly, not migrant exclusive. So the business works — and so does the life around it.",
  noteLead: "Not ready yet?",
  noteLink: "Join as a Forever Free member",
  noteBody: "The founder newsletter, the community Slack and event discounts. No card required.",
  links: ["LinkedIn", "Instagram", "Website"],
  legal: "© 2026 Uncommon Collective. A community-led social enterprise.",
};
