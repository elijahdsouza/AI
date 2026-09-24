// Writes src/assets/uc-magnet.json: the UC magnet as a Lottie, from the measured
// logo geometry in src/components/ucMark.ts.   node scripts/make-magnet.ts
//   frames   0-60   the outline draws on, the pole caps close, the field fades in
//   frames  60-180  seamless loop: field lines flow pole to pole and breathe
import { writeFileSync } from "node:fs";
import { MARK, OUTLINE, DOMES, POLES, LOTTIE, markBounds, makeTf, type Pt } from "../src/components/ucMark.ts";

const GOLD = [187 / 255, 171 / 255, 105 / 255, 1].map((v) => Math.round(v * 10000) / 10000);
const { centre } = markBounds();
const S = LOTTIE.scale;
const tf = makeTf(centre, LOTTIE.centre, S);
const rot = makeTf([0, 0], [0, 0], S); // vectors: rotate + scale, no move
const R = (n: number) => Math.round(n * 100) / 100;
const P = (p: Pt) => [R(p[0]), R(p[1])];

type Seg = (typeof OUTLINE)[number];
// Circle arcs become cubic Beziers, at most 90 degrees per piece.
function toBezier(segs: Seg[], closed: boolean) {
  const v: number[][] = [], i: number[][] = [], o: number[][] = [];
  const push = (pt: Pt, inT: Pt, outT: Pt) => {
    const last = v.length - 1;
    if (last >= 0 && Math.hypot(v[last][0] - pt[0], v[last][1] - pt[1]) < 0.01) { o[last] = P(outT); return; }
    v.push(P(pt)); i.push(P(inT)); o.push(P(outT));
  };
  for (const seg of segs) {
    if ("l" in seg) {
      push(tf(seg.l[0]), [0, 0], [0, 0]);
      push(tf(seg.l[1]), [0, 0], [0, 0]);
      continue;
    }
    const { c, r, a0, a1 } = seg.a;
    const n = Math.ceil(Math.abs(a1 - a0) / (Math.PI / 2) - 1e-9);
    const step = (a1 - a0) / n;
    const h = (4 / 3) * Math.tan(step / 4) * r;
    for (let k = 0; k < n; k++) {
      const a = a0 + step * k, b = a + step;
      const p0: Pt = [c[0] + r * Math.cos(a), c[1] + r * Math.sin(a)];
      const p1: Pt = [c[0] + r * Math.cos(b), c[1] + r * Math.sin(b)];
      const t0 = rot([-Math.sin(a) * h, Math.cos(a) * h]);
      const t1 = rot([Math.sin(b) * h, -Math.cos(b) * h]);
      push(tf(p0), [0, 0], t0);
      const last = v.length - 1; o[last] = P(t0);
      push(tf(p1), t1, [0, 0]);
    }
  }
  if (closed && v.length > 1) {
    const L = v.length - 1;
    if (Math.hypot(v[L][0] - v[0][0], v[L][1] - v[0][1]) < 0.01) { i[0] = i[L]; v.pop(); i.pop(); o.pop(); }
  }
  return { i, o, v, c: closed };
}

const sh = (nm: string, k: object) => ({ ty: "sh", nm, ks: { a: 0, k } });
const st = (nm: string, width: number, opacity: object, extra: object = {}) =>
  ({ ty: "st", nm, c: { a: 0, k: GOLD, sid: "markColor" }, o: opacity, w: { a: 0, k: width }, lc: 2, lj: 2, ml: 4, ...extra });
const tr = () => ({ ty: "tr", p: { a: 0, k: [0, 0] }, a: { a: 0, k: [0, 0] }, s: { a: 0, k: [100, 100] }, r: { a: 0, k: 0 }, o: { a: 0, k: 100 } });
const ease = (o: [number, number], i: [number, number]) => ({ o: { x: [o[0]], y: [o[1]] }, i: { x: [i[0]], y: [i[1]] } });
const kf = (t: number, s: number[], e?: ReturnType<typeof ease>) => ({ t, s, ...(e ?? {}) });
const trim = (from: number, to: number) => ({
  ty: "tm", nm: "Draw on", s: { a: 0, k: 0 }, o: { a: 0, k: 0 }, m: 1,
  e: { a: 1, k: [kf(from, [0], ease([0.65, 0], [0.2, 1])), kf(to, [100])] },
});
const layerBase = (ind: number, nm: string) => ({
  ddd: 0, ind, ty: 4, nm, sr: 1, ip: 0, op: 180, st: 0, bm: 0, ao: 0,
  ks: { o: { a: 0, k: 100 }, r: { a: 0, k: 0 }, p: { a: 0, k: [0, 0, 0] }, a: { a: 0, k: [0, 0, 0] }, s: { a: 0, k: [100, 100, 100] } },
});

const STROKE = R(MARK.stroke * S);

// The mark: the outline draws on like a pen, then the two domes close off the pole caps.
const mark = {
  ...layerBase(1, "Magnet"),
  shapes: [
    { ty: "gr", nm: "Outline", it: [sh("Outline", toBezier(OUTLINE, true)), trim(0, 48), st("Line", STROKE, { a: 0, k: 100 }), tr()] },
    {
      ty: "gr", nm: "Pole caps", it: [
        sh("Left cap", toBezier(DOMES[0], false)), sh("Right cap", toBezier(DOMES[1], false)),
        trim(30, 56),
        st("Line", STROKE, { a: 0, k: 100 }),
        tr(),
      ],
    },
  ],
};

// The field: dotted arcs from pole to pole beyond the tips, flowing on a seamless 2s loop.
const [A, B] = POLES;
const arcs = [150, 280, 410, 540].map((hgt, k) => {
  const spread = 70 * (k + 1);
  const pts: Pt[] = [A, [A[0] - spread, A[1] - hgt], [B[0] + spread, B[1] - hgt], B].map(tf);
  const [p0, c1, c2, p1] = pts;
  const k2 = { i: [[0, 0], [R(c2[0] - p1[0]), R(c2[1] - p1[1])]], o: [[R(c1[0] - p0[0]), R(c1[1] - p0[1])], [0, 0]], v: [P(p0), P(p1)], c: false };
  const alpha = [58, 44, 32, 22][k];
  return {
    ty: "gr", nm: `Field ${k + 1}`, it: [
      sh(`Arc ${k + 1}`, k2),
      st("Dots", R(STROKE * 0.26), { a: 0, k: alpha }, {
        d: [
          { n: "d", nm: "dash", v: { a: 0, k: 0.1 } },
          { n: "g", nm: "gap", v: { a: 0, k: 11.9 } },
          { n: "o", nm: "offset", v: { a: 1, k: [kf(60, [0]), kf(180, [-48])] } },
        ],
      }),
      tr(),
    ],
  };
});
const field = {
  ...layerBase(2, "Field"),
  ks: {
    ...layerBase(2, "Field").ks,
    o: { a: 1, k: [
      kf(36, [0], ease([0.3, 0], [0.2, 1])), kf(60, [100], ease([0.45, 0], [0.55, 1])),
      kf(120, [62], ease([0.45, 0], [0.55, 1])), kf(180, [100]),
    ] },
  },
  shapes: arcs,
};

const lottie = {
  v: "5.12.2", fr: 60, ip: 0, op: 180, w: LOTTIE.size, h: LOTTIE.size, nm: "UC magnet", ddd: 0,
  assets: [], layers: [mark, field],
  markers: [{ tm: 0, cm: "intro", dr: 60 }, { tm: 60, cm: "loop", dr: 120 }],
  slots: { markColor: { p: { a: 0, k: GOLD } } },
};

const out = new URL("../src/assets/uc-magnet.json", import.meta.url);
writeFileSync(out, JSON.stringify(lottie));
const all = [...mark.shapes.flatMap((g) => g.it), ...arcs.flatMap((g) => g.it)]
  .filter((s: { ty: string }) => s.ty === "sh").flatMap((s: any) => s.ks.k.v);
const xs = all.map((p: number[]) => p[0]), ys = all.map((p: number[]) => p[1]);
console.log(`wrote uc-magnet.json  bounds x ${Math.min(...xs).toFixed(0)}..${Math.max(...xs).toFixed(0)}  y ${Math.min(...ys).toFixed(0)}..${Math.max(...ys).toFixed(0)}  stroke ${STROKE}`);
