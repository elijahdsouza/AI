/*
  The Uncommon Collective magnet mark as geometry, measured from the logo
  artwork (89% pixel overlap with the original at its native size).

  Drawn upright, arms up, in "logo units", then turned 46.75° clockwise, which
  is how the logo sits. It is one closed outline around the magnet plus a dome
  across each arm, which marks off the two pole caps.

  Used by the hero's Lottie magnet (scripts/make-magnet.ts), the particle field
  behind it, and the "What we believe" window.
*/
export const MARK = {
  xc: 485.75, // axis of symmetry
  d: 289.75, // arm centreline to axis
  w: 288, // band width, centreline to centreline
  yt: 198, // centre of the rounded arm tips
  yd: 531, // centre of the pole-cap domes
  yo: 589, // centre of the outer bottom arc
  yi: 535, // centre of the inner bottom arc
  stroke: 48, // line weight
  angle: 46.75, // degrees clockwise
} as const;

export type Pt = [number, number];
export type Tf = (p: Pt) => Pt;

const { xc, d, w, yt, yd, yo, yi } = MARK;
const r = w / 2;
const Ro = d + w / 2;
const Ri = d - w / 2;
const xLo = xc - d - w / 2, xLi = xc - d + w / 2, xRi = xc + d - w / 2, xRo = xc + d + w / 2;

/** A point on the tip of each pole: where the magnet's field comes out. */
export const POLES: [Pt, Pt] = [[xc - d, yt - r], [xc + d, yt - r]];
/** Middle of the band at the bottom of the U: the point the window flies into. */
export const BAND: Pt = [xc, (yi + Ri + yo + Ro) / 2];

/**
 * The outline as segments: lines and circular arcs (centre, radius, start and end
 * angles in radians, measured in the upright frame, y down).
 */
type Seg = { l: [Pt, Pt] } | { a: { c: Pt; r: number; a0: number; a1: number } };
export const OUTLINE: Seg[] = [
  { a: { c: [xc - d, yt], r, a0: Math.PI, a1: 2 * Math.PI } }, // left tip, over the top
  { l: [[xLi, yt], [xLi, yi]] },
  { a: { c: [xc, yi], r: Ri, a0: Math.PI, a1: 0 } }, // inner arc, under the hole
  { l: [[xRi, yi], [xRi, yt]] },
  { a: { c: [xc + d, yt], r, a0: Math.PI, a1: 2 * Math.PI } }, // right tip
  { l: [[xRo, yt], [xRo, yo]] },
  { a: { c: [xc, yo], r: Ro, a0: 0, a1: Math.PI } }, // outer arc, round the bottom
  { l: [[xLo, yo], [xLo, yt]] },
];
export const DOMES: Seg[][] = [
  [{ a: { c: [xc - d, yd], r, a0: Math.PI, a1: 2 * Math.PI } }],
  [{ a: { c: [xc + d, yd], r, a0: Math.PI, a1: 2 * Math.PI } }],
];

/** Rotate by the logo's angle and scale about `anchor`, placing it at `to`. */
export function makeTf(anchor: Pt, to: Pt, scale: number, angleDeg: number = MARK.angle): Tf {
  const t = (angleDeg * Math.PI) / 180, c = Math.cos(t), s = Math.sin(t);
  return ([x, y]) => {
    const dx = x - anchor[0], dy = y - anchor[1];
    return [to[0] + scale * (dx * c - dy * s), to[1] + scale * (dx * s + dy * c)];
  };
}

const f = (n: number) => Math.round(n * 100) / 100;

/** SVG path data for a run of segments under a rotate-and-scale transform. */
export function pathData(segs: Seg[], tf: Tf, scale: number, close: boolean): string {
  let out = "";
  segs.forEach((seg, i) => {
    if ("l" in seg) {
      const [p0, p1] = seg.l.map(tf);
      out += (i === 0 ? `M${f(p0[0])},${f(p0[1])}` : "") + `L${f(p1[0])},${f(p1[1])}`;
    } else {
      const { c, r: rad, a0, a1 } = seg.a;
      const at = (a: number): Pt => tf([c[0] + rad * Math.cos(a), c[1] + rad * Math.sin(a)]);
      const p0 = at(a0), p1 = at(a1);
      const sweep = a1 > a0 ? 1 : 0; // clockwise on screen when the angle grows (y down)
      const large = Math.abs(a1 - a0) > Math.PI ? 1 : 0;
      if (i === 0) out += `M${f(p0[0])},${f(p0[1])}`;
      out += `A${f(rad * scale)},${f(rad * scale)} 0 ${large} ${sweep} ${f(p1[0])},${f(p1[1])}`;
    }
  });
  return close ? out + "Z" : out;
}

/** Points along the outline, for bounds and for the particle field. */
export function samplePoints(segs: Seg[], n = 24): Pt[] {
  const pts: Pt[] = [];
  for (const seg of segs) {
    if ("l" in seg) pts.push(seg.l[0], seg.l[1]);
    else {
      const { c, r: rad, a0, a1 } = seg.a;
      for (let k = 0; k <= n; k++) {
        const a = a0 + ((a1 - a0) * k) / n;
        pts.push([c[0] + rad * Math.cos(a), c[1] + rad * Math.sin(a)]);
      }
    }
  }
  return pts;
}

/** The turned mark's bounds in logo units (line weight included), and its centre. */
export function markBounds() {
  const tf = makeTf([0, 0], [0, 0], 1);
  const pts = samplePoints(OUTLINE).map(tf);
  const half = MARK.stroke / 2;
  const xs = pts.map((p) => p[0]), ys = pts.map((p) => p[1]);
  const minX = Math.min(...xs) - half, maxX = Math.max(...xs) + half;
  const minY = Math.min(...ys) - half, maxY = Math.max(...ys) + half;
  // the upright point that lands on the centre of the turned bounds
  const t = (-MARK.angle * Math.PI) / 180, c = Math.cos(t), s = Math.sin(t);
  const mx = (minX + maxX) / 2, my = (minY + maxY) / 2;
  const centre: Pt = [mx * c - my * s, mx * s + my * c];
  return { width: maxX - minX, height: maxY - minY, centre };
}

/** Where the mark sits in the hero's 512 x 512 Lottie (the field lines need the room up and right). */
export const LOTTIE = { size: 512, scale: 0.2705, centre: [232, 284] as Pt };
