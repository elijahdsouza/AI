import { chromium } from 'playwright-core';
const CHROME='/opt/pw-browsers/chromium-1194/chrome-linux/chrome';
const b = await chromium.launch({executablePath:CHROME,args:['--no-sandbox','--disable-dev-shm-usage']});
for (const theme of ['bone','black']) {
  const p = await b.newPage({viewport:{width:1440,height:900}});
  await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'});
  await p.click('#w-'+theme); await p.waitForTimeout(500);
  const rows = await p.evaluate(()=>{
    const lum=c=>{const [r,g,bl]=c.map(v=>{v/=255;return v<=0.03928?v/12.92:Math.pow((v+0.055)/1.055,2.4);});
      return 0.2126*r+0.7152*g+0.0722*bl;};
    const parse=s=>{const m=s.match(/[\d.]+/g); return m?m.slice(0,3).map(Number):null;};
    function bg(el){ let n=el; while(n&&n!==document.documentElement){
      const c=getComputedStyle(n).backgroundColor;
      if(c&&!/rgba\(0, 0, 0, 0\)|transparent/.test(c)) return parse(c); n=n.parentElement;}
      return parse(getComputedStyle(document.body).backgroundColor); }
    const sel='h1,h2,h3,p,li,a,figcaption,blockquote,span.strip,.strip span,.calibre__lead';
    const out=[];
    document.querySelectorAll(sel).forEach(el=>{
      const t=el.textContent.trim(); if(!t||el.children.length>2) return;
      const cs=getComputedStyle(el); const r=el.getBoundingClientRect();
      if(r.width<4||r.height<4) return;
      // skip anything not actually painted: hidden tooltips, collapsed nodes
      let o=1,n2=el; while(n2&&n2!==document.documentElement){
        o*=parseFloat(getComputedStyle(n2).opacity||'1'); n2=n2.parentElement; }
      if(o<0.06||cs.visibility==='hidden'||cs.display==='none') return;
      // text over media is composited against the scrim's worst case, not the DOM bg
      if(el.closest('.plate')) return;
      // .seat is an icon link: its accessible name is an aria-label and its
      // visible text lives in a tooltip at opacity 0. Audited as a control
      // (focus ring), not as body text.
      if(el.classList.contains('seat')||el.closest('.seat__label')) return;
      const fg=parse(cs.color), b2=bg(el); if(!fg||!b2) return;
      const L1=lum(fg),L2=lum(b2);
      const ratio=(Math.max(L1,L2)+0.05)/(Math.min(L1,L2)+0.05);
      const px=parseFloat(cs.fontSize), wt=parseInt(cs.fontWeight)||400;
      const large = px>=24 || (px>=18.66 && wt>=700);
      const need = large?3:4.5;
      out.push({t:t.slice(0,42),px:+px.toFixed(1),wt,ratio:+ratio.toFixed(2),need,pass:ratio>=need});
    });
    return out;
  });
  const fails=rows.filter(r=>!r.pass);
  console.log(`\n--- ${theme} --- ${rows.length} text nodes, ${fails.length} below threshold`);
  fails.forEach(f=>console.log(`  FAIL ${f.ratio} (need ${f.need}) ${f.px}px/${f.wt} :: ${f.t}`));
  const min=rows.reduce((a,r)=>Math.min(a,r.ratio),99);
  console.log(`  lowest ratio on page: ${min.toFixed(2)}`);
  await p.close();
}
await b.close();
