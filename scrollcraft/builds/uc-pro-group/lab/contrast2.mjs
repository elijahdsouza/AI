import { chromium } from 'playwright-core';
const CHROME='/opt/pw-browsers/chromium-1194/chrome-linux/chrome';
const b=await chromium.launch({executablePath:CHROME,args:['--no-sandbox','--disable-dev-shm-usage']});
const p=await b.newPage({viewport:{width:1440,height:900}});
await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'});
await p.waitForTimeout(1500);
const rows=await p.evaluate(()=>{
  const lum=c=>{const [r,g,bl]=c.map(v=>{v/=255;return v<=0.03928?v/12.92:Math.pow((v+0.055)/1.055,2.4);});
    return 0.2126*r+0.7152*g+0.0722*bl;};
  const parse=s=>{const m=s.match(/[\d.]+/g);if(!m)return null;
    const v=m.slice(0,3).map(Number); const a=m.length>3?+m[3]:1; return {v,a};};
  // composite a possibly-translucent stack down to an opaque colour
  function bg(el){
    let n=el, acc=null;
    while(n&&n!==document.documentElement){
      const c=parse(getComputedStyle(n).backgroundColor);
      if(c&&c.a>0){ if(!acc) acc={v:c.v.slice(),a:c.a};
        else acc={v:acc.v.map((x,i)=>x*acc.a+c.v[i]*(1-acc.a)),a:1};
        if(acc.a>=0.999) return acc.v; }
      n=n.parentElement;
    }
    const body=parse(getComputedStyle(document.body).backgroundColor).v;
    if(!acc) return body;
    return acc.v.map((x,i)=>x*acc.a+body[i]*(1-acc.a));
  }
  const out=[];
  document.querySelectorAll('h1,h2,h3,p,li,a,span,figcaption,b').forEach(el=>{
    const t=el.textContent.trim(); if(!t||el.children.length>1) return;
    const cs=getComputedStyle(el), r=el.getBoundingClientRect();
    if(r.width<4||r.height<4) return;
    if(cs.visibility==='hidden'||cs.display==='none') return;
    let o=1,n2=el; while(n2&&n2!==document.documentElement){
      o*=parseFloat(getComputedStyle(n2).opacity||'1'); n2=n2.parentElement; }
    if(o<0.2) return;
    if(el.closest('.stage')||el.closest('.pick')) return;  // over media / dev control
    const fg=parse(cs.color); if(!fg) return;
    const f=fg.v.map((x,i)=>x*o + bg(el)[i]*(1-o));  // fold opacity into the fg
    const L1=lum(f),L2=lum(bg(el));
    const ratio=(Math.max(L1,L2)+0.05)/(Math.min(L1,L2)+0.05);
    const px=parseFloat(cs.fontSize),wt=parseInt(cs.fontWeight)||400;
    const large=px>=24||(px>=18.66&&wt>=700);
    const need=large?3:4.5;
    out.push({t:t.slice(0,44),px:+px.toFixed(1),wt,o:+o.toFixed(2),
              ratio:+ratio.toFixed(2),need,pass:ratio>=need});
  });
  return out;
});
const fails=rows.filter(r=>!r.pass);
console.log(`${rows.length} painted text nodes · ${fails.length} below threshold`);
fails.forEach(f=>console.log(`  FAIL ${f.ratio} (need ${f.need}) ${f.px}px/${f.wt} op${f.o} :: ${f.t}`));
console.log('lowest:', rows.reduce((a,r)=>Math.min(a,r.ratio),99).toFixed(2));
await b.close();
