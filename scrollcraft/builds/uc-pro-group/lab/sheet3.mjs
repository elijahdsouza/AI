import { chromium } from 'playwright-core';
const CHROME='/opt/pw-browsers/chromium-1194/chrome-linux/chrome';
const b=await chromium.launch({executablePath:CHROME,args:['--no-sandbox','--disable-dev-shm-usage']});
// narrower viewport => shorter full page and a smaller file
const p=await b.newPage({viewport:{width:1100,height:900},deviceScaleFactor:1});
await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'});
await p.waitForTimeout(1500);
await p.waitForFunction(()=>{const t=document.getElementById('tw');
  return !t||/\.$/.test(t.textContent.trim());},null,{timeout:9000}).catch(()=>{});
await p.evaluate(async()=>{for(let y=0;y<document.body.scrollHeight;y+=600){
  scrollTo(0,y); await new Promise(r=>setTimeout(r,55));}});
await p.waitForTimeout(700);
await p.evaluate(()=>{
  // a static capture cannot show horizontal travel, so collapse each rail to
// its natural height instead of printing the reserved scroll distance as a gap
document.querySelectorAll('.hrail').forEach(r=>{r.style.height='auto';});
document.querySelectorAll('.hrail__sticky').forEach(s=>{s.style.position='static';s.style.height='auto';
  s.style.paddingBlock='64px';});
document.querySelectorAll('.hrail__vp').forEach(v=>{v.style.overflow='hidden';});
['track-alt','track-rhythm'].forEach(id=>{const t=document.getElementById(id); if(t) t.style.transform='translate3d(0,0,0)';});
  document.querySelectorAll('.pick,.thumb').forEach(e=>e.style.display='none');
  const bar=document.querySelector('.bar'); if(bar) bar.style.position='absolute';
  scrollTo(0,0);
});
await p.waitForTimeout(400);
const H=await p.evaluate(()=>document.documentElement.scrollHeight);
const W=1100, N=6, slice=Math.ceil(H/N);
for(let i=0;i<N;i++){
  const y=i*slice, h=Math.min(slice, H-y);
  await p.screenshot({path:`lab/print-${i+1}.png`, fullPage:true, clip:{x:0,y,width:W,height:h}});
  console.log(`slice ${i+1}: y=${y} h=${h}`);
}
console.log('total height', H);
await b.close();
