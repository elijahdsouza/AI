import { chromium } from 'playwright-core';
const CHROME='/opt/pw-browsers/chromium-1194/chrome-linux/chrome';
const b=await chromium.launch({executablePath:CHROME,args:['--no-sandbox','--disable-dev-shm-usage']});
const p=await b.newPage({viewport:{width:1440,height:900},deviceScaleFactor:1});
await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'});
await p.waitForTimeout(1500);
await p.waitForFunction(()=>{const t=document.getElementById('tw');
  return !t||/\.$/.test(t.textContent.trim());},null,{timeout:9000}).catch(()=>{});
// walk the page so counters/reveals have fired, then capture full-page
await p.evaluate(async()=>{for(let y=0;y<document.body.scrollHeight;y+=600){
  scrollTo(0,y); await new Promise(r=>setTimeout(r,60));}});
await p.waitForTimeout(800);
await p.evaluate(()=>{
  // freeze the jacked rail mid-travel and hide dev chrome for the sheet
  const t=document.getElementById('track'); if(t) t.style.transform='translate3d(-620px,0,0)';
  document.querySelectorAll('.pick,.thumb').forEach(e=>e.style.display='none');
  scrollTo(0,0);
});
await p.waitForTimeout(500);
await p.screenshot({path:'lab/v3-FULL.png',fullPage:true});
const h=await p.evaluate(()=>document.documentElement.scrollHeight);
console.log('full page captured',h,'px ·',(h/900).toFixed(1),'screens');
await b.close();
