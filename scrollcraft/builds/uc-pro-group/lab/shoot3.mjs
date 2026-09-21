import { chromium } from 'playwright-core';
const CHROME='/opt/pw-browsers/chromium-1194/chrome-linux/chrome';
const URL='http://localhost:4500/index.html';
const b=await chromium.launch({executablePath:CHROME,args:['--no-sandbox','--disable-dev-shm-usage','--force-color-profile=srgb']});

async function open(vp,reduced){
  const ctx=await b.newContext({viewport:vp,deviceScaleFactor:1,
    reducedMotion:reduced?'reduce':'no-preference'});
  const p=await ctx.newPage();
  await p.goto(URL,{waitUntil:'networkidle',timeout:60000});
  await p.waitForTimeout(1400);
  await p.waitForFunction(()=>{const t=document.getElementById('tw');
    return !t||/\.$/.test(t.textContent.trim());},null,{timeout:9000}).catch(()=>{});
  return {ctx,p};
}
async function stir(p){
  const box=await p.locator('#stage').boundingBox(); if(!box) return;
  for(const f of [0.30,0.48,0.60]){
    await p.mouse.move(box.x+box.width*f, box.y+box.height*0.45,{steps:10});
    await p.waitForTimeout(240);
  }
  await p.waitForTimeout(650);
}

// hero, both lattice modes
for(const g of ['room','void']){
  const {ctx,p}=await open({width:1440,height:900},false);
  await p.click(`.pick button[data-g="${g}"]`); await p.waitForTimeout(450);
  await stir(p);
  await p.screenshot({path:`lab/v3-hero-${g}.png`});
  console.log('hero',g); await ctx.close();
}

// every section, centred
{
  const {ctx,p}=await open({width:1440,height:900},false);
  const h=await p.evaluate(()=>document.documentElement.scrollHeight);
  console.log('page height',h,'screens',(h/900).toFixed(1));
  const ids=['community','problem','alternatives','third-space','pillars','proof',
             'standard','compare','pricing','services','founding','faq','close'];
  for(const id of ids){
    const ok=await p.evaluate(i=>{const el=document.getElementById(i);
      if(!el)return false; el.scrollIntoView({block:'start'}); window.scrollBy(0,-70); return true;},id);
    if(!ok){console.log('MISSING SECTION',id);continue;}
    await p.waitForTimeout(950);
    await p.screenshot({path:`lab/v3-${id}.png`});
  }
  // horizontal act, mid travel
  const rail=await p.evaluate(()=>{const r=document.getElementById('rail');
    const bb=r.getBoundingClientRect(); return {top:bb.top+scrollY,h:r.offsetHeight};});
  await p.evaluate(y=>scrollTo(0,y), Math.round(rail.top+(rail.h-900)*0.5));
  await p.waitForTimeout(900);
  await p.screenshot({path:'lab/v3-rhythm-mid.png'});
  console.log('sections done'); await ctx.close();
}

// mobile + reduced
for(const [tag,vp,red] of [['m',{width:390,height:844},false],
                           ['reduced',{width:1440,height:900},true]]){
  const {ctx,p}=await open(vp,red);
  await p.screenshot({path:`lab/v3-${tag}-top.png`});
  for(const id of ['pricing','founding']){
    await p.evaluate(i=>{const e=document.getElementById(i);
      if(e){e.scrollIntoView({block:'start'});window.scrollBy(0,-60);}},id);
    await p.waitForTimeout(900);
    await p.screenshot({path:`lab/v3-${tag}-${id}.png`});
  }
  console.log('shot',tag); await ctx.close();
}
await b.close();
