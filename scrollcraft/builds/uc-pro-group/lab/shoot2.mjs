import { chromium } from 'playwright-core';
const CHROME='/opt/pw-browsers/chromium-1194/chrome-linux/chrome';
const URL='http://localhost:4500/index.html';
const b=await chromium.launch({executablePath:CHROME,args:['--no-sandbox','--disable-dev-shm-usage','--force-color-profile=srgb']});

async function page(vp,reduced){
  const ctx=await b.newContext({viewport:vp,deviceScaleFactor:1,
    reducedMotion:reduced?'reduce':'no-preference'});
  const p=await ctx.newPage();
  await p.goto(URL,{waitUntil:'networkidle',timeout:60000});
  await p.evaluate(()=>{try{localStorage.clear()}catch(e){}});
  await p.waitForTimeout(1200);
  return {ctx,p};
}
async function settle(p){
  await p.waitForFunction(()=>{const t=document.getElementById('tw');
    return !t||/\.$/.test(t.textContent.trim());},null,{timeout:9000}).catch(()=>{});
}
// drive the pointer across the stage so the graphic is caught mid-reaction
async function stir(p){
  const box=await p.locator('#stage').boundingBox();
  if(!box) return;
  const cy=box.y+box.height*0.46;
  for(const f of [0.25,0.42,0.55]){
    await p.mouse.move(box.x+box.width*f, cy, {steps:12});
    await p.waitForTimeout(260);
  }
  await p.waitForTimeout(700);
}

for (const g of ['constellation','table','room']) {
  const {ctx,p}=await page({width:1440,height:900},false);
  await p.click(`.pick button[data-g="${g}"]`);
  await p.waitForTimeout(500);
  await settle(p); await stir(p);
  await p.screenshot({path:`lab/v2-${g}.png`});
  console.log('shot', g);
  await ctx.close();
}

// fold: logos + stats + pillars
{
  const {ctx,p}=await page({width:1440,height:900},false);
  await settle(p);
  await p.evaluate(()=>document.getElementById('stats').scrollIntoView({block:'center'}));
  await p.waitForTimeout(1600);
  await p.screenshot({path:'lab/v2-fold.png'});
  const h=await p.evaluate(()=>document.documentElement.scrollHeight);
  console.log('page height',h,'screens',(h/900).toFixed(1));
  // horizontal act at three positions
  const rail=await p.evaluate(()=>{const r=document.getElementById('rail');
    const b=r.getBoundingClientRect();
    return {top:b.top+window.scrollY,h:r.offsetHeight};});
  for(const [i,f] of [[1,0.10],[2,0.48],[3,0.92]].entries()){
    await p.evaluate(y=>window.scrollTo(0,y), Math.round(rail.top+(rail.h-900)*f[1]));
    await p.waitForTimeout(900);
    await p.screenshot({path:`lab/v2-h${f[0]}.png`});
  }
  console.log('shot horizontal');
  await ctx.close();
}

// mobile + reduced
for(const [tag,vp,red] of [['m',{width:390,height:844},false],['reduced',{width:1440,height:900},true]]){
  const {ctx,p}=await page(vp,red);
  await settle(p);
  await p.screenshot({path:`lab/v2-${tag}-top.png`});
  await p.evaluate(()=>document.getElementById('stats').scrollIntoView({block:'center'}));
  await p.waitForTimeout(1200);
  await p.screenshot({path:`lab/v2-${tag}-fold.png`});
  console.log('shot',tag);
  await ctx.close();
}
await b.close();
