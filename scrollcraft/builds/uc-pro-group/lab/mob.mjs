import { chromium } from 'playwright-core';
const b=await chromium.launch({executablePath:'/opt/pw-browsers/chromium-1194/chrome-linux/chrome',args:['--no-sandbox','--disable-dev-shm-usage']});
for(const [tag,vp,red] of [['m',{width:390,height:844},false],['rm',{width:1440,height:900},true]]){
  const c=await b.newContext({viewport:vp,reducedMotion:red?'reduce':'no-preference'});
  const p=await c.newPage();
  await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'}); await p.waitForTimeout(1200);
  const r=await p.evaluate(()=>({
    hscroll: document.documentElement.scrollWidth>innerWidth+1,
    overflowers:[...document.querySelectorAll('main *')].filter(e=>{const b=e.getBoundingClientRect();
      return b.right>innerWidth+2 && !e.closest('.mq,.hrail__vp,.cmp') && getComputedStyle(e).position!=='fixed';}).length,
    h1: document.querySelector('h1').textContent.replace(/\s+/g,' ').trim()}));
  await p.screenshot({path:`lab/v4-${tag}.png`});
  console.log(tag, vp.width+'px', '| page scrolls sideways:', r.hscroll, '| stray overflowers:', r.overflowers);
  if(red) console.log('   reduced-motion H1:', JSON.stringify(r.h1));
  await c.close();}
await b.close();
