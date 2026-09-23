import { chromium } from 'playwright-core';
const b=await chromium.launch({executablePath:'/opt/pw-browsers/chromium-1194/chrome-linux/chrome',args:['--no-sandbox','--disable-dev-shm-usage']});
const p=await b.newPage({viewport:{width:390,height:844}});
await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'}); await p.waitForTimeout(1000);
console.log(await p.evaluate(()=>[...document.querySelectorAll('main *')].filter(e=>{const r=e.getBoundingClientRect();
  return r.right>innerWidth+2 && !e.closest('.mq,.hrail__vp,.cmp') && getComputedStyle(e).position!=='fixed';})
  .map(e=>`${e.tagName.toLowerCase()}.${[...e.classList].join('.')} right=${Math.round(e.getBoundingClientRect().right)} clipped-by=${(()=>{let n=e.parentElement;while(n){const o=getComputedStyle(n).overflow;if(o!=='visible')return n.className||n.tagName;n=n.parentElement}return 'none'})()}`).join('\n')));
await b.close();
