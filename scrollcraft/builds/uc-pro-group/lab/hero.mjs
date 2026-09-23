import { chromium } from 'playwright-core';
const b=await chromium.launch({executablePath:'/opt/pw-browsers/chromium-1194/chrome-linux/chrome',args:['--no-sandbox','--disable-dev-shm-usage']});
const p=await b.newPage({viewport:{width:1440,height:900}});
await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'});
await p.waitForTimeout(1500);
const box=await p.locator('#stage').boundingBox();
for(const f of [0.35,0.5,0.62]){ await p.mouse.move(box.x+box.width*f,box.y+box.height*0.45,{steps:10}); await p.waitForTimeout(260); }
await p.waitForTimeout(700);
await p.screenshot({path:'lab/v4-hero.png'});
await b.close(); console.log('hero shot');
