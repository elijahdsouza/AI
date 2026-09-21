import { chromium } from 'playwright-core';
const CHROME='/opt/pw-browsers/chromium-1194/chrome-linux/chrome';
const URL='http://localhost:4500/index.html';
const b = await chromium.launch({ executablePath: CHROME, args:['--no-sandbox','--disable-dev-shm-usage','--force-color-profile=srgb'] });

async function run(tag, vp, opts={}) {
  const ctx = await b.newContext({ viewport: vp, deviceScaleFactor: 1,
    reducedMotion: opts.reduced ? 'reduce' : 'no-preference' });
  const p = await ctx.newPage();
  await p.goto(URL, {waitUntil:'networkidle', timeout:60000});
  await p.waitForTimeout(1800);
  if (opts.theme) { await p.click('#w-'+opts.theme); await p.waitForTimeout(700); }
  // Wait for the typewriter to settle on a whole phrase, so a screenshot
  // shows the headline as a reader sees it rather than mid-keystroke.
  await p.waitForFunction(() => {
    const t = document.getElementById('tw');
    return !t || /\.$/.test(t.textContent.trim());
  }, null, {timeout: 8000}).catch(()=>{});
  const h = await p.evaluate(()=>document.documentElement.scrollHeight);
  await p.screenshot({ path:`lab/${tag}-a-top.png` });
  for (const [i,y] of [[1,0.30],[2,0.55],[3,0.80]]) {
    await p.evaluate(yy=>window.scrollTo(0,yy), Math.round(h*y));
    await p.waitForTimeout(1100);
    await p.screenshot({ path:`lab/${tag}-${'bcd'[i-1]}-${Math.round(y*100)}.png` });
  }
  console.log(tag, 'height', h, 'screens', (h/vp.height).toFixed(1));
  await ctx.close();
}
await run('bone',  {width:1440,height:900}, {theme:'bone'});
await run('black', {width:1440,height:900}, {theme:'black'});
await run('m-bone',{width:390, height:844}, {theme:'bone'});
await run('reduced',{width:1440,height:900},{theme:'bone', reduced:true});
await b.close();
