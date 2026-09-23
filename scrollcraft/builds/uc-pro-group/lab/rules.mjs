import { chromium } from 'playwright-core';
const b=await chromium.launch({executablePath:'/opt/pw-browsers/chromium-1194/chrome-linux/chrome',args:['--no-sandbox','--disable-dev-shm-usage']});
const p=await b.newPage({viewport:{width:1440,height:900}});
await p.goto('http://localhost:4500/index.html',{waitUntil:'networkidle'});
await p.waitForTimeout(1200);
const r=await p.evaluate(()=>{
  const out={};
  // RULE: no cream base anywhere
  const cream=[]; document.querySelectorAll('*').forEach(el=>{
    const c=getComputedStyle(el).backgroundColor;
    if(/rgb\(242, 240, 234\)|rgb\(244, 241, 233\)|rgb\(247, 241, 224\)/.test(c)) cream.push(el.tagName+'#'+el.id+'.'+el.className);});
  out.cream=cream;
  // RULE: every H1/H2 highlights key words in gold
  const heads=[...document.querySelectorAll('h1,h2')];
  out.headings=heads.length;
  out.noAccent=heads.filter(h=>!h.querySelector('.hl,.tail')).map(h=>h.textContent.trim().slice(0,60));
  // RULE: no em dash in visible copy
  const w=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT);
  const em=[]; let n; while(n=w.nextNode()){
    if(n.parentElement.closest('script,style'))continue;
    if(/—/.test(n.textContent)) em.push(n.textContent.trim().slice(0,50));}
  out.emdash=em;
  // RULE: real icon set, uniform
  out.lucideUses=document.querySelectorAll('use[href^="#i-"]').length;
  out.handDrawn=document.querySelectorAll('[data-s],[data-d],[data-draw]').length;
  // sections and grounds
  out.sections=[...document.querySelectorAll('main > section')].map(s=>{
    const g=[...s.classList].find(c=>c.startsWith('g-'))||'?';
    const h=s.querySelector('h1,h2'); return g.replace('g-','')+' · '+(s.id||'-')+' · '+(h?h.textContent.trim().slice(0,46):'(no heading)');});
  out.tbc=document.querySelectorAll('.tbc').length;
  return out;});
console.log('SECTIONS ('+r.sections.length+')'); r.sections.forEach((s,i)=>console.log('  '+String(i+1).padStart(2)+' '+s));
console.log('\nRULE  no cream base         :', r.cream.length? 'FAIL '+r.cream.join(', ') : 'PASS');
console.log('RULE  gold accent, H1+H2    :', r.noAccent.length? 'FAIL on '+r.noAccent.length+': '+r.noAccent.join(' | ') : 'PASS ('+r.headings+' headings)');
console.log('RULE  no em dash visible    :', r.emdash.length? 'FAIL '+r.emdash.join(' | ') : 'PASS');
console.log('RULE  real uniform icons    :', r.handDrawn? 'FAIL '+r.handDrawn+' hand-drawn marks remain' : 'PASS ('+r.lucideUses+' Lucide icons)');
console.log('      visible [TBC] markers :', r.tbc);
await b.close();
