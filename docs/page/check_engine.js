// Check the page's JavaScript engine against Lean's results in truth.json.
// Usage: node check_engine.js   (from docs/page/)
const fs = require('fs'), path = require('path'), vm = require('vm');
const html = fs.readFileSync(path.join(__dirname, '..', 'index.html'), 'utf8');
const src = /<script id="engine">([\s\S]*?)<\/script>/.exec(html)[1];
const sandbox = { module: { exports: {} } };
vm.runInNewContext(src, sandbox);
const E = sandbox.module.exports;
const T = JSON.parse(fs.readFileSync(path.join(__dirname, 'truth.json'), 'utf8'));

let pass = 0, fail = 0;
const check = (label, got, want) => {
  if (JSON.stringify(got) === JSON.stringify(want)) pass++;
  else { fail++; console.log('MISMATCH', label, '\n  engine:', JSON.stringify(got), '\n  lean:  ', JSON.stringify(want)); }
};
const parseExpr = t => { const m = /^⟨(.*), ([^,⟩]+)⟩/.exec(t); return { str: m[1].split(' '), cat: m[2] }; };
const errText = c => c.messages.filter(m => m.severity === 'error').map(m => m.text);

// rule tables
for (const g of ['linear₁', 'linear₂', 'xbarGB']) check('rules ' + g, E.grammars[g].rules.map(r => r.name), T.rules[g]);

function ruleCase(g, c, label) {
  const m = /^rule "([^"]*)" (.*)$/.exec(c.cmd);
  const env = Object.fromEntries(c.before.map(([n, t]) => [n, parseExpr(t)]));
  const f = E.findRule(g, m[1]);
  if (!f.ok) return check(label, [f.msg], errText(c));
  const r = E.applyRule(f.rule, m[2].split(' ').map(n => env[n]));
  if (!r.ok) return check(label, [r.msg], errText(c));
  check(label, [true, E.exprText(r.out)], [c.ok, c.after[c.after.length - 1][1]]);
}
const G = { lin1: 'linear₁', over: 'linear₂', xbar: 'xbarGB' };
for (const k of Object.keys(G)) {
  T[k].steps.forEach((c, i) => ruleCase(G[k], c, `${k} step ${i + 1}: ${c.cmd}`));
  T[k].wrong.forEach(c => ruleCase(G[k], c, `${k} wrong: ${c.cmd}`));
}
T.impossible.cases.forEach(c => ruleCase('linear₁', c, `impossible: ${c.cmd}`));

// MP: run the commands on the engine's own workspace
const target = ['the', 'cat', 'will', 'sleep'];
const info = c => c.messages.filter(m => m.severity === 'information').map(m => m.text);
let ws = [];
const steps = T.mp.steps.map(c => c.cmd);
T.mp.steps.forEach((c, i) => {
  const r = E.mpCommand(ws, c.cmd, target);
  ws = r.ws;
  check(`mp step ${i + 1}: ${c.cmd}`, [E.renderWS(ws), r.msgs], [c.after[0][1], info(c)]);
});
T.mp.wrong.forEach(c => {
  let w = [];
  steps.slice(0, c.after_step).forEach(s => { w = E.mpCommand(w, s, target).ws; });
  const r = E.mpCommand(w, c.cmd, target);
  if (!r.ok) check(`mp wrong: ${c.cmd}`, [r.msg], errText(c));
  else check(`mp wrong: ${c.cmd}`, [c.ok, E.renderWS(r.ws)], [true, c.after[0][1]]);
});
const ncases = T.lin1.steps.length + T.lin1.wrong.length + T.over.steps.length + T.over.wrong.length +
  T.xbar.steps.length + T.xbar.wrong.length + T.impossible.cases.length + T.mp.steps.length + T.mp.wrong.length;
console.log(`${pass} checks passed, ${fail} failed (${ncases} Lean cases + 3 rule tables)`);
process.exit(fail ? 1 : 0);
