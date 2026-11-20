// Check the page's JavaScript engine against Lean's results in truth.json.
// Usage: node check_engine.js   (from docs/page/)
// Rule levels are replayed in the engine from the lexicon, step by step, so that
// derived expressions keep everything Lean's category carries (a waiting phrase
// is displayed only as VP/DP, but its string matters).
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
const parseLex = t => { const m = /^⟨(.*), ([^,⟩]+)⟩/.exec(t); return { str: m[1] === '∅' ? [] : m[1].split(' '), cat: m[2] }; };
const errText = c => c.messages.filter(m => m.severity === 'error').map(m => m.text);

for (const g of ['linear₁', 'linear₂', 'xbarGB']) check('rules ' + g, E.grammars[g].rules.map(r => r.name), T.rules[g]);

/* run one `rule` command on an environment of named expressions */
function run(g, env, cmd) {
  const m = /^rule "([^"]*)" (.*)$/.exec(cmd);
  const f = E.findRule(g, m[1]);
  if (!f.ok) return { ok: false, msg: f.msg };
  return E.applyRule(f.rule, m[2].split(' ').map(n => env[n]));
}
function lexEnv(c) {
  const env = {};
  c.before.forEach(([n, t]) => { if (t.endsWith('∈ Lex(' + t.split('∈ Lex(')[1])) env[n] = parseLex(t); });
  return env;
}
function replay(g, steps, n) {
  const env = lexEnv(steps[0]);
  steps.slice(0, n).forEach(c => { const r = run(g, env, c.cmd); env[c.after[c.after.length - 1][0]] = r.out; });
  return env;
}
const G = { lin1: 'linear₁', over: 'linear₂', xbar: 'xbarGB' };
for (const k of Object.keys(G)) {
  const g = G[k], steps = T[k].steps;
  steps.forEach((c, i) => {
    const r = run(g, replay(g, steps, i), c.cmd);
    check(`${k} step ${i + 1}: ${c.cmd}`, r.ok ? [true, E.exprText(r.out)] : [r.msg], [c.ok, c.after[c.after.length - 1][1]]);
  });
  T[k].wrong.forEach(c => {
    const r = run(g, replay(g, steps, c.after_step), c.cmd);
    check(`${k} wrong: ${c.cmd}`, r.ok ? [true, E.exprText(r.out)] : [r.msg], c.ok ? [true, c.after[c.after.length - 1][1]] : errText(c));
  });
}
T.impossible.cases.forEach(c => {
  const r = run('linear₁', lexEnv(c), c.cmd);
  check(`impossible: ${c.cmd}`, r.ok ? [true] : [r.msg], errText(c));
});

// MP: run the commands on the engine's own workspace
const target = ['the', 'cat', 'will', 'sleep'];
const info = c => c.messages.filter(m => m.severity === 'information').map(m => m.text);
let ws = [];
const mpSteps = T.mp.steps.map(c => c.cmd);
T.mp.steps.forEach((c, i) => {
  const r = E.mpCommand(ws, c.cmd, target);
  ws = r.ws;
  check(`mp step ${i + 1}: ${c.cmd}`, [E.renderWS(ws), r.msgs], [c.after[0][1], info(c)]);
});
T.mp.wrong.forEach(c => {
  let w = [];
  mpSteps.slice(0, c.after_step).forEach(s => { w = E.mpCommand(w, s, target).ws; });
  const r = E.mpCommand(w, c.cmd, target);
  if (!r.ok) check(`mp wrong: ${c.cmd}`, [r.msg], errText(c));
  else check(`mp wrong: ${c.cmd}`, [c.ok, E.renderWS(r.ws)], [true, c.after[0][1]]);
});
const n = ['lin1', 'over', 'xbar', 'mp'].reduce((a, k) => a + T[k].steps.length + T[k].wrong.length, 0) + T.impossible.cases.length;
console.log(`${pass} checks passed, ${fail} failed (${n} Lean cases + 3 rule tables)`);
process.exit(fail ? 1 : 0);
