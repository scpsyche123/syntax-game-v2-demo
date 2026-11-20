"""Run each level in Lean, capture the infoview state after every step and the
messages of every step, plus a few rejected moves. Output: data.json."""
import json, subprocess, os

HERE = os.path.dirname(os.path.abspath(__file__))
PG = os.path.join(HERE, '..', '..', 'playground')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])

L1_HYPS = '''(a : (["a"], Linear1Cat.D) ∈ linear₁.lexicon)
    (very : (["very"], Linear1Cat.Adv) ∈ linear₁.lexicon)
    (good : (["good"], Linear1Cat.A) ∈ linear₁.lexicon)
    (day : (["day"], Linear1Cat.N) ∈ linear₁.lexicon)'''
L1_GOAL = 'CanYield linear₁ ["a", "good", "day"] .N'
L1_STEPS = ['rule "N -> D A N" a good day']

L2_HYPS = '''(the : (["the"], x0 .D) ∈ xbarGB.lexicon)
    (cat : (["cat"], x0 .N) ∈ xbarGB.lexicon)
    (dog : (["dog"], x0 .N) ∈ xbarGB.lexicon)
    (see : (["see"], x0 .V) ∈ xbarGB.lexicon)
    (s : (["-s"], x0 .T) ∈ xbarGB.lexicon)'''
L2_GOAL = 'CanYield xbarGB ["the", "cat", "sees", "the", "dog"] (xp .T)'
L2_STEPS = ['rule "N\' -> N0" cat', 'rule "NP -> N\'" cat_N\'', 'rule "D\' -> D0 NP" the cat_NP',
            'rule "DP -> D\'" the_cat_D\'', 'rule "N\' -> N0" dog', 'rule "NP -> N\'" dog_N\'',
            'rule "D\' -> D0 NP" the dog_NP', 'rule "DP -> D\'" the_dog_D\'',
            'rule "V\' -> V0 DP" see the_dog_DP', 'rule "VP -> V\'" see_the_dog_V\'',
            'rule "T\' -> T0 VP" s see_the_dog_VP', 'rule "TP -> DP T\'" the_cat_DP sees_the_dog_T\'']

L3_HYPS = ''
L3_GOAL = 'MP.Converges ["the", "cat", "will", "sleep"]'
L3_STEPS = ['select the n cat will v sleep', 'merge n cat', 'merge the nP', 'merge v sleep',
            'merge DP vP', 'merge will {DP, vP}', 'merge DP TP']

LEVELS = [('linear', L1_HYPS, L1_GOAL, L1_STEPS),
          ('xbargb', L2_HYPS, L2_GOAL, L2_STEPS),
          ('mp', L3_HYPS, L3_GOAL, L3_STEPS)]

# wrong moves: (level, number of correct steps before, wrong command)
WRONG = [
    ('linear', 0, 'rule "N -> D N" a good day'),
    ('linear', 0, 'rule "N -> D A N" good a day'),
    ('xbargb', 2, 'rule "D\' -> D0 NP" the cat_N\''),
    ('xbargb', 11, 'rule "TP -> T\'" sees_the_dog_T\''),
    ('xbargb', 8, 'rule "V\' -> V0 DP" see dog_NP'),
    ('mp', 5, 'merge will vP'),
    ('mp', 6, 'merge DP vP'),
    ('mp', 1, 'merge cat sleep'),
]

def run(src):
    path = os.path.join(PG, 'Gen.lean')
    open(path, 'w').write(src)
    p = subprocess.run(['lake', 'env', 'lean', '--json', 'Gen.lean'], cwd=PG, env=ENV,
                       capture_output=True, text=True)
    msgs = []
    for line in p.stdout.splitlines():
        line = line.strip()
        if line.startswith('{'):
            msgs.append(json.loads(line))
    os.remove(path)
    return msgs

def header():
    return 'import BareSyntax\nset_option linter.unusedVariables false\nopen BareSyntax\n\n'

def statement(hyps, goal):
    return f'example {hyps} :\n    {goal} := by\n' if hyps else f'example :\n    {goal} := by\n'

def parse_state(text):
    hyps, goals = [], []
    for ln in text.splitlines():
        if ln.startswith('⊢ '):
            goals.append(ln[2:])
        elif ' : ' in ln and not ln.startswith(' '):
            n, t = ln.split(' : ', 1)
            hyps.append([n, t])
        elif ln.startswith('  ') and hyps:
            hyps[-1][1] += ' ' + ln.strip()
    return {'hyps': hyps, 'goal': goals[0] if goals else None}

data = {}
for key, hyps, goal, steps in LEVELS:
    # run A: the real goal, to collect each step's messages and the initial state
    src = header() + statement(hyps, goal) + '  trace_state\n'
    lines_of = []
    base = src.count('\n') + 1
    for i, st in enumerate(steps):
        lines_of.append(base + i)
        src += f'  {st}\n'
    msgsA = run(src)
    # run B: a goal that never closes, so the final hypotheses stay visible
    srcB = header() + statement(hyps, 'False') + '  trace_state\n'
    tl = []
    baseB = srcB.count('\n') + 1
    for i, st in enumerate(steps):
        srcB += f'  {st}\n  trace_state\n'
        tl.append(baseB + 2 * i + 1)
    srcB += '  sorry\n'
    msgsB = run(srcB)
    init = [m for m in msgsA if m['pos']['line'] == base - 1 and m['severity'] == 'information']
    state0 = parse_state(init[0]['data'])
    goal_text = state0['goal']
    out_steps = []
    for i, st in enumerate(steps):
        info = [m['data'] for m in msgsA if m['pos']['line'] == lines_of[i]]
        errs = [m['data'] for m in msgsA if m['pos']['line'] == lines_of[i] and m['severity'] == 'error']
        assert not errs, (key, st, errs)
        sB = [m for m in msgsB if m['pos']['line'] == tl[i] and m['severity'] == 'information']
        stt = parse_state(sB[0]['data'])
        closed = (i == len(steps) - 1)
        out_steps.append({'cmd': st, 'hyps': stt['hyps'], 'messages': info, 'closed': closed})
    unsolved = [m for m in msgsA if m['severity'] == 'error']
    assert not unsolved, (key, unsolved)
    data[key] = {'goal': goal_text, 'start': state0['hyps'], 'steps': out_steps, 'wrong': []}

for key, n, cmd in WRONG:
    _, hyps, goal, steps = next(l for l in LEVELS if l[0] == key)
    src = header() + statement(hyps, goal)
    for st in steps[:n]:
        src += f'  {st}\n'
    line = src.count('\n') + 1
    src += f'  {cmd}\n  sorry\n'
    msgs = run(src)
    at = [m for m in msgs if m['pos']['line'] == line]
    data[key]['wrong'].append({'after': n, 'cmd': cmd,
                               'messages': [{'severity': m['severity'], 'text': m['data']} for m in at]})

# grammar facts straight from Lean
src = header() + '''#eval linear₁.ruleNames
#eval xbarGB.ruleNames
'''
ev = run(src)
data['linear']['rules'] = json.loads(ev[0]['data'])
data['xbargb']['rules'] = json.loads(ev[1]['data'])

# a move free MERGE accepts but that can never be labeled: keep its workspace
src = header() + 'example : False := by\n  select the n cat will v sleep\n  merge cat sleep\n  trace_state\n  sorry\n'
st = [m['data'] for m in run(src) if m['severity'] == 'information'][0]
for w in data['mp']['wrong']:
    if w['cmd'] == 'merge cat sleep':
        w['accepted'] = True
        w['state'] = [l.split(' : ', 1) for l in st.splitlines() if ' : ' in l]

json.dump(data, open(os.path.join(HERE, 'data.json'), 'w'), ensure_ascii=False, indent=1)
tpl = open(os.path.join(HERE, 'template.html')).read()
page = tpl.replace('__DATA__', json.dumps(data, ensure_ascii=False).replace('</', '<\\/'))
open(os.path.join(HERE, '..', 'index.html'), 'w').write(page)
print('ok')
