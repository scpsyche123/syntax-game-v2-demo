"""Lean ground truth for the interactive page.

Runs Lean (in ../../playground) on every solution step, every listed wrong move,
and, for the underivable sentence, every grouping of neighbouring words with
every rule. Writes truth.json. The page's JavaScript engine is then checked
against it by check_engine.mjs.
"""
import json, subprocess, os, re, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
PG = os.path.join(HERE, '..', '..', 'playground')
ENV = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])

def run(src):
    path = os.path.join(PG, 'Gen.lean')
    open(path, 'w').write(src)
    p = subprocess.run(['lake', 'env', 'lean', '--json', 'Gen.lean'], cwd=PG, env=ENV,
                       capture_output=True, text=True)
    os.remove(path)
    return [json.loads(l) for l in p.stdout.splitlines() if l.startswith('{')]

HEAD = 'import BareSyntax\nset_option linter.unusedVariables false\nopen BareSyntax\n\n'

def lexbind(G, items):
    def strs(s):
        return '([] : List String)' if not s.split() else '[' + ', '.join(chr(34) + w + chr(34) for w in s.split()) + ']'
    return '\n    '.join(f'({n} : ({strs(s)}, {c}) ∈ {G}.lexicon)' for n, s, c in items)

LIN1_LEX = [('a', 'a', 'Linear1Cat.D'), ('very', 'very', 'Linear1Cat.Adv'),
            ('good', 'good', 'Linear1Cat.A'), ('day', 'day', 'Linear1Cat.N')]
LIN2_LEX = [('a', 'a', 'Linear1Cat.D'), ('the', 'the', 'Linear1Cat.D'),
            ('this', 'this', 'Linear1Cat.D'), ('dog', 'dog', 'Linear1Cat.N')]
XB_LEX = [('the', 'the', 'x0 .D'), ('cat', 'cat', 'x0 .N'), ('dog', 'dog', 'x0 .N'),
          ('see', 'see', 'x0 .V'), ('s', '-s', 'x0 .T'), ('c', '', 'x0 .C')]

LEVELS = {
  'lin1': dict(G='linear₁', lex=LIN1_LEX, goal='CanYield linear₁ ["a", "very", "good", "day"] .D',
               steps=['rule "Adv A -> A" very good', 'rule "A N -> N" very_good_A day',
                      'rule "D N -> D" a very_good_day_N'],
               wrong=[(0, 'rule "A N -> N" very good'), (0, 'rule "D N -> D" a very'),
                      (1, 'rule "D N -> D" a very_good_A')]),
  'over': dict(G='linear₂', lex=LIN2_LEX, goal='CanYield linear₂ ["a", "a", "the", "this", "dog"] .N',
               steps=['rule "D N -> N" this dog', 'rule "D N -> N" the this_dog_N',
                      'rule "D N -> N" a the_this_dog_N', 'rule "D N -> N" a a_the_this_dog_N'],
               wrong=[(0, 'rule "Adv A -> A" the dog'), (0, 'rule "D N -> D" this the')]),
  'xbar': dict(G='xbarGB', lex=XB_LEX, goal='CanYield xbarGB ["the", "cat", "sees", "the", "dog"] (xp .C)',
               steps=["rule \"X0 -> X'\" cat", "rule \"X' -> XP\" cat_N'", "rule \"X0 YP -> X'\" the cat_NP",
                      "rule \"X' -> XP\" the_cat_D'", "rule \"X0 -> X'\" dog", "rule \"X' -> XP\" dog_N'",
                      "rule \"X0 YP -> X'\" the dog_NP", "rule \"X' -> XP\" the_dog_D'",
                      "rule \"X0 YP -> X'\" see the_dog_DP", "rule \"YP X' -> XP\" the_cat_DP see_the_dog_V'",
                      "rule \"X0 YP -> X'\" s see_the_dog_VP_DP", "rule \"Move α: YP X' -> XP\" the_cat_DP sees_the_dog_T'_DP",
                      "rule \"X0 YP -> X'\" c the_cat_sees_the_dog_TP", "rule \"X' -> XP\" the_cat_sees_the_dog_C'"],
               wrong=[(2, "rule \"X0 YP -> X'\" the cat_N'"), (11, "rule \"X' -> XP\" sees_the_dog_T'_DP"),
                      (8, "rule \"X0 YP -> X'\" see dog_NP"), (0, "rule \"X0 -> X'\" the"), (0, "rule \"X0 -> X'\" c"),
                      (4, "rule \"X' YP -> X'\" cat_N' the_cat_DP"), (8, "rule \"YP X' -> XP\" the_cat_DP the_dog_D'"),
                      (11, "rule \"YP X' -> XP\" the_cat_DP sees_the_dog_T'_DP"),
                      (11, "rule \"Move α: YP X' -> XP\" the_dog_DP sees_the_dog_T'_DP"),
                      (9, "rule \"Move α: YP X' -> XP\" the_cat_DP see_the_dog_V'"),
                      (12, "rule \"X0 YP -> X'\" c sees_the_dog_T'_DP"),
                      (9, "rule \"X' -> XP\" see_the_dog_V'"),
                      (0, "rule \"N' -> N0\" cat")]),
  'mp': dict(G=None, lex=[], goal='MP.Converges ["the", "cat", "will", "sleep"]',
             steps=['select the n cat will v sleep', 'merge n cat', 'merge the nP', 'merge v sleep',
                    'merge DP vP', 'merge will {DP, vP}', 'merge DP TP'],
             wrong=[(5, 'merge will vP'), (6, 'merge DP vP'), (1, 'merge cat sleep'),
                    # the subject never enters vP: merged straight into the specifier of T (θ-criterion)
                    (4, ['merge will vP', 'merge DP TP']),
                    # no n, no v: D and T take roots (selection)
                    (0, ['select the cat will sleep', 'merge the cat', 'merge will sleep', 'merge DP TP']),
                    # T's head is merged again (chains)
                    (6, ['merge TP will', 'merge DP {{will, {DP, vP}}, will}'])]),
}

def statement(L, goal):
    b = lexbind(L['G'], L['lex']) if L['lex'] else ''
    return f'example {b} :\n    {goal} := by\n' if b else f'example :\n    {goal} := by\n'

def parse_hyps(text):
    hyps = []
    for ln in text.splitlines():
        if ln.startswith('⊢'):
            continue
        if ' : ' in ln and not ln.startswith(' '):
            n, t = ln.split(' : ', 1)
            hyps.append([n, t])
        elif ln.startswith('  ') and hyps:
            hyps[-1][1] += ' ' + ln.strip()
    return hyps

def case(L, prefix, cmd, goal=None):
    """State before `cmd`, messages of `cmd`, state after it (goal False keeps it open)."""
    src = HEAD + statement(L, goal or 'False')
    for c in prefix:
        src += f'  {c}\n'
    src += '  trace_state\n'
    tl_before = src.count('\n')
    src += f'  {cmd}\n'
    cl = src.count('\n')
    src += '  trace_state\n  sorry\n'
    tl_after = src.count('\n') - 1
    ms = run(src)
    before = [m['data'] for m in ms if m['pos']['line'] == tl_before and m['severity'] == 'information']
    after = [m['data'] for m in ms if m['pos']['line'] == tl_after and m['severity'] == 'information']
    at = [{'severity': m['severity'], 'text': m['data']} for m in ms if m['pos']['line'] == cl]
    return {'cmd': cmd, 'before': parse_hyps(before[0]) if before else None,
            'after': parse_hyps(after[0]) if after else None, 'messages': at,
            'ok': not any(m['severity'] == 'error' for m in at)}

truth = {}
for key, L in LEVELS.items():
    entry = {'steps': [], 'wrong': []}
    for i, st in enumerate(L['steps']):
        c = case(L, L['steps'][:i], st)
        if key == 'mp':   # messages need the real goal
            c['messages'] = case(L, L['steps'][:i], st, goal=L['goal'])['messages']
        assert c['ok'], (key, st, c['messages'])
        entry['steps'].append(c)
    for n, cmd in L['wrong']:
        cmds = cmd if isinstance(cmd, list) else [cmd]
        c = case(L, L['steps'][:n] + cmds[:-1], cmds[-1], goal=L['goal'] if key == 'mp' else None)
        c['after_step'] = n
        c['extra'] = cmds[:-1]
        entry['wrong'].append(c)
    truth[key] = entry

# the underivable sentence: every grouping of neighbours, every rule of linear₁
IMP = dict(G='linear₁', lex=[('a', 'a', 'Linear1Cat.D'), ('very', 'very', 'Linear1Cat.Adv'),
                            ('day', 'day', 'Linear1Cat.N')])
words = ['a', 'very', 'day']
rules = ['Adv A -> A', 'A N -> N', 'D N -> D']
imp = []
for i in range(3):
    for j in range(i + 2, 4):
        for r in rules:
            imp.append(case(IMP, [], f'rule "{r}" ' + ' '.join(words[i:j])))
truth['impossible'] = {'cases': imp}
assert not any(c['ok'] for c in imp)

# rule lists as Lean shows them
ev = run(HEAD + '#eval linear₁.ruleNames\n#eval linear₂.ruleNames\n#eval xbarGB.fruleNames\n')
truth['rules'] = {'linear₁': json.loads(ev[0]['data']), 'linear₂': json.loads(ev[1]['data']),
                  'xbarGB': json.loads(ev[2]['data'])}
json.dump(truth, open(os.path.join(HERE, 'truth.json'), 'w'), ensure_ascii=False, indent=1)
print('cases:', sum(len(v['steps']) + len(v['wrong']) for k, v in truth.items() if k not in ('impossible', 'rules'))
      + len(imp))
