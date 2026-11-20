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
XB_LEX = [('kedi', 'kedi', 'x0 .N'), ('köpek', 'köpek', 'x0 .N'), ('gör', 'gör', 'x0 .V'),
          ('yor', '-Iyor', 'x0 .T'), ('c', '', 'x0 .C')]

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
  'xbar': dict(G='xbarTR', lex=XB_LEX, goal='CanYield xbarTR ["kedi", "köpeği", "görüyor"] (xp .C)',
               steps=["rule \"X0 -> X'\" kedi", "rule \"X' -> XP\" kedi_N'", "rule \"X0 -> X'\" köpek",
                      "rule \"X' -> XP\" köpek_N'", "rule \"YP X0 -> X'\" köpek_NP gör",
                      "rule \"YP X' -> XP\" kedi_NP köpeği_gör_V'", "rule \"YP X0 -> X'\" köpeği_gör_VP_NP yor",
                      "rule \"Move α: YP X' -> XP\" kedi_NP köpeği_görüyor_T'_NP",
                      "rule \"YP X0 -> X'\" kedi_köpeği_görüyor_TP c", "rule \"X' -> XP\" kedi_köpeği_görüyor_C'"],
               wrong=[(0, "rule \"X0 -> X'\" gör"), (0, "rule \"X0 YP -> X'\" gör kedi"),
                      (4, "rule \"YP X0 -> X'\" köpek_N' gör"), (4, "rule \"YP X0 -> X'\" gör köpek_NP"),
                      (7, "rule \"X' -> XP\" köpeği_görüyor_T'_NP"), (5, "rule \"X' -> XP\" köpeği_gör_V'"),
                      (7, "rule \"Move α: YP X' -> XP\" köpek_NP köpeği_görüyor_T'_NP"),
                      (7, "rule \"YP X' -> XP\" kedi_NP köpeği_görüyor_T'_NP"),
                      (4, "rule \"X' YP -> X'\" kedi_N' köpek_NP"),
                      (8, "rule \"YP X0 -> X'\" köpeği_görüyor_T'_NP c"),
                      (0, "rule \"N' -> N0\" kedi")]),
  'mp': dict(G=None, lex=[], goal='MP.Converges ["mtoto", "atalala"]',
             steps=['select m toto ata v lala', 'merge m toto', 'merge v lala', 'merge nP vP',
                    'merge ata {nP, vP}', 'merge nP TP'],
             wrong=[(4, 'merge ata vP'), (5, 'merge nP vP'), (1, 'merge toto lala'),
                    # the subject never enters vP: merged straight into the specifier of T (θ-criterion)
                    (3, ['merge ata vP', 'merge nP TP']),
                    # no v: T takes a root (selection)
                    (0, ['select m toto ata lala', 'merge m toto', 'merge ata lala', 'merge nP TP']),
                    # T's head is merged again (chains)
                    (5, ['merge TP ata', 'merge nP {{ata, {nP, vP}}, ata}'])]),
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
ev = run(HEAD + '#eval linear₁.ruleNames\n#eval linear₂.ruleNames\n#eval xbarTR.fruleNames\n')
truth['rules'] = {'linear₁': json.loads(ev[0]['data']), 'linear₂': json.loads(ev[1]['data']),
                  'xbarTR': json.loads(ev[2]['data'])}
json.dump(truth, open(os.path.join(HERE, 'truth.json'), 'w'), ensure_ascii=False, indent=1)
print('cases:', sum(len(v['steps']) + len(v['wrong']) for k, v in truth.items() if k not in ('impossible', 'rules'))
      + len(imp))
