#!/usr/bin/env python3
"""Regression suite for pgg-smc/scripts/profile_facade_check.sh.

Builds a disposable git repo that mirrors the real tree's declaration shapes,
copies the COMMITTED script in unmodified, and runs one case per mutation.
Nothing in the real repository is touched.
"""
import os, shutil, subprocess, sys, tempfile, pathlib

SCRIPT = pathlib.Path(__file__).resolve().with_name('profile_facade_check.sh')
BOX = pathlib.Path(sys.argv[1] if len(sys.argv) > 1
                   else tempfile.mkdtemp(prefix='pfc-')) / 'pfc_sandbox'

PROFILES = {
  'pgg-smc/instances/pgl27/pgl27_profile.v':
    '(** doc *)\nDefinition pgl27_profile : MonodromyProfile :=\n  @MkMonodromyProfile a b c.\n',
  'pgg-smc/instances/kim2025/five_card_family.v':
    'Definition five_card_profile : MonodromyProfile :=\n  @MkMonodromyProfile a b c.\n',
  'pgg-smc/instances/denboer1989/den_boer_profile.v':
    'Definition den_boer_profile : MonodromyProfile := five_card_profile.\n',
  'pgg-smc/instances/s5/s5_profile.v':
    'Definition s5_profile : MonodromyProfile := @MkMonodromyProfile a b c.\n',
  'pgg-smc/instances/s5x5/s5x5_profile.v':
    'Definition s5x5_profile : MonodromyProfile := @MkMonodromyProfile a b c.\n',
  'pgg-smc/instances/abelian/abel_profile.v':
    'Definition abel_profile : MonodromyProfile := @MkMonodromyProfile a b c.\n',
}
FACADES = {
  'pgg-smc/instances/pgl27/pgl27_analysis.v': ('PGL27Analysis', 'pgl27_profile'),
  'pgg-smc/instances/kim2025/five_card_analysis.v': ('FiveCardAnalysis', 'five_card_profile'),
  'pgg-smc/instances/s5/s5_analysis.v': ('S5Analysis', 's5_profile'),
  'pgg-smc/instances/s5x5/s5x5_analysis.v': ('S5x5Analysis', 's5x5_profile'),
  'pgg-smc/instances/abelian/abelian_analysis.v': ('AbelianAnalysis', 'abel_profile'),
}
# section-local Let shapes, as in the real exec/models files
LETS = {
  'pgg-smc/instances/s5/s5_exec.v':
    'Section E.\nVariable R : realType.\nLet mpS : MonodromyProfile := s5_profile.\nEnd E.\n',
}
OUT_OF_SCOPE = {
  'pgg-smc/protocol/pgg_monodromy_profile.v':
    'Record MonodromyProfile := MkMonodromyProfile { mp_M : nat }.\n',
}

def facade_text(module, profile, alias_inside=True, module_name=None):
    module_name = module_name or module
    alias = 'Definition profile := %s.\n' % profile
    body = alias if alias_inside else ''
    tail = '' if alias_inside else alias
    extra = ''
    if profile == 'five_card_profile':
        extra = 'Definition den_boer_profile := den_boer_profile.den_boer_profile.\n'
    return ('Module %s.\n%s%sEnd %s.\n%s'
            % (module_name, body, extra if alias_inside else '', module_name, tail))

def build(mutate=None):
    if BOX.exists():
        shutil.rmtree(BOX)
    files = dict(PROFILES)
    files.update(LETS)
    files.update(OUT_OF_SCOPE)
    for path, (module, profile) in FACADES.items():
        files[path] = facade_text(module, profile)
    untracked = {}
    if mutate:
        mutate(files, untracked)
    for path, text in files.items():
        p = BOX / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    (BOX / 'pgg-smc/scripts').mkdir(parents=True, exist_ok=True)
    shutil.copy(SCRIPT, BOX / 'pgg-smc/scripts/profile_facade_check.sh')
    os.chmod(BOX / 'pgg-smc/scripts/profile_facade_check.sh', 0o755)
    subprocess.run(['git', 'init', '-q'], cwd=BOX, check=True)
    subprocess.run(['git', 'add', '-A'], cwd=BOX, check=True)
    for path, text in untracked.items():
        p = BOX / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

def run():
    r = subprocess.run(['bash', 'pgg-smc/scripts/profile_facade_check.sh'],
                       cwd=BOX, capture_output=True, text=True)
    return r.returncode, (r.stderr.strip().splitlines() or [''])[0]

ROGUE = 'Definition rogue_profile%s : MonodromyProfile := @MkMonodromyProfile a b c.\n'

CASES = [
 ('C0  baseline', None, 0),
 ('C1  parameterized rogue',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v', ROGUE % ' (eps : nat)'), 2),
 ('C1b implicit-binder rogue',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v', ROGUE % ' {R : realType}'), 2),
 ('C2  Program rogue',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v', 'Program ' + ROGUE % ''), 2),
 ('C3  #[local] rogue is skipped',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v', '#[local] ' + ROGUE % ''), 0),
 ('C4  den Boer body changed',
  lambda f, u: f.__setitem__('pgg-smc/instances/denboer1989/den_boer_profile.v',
     'Definition den_boer_profile : MonodromyProfile := s5_profile.\n'), 1),
 ('C5  facade module renamed',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/s5_analysis.v',
     facade_text('S5Analysis', 's5_profile', module_name='ScratchModule')), 1),
 ('C6  alias outside the module',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/s5_analysis.v',
     facade_text('S5Analysis', 's5_profile', alias_inside=False)), 1),
 ('C7  Module-wrapped rogue',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v',
     'Module M.\n' + ROGUE % '' + 'End M.\n'), 2),
 ('C7b Section-wrapped rogue',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v',
     'Section G.\nVariable n : nat.\n' + ROGUE % '' + 'End G.\n'), 2),
 ('C8  rogue inside a facade file',
  lambda f, u: f.__setitem__('pgg-smc/instances/pgl27/pgl27_analysis.v',
     facade_text('PGL27Analysis', 'pgl27_profile') + ROGUE % ''), 2),
 ('C8b self-exempting *_analysis.v',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/scratch_analysis.v', ROGUE % ''), 2),
 ('C9  duplicate profile',
  lambda f, u: f.__setitem__('pgg-smc/instances/abelian/zz_dup.v',
     'Definition abel_profile : MonodromyProfile := @MkMonodromyProfile w.\n'), 2),
 ('C10 nested comment hides a declaration',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v',
     '(* draft\n(* see below *)\n' + ROGUE % '' + 'end *)\n'), 0),
 ('C10b real declaration deleted, ghost in nested comment',
  lambda f, u: f.__setitem__('pgg-smc/instances/abelian/abel_profile.v',
     '(* old\n(* note *)\nDefinition abel_profile : MonodromyProfile := @MkMonodromyProfile a.\nend *)\n'), 1),
 ('C11 untracked profile file',
  lambda f, u: u.__setitem__('pgg-smc/instances/s5/rogue.v', ROGUE % ''), 2),
 ('C12 profile outside instances',
  lambda f, u: f.__setitem__('pgg-smc/protocol/other.v', ROGUE % ''), 2),
 ('C13 string literal containing a comment opener',
  lambda f, u: f.__setitem__('pgg-smc/instances/s5/rogue.v',
     'Definition msg := "note (* here".\n'), 0),
]

fails = 0
for name, mutate, expect in CASES:
    build(mutate)
    code, first = run()
    ok = code == expect
    fails += (not ok)
    print('%-4s %-42s exit=%d expected=%d %s  %s'
          % ('PASS' if ok else 'FAIL', name, code, expect,
             '' if ok else '<<<', first[:70]))
shutil.rmtree(BOX, ignore_errors=True)
print('\n%d case(s) failed' % fails)
sys.exit(1 if fails else 0)
