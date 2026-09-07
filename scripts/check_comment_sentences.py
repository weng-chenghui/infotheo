#!/usr/bin/env python3
"""Statement comments: at most two prose sentences of at most LIMIT words.

A statement comment is the (* ... *) block ending on the line just above a
Definition / Lemma / Theorem / Corollary / Fact / Let / Canonical / Variant
/ Record / Structure / Notation / Local Notation keyword.

The block is split into sentences at a period, question mark or
exclamation mark followed by white space and a capital letter, a backquote,
a bracket, a bar or a paren.  A sentence is a DISPLAY when it starts with
one of ` [ | ( or holds fewer than three prose words beside identifiers or
operators; a displayed line such as
    |accept D G0 - accept D G2| <= eps_bob D + eps_charlie D
is therefore not counted as a sentence and its length is not measured.  A
prose word is a token made of letters, apostrophes and hyphens only, so
identifiers with digits or underscores (eps_bob, G0, u1) and operators do
not count toward the word limit.

Usage:
    check_comment_sentences.py [--limit N] [--max-sentences M] FILE.v ...
    check_comment_sentences.py [--limit N]            # staged .v files

Exit status 1 when any statement comment has more than M prose sentences
or a prose sentence of more than N prose words; 0 otherwise.  One entry is
printed per offending comment, worst first.
"""
import re
import subprocess
import sys

KW = re.compile(
    r'^\s*(Definition|Lemma|Theorem|Corollary|Fact|Let|Canonical|Variant'
    r'|Record|Structure|Local Notation|Notation)\s+'
    r'([A-Za-z_][A-Za-z0-9_\']*|"[^"]*")')
SPLIT = re.compile(r'(?<=[.!?])\s+(?=[A-Z`\[|(])')
PROSE = re.compile(r"^[A-Za-z][A-Za-z'\-]*[.,;:!?]?$")
DISPLAY_START = ('`', '[', '|', '(')


def parse_args(argv):
    limit, max_sentences, files = 20, 2, []
    i = 0
    while i < len(argv):
        if argv[i] == '--limit':
            limit = int(argv[i + 1]); i += 2
        elif argv[i] == '--max-sentences':
            max_sentences = int(argv[i + 1]); i += 2
        else:
            files.append(argv[i]); i += 1
    if not files:
        out = subprocess.run(
            ['git', 'diff', '--cached', '--name-only', '--diff-filter=ACMR'],
            capture_output=True, text=True, check=False).stdout
        files = [f for f in out.split('\n') if f.endswith('.v')]
    return limit, max_sentences, files


def header_blocks(lines):
    """Yield (line_number_of_keyword, identifier, comment_text)."""
    for i, line in enumerate(lines):
        m = KW.match(line)
        if not m or i == 0 or not lines[i - 1].rstrip().endswith('*)'):
            continue
        j, depth = i - 1, 0
        while j >= 0:
            depth += lines[j].count('*)') - lines[j].count('(*')
            if depth <= 0 and '(*' in lines[j]:
                break
            j -= 1
        block = ' '.join(l.strip() for l in lines[j:i]).strip()
        if block.startswith('(*'):
            block = block[2:]
        if block.endswith('*)'):
            block = block[:-2]
        yield i + 1, m.group(2), block.strip()


def prose_words(sentence):
    return [t for t in sentence.split() if PROSE.match(t)]


def is_display(sentence):
    """A displayed formula: opens with a math delimiter, or is mostly
    non-prose tokens (fewer than three prose words beside at least one
    identifier or operator).  A short all-prose sentence is prose."""
    s = sentence.lstrip()
    if s.startswith(DISPLAY_START):
        return True
    tokens = s.split()
    prose = prose_words(s)
    return len(prose) < 3 and len(tokens) > len(prose)


def main(argv):
    limit, max_sentences, files = parse_args(argv)
    rows = []
    for path in files:
        try:
            lines = open(path, encoding='utf-8').read().split('\n')
        except OSError:
            continue
        for ln, name, block in header_blocks(lines):
            sents = [s for s in SPLIT.split(block) if s.strip()]
            prose = [s for s in sents if not is_display(s)]
            if not prose:
                continue
            longest = max(prose, key=lambda s: len(prose_words(s)))
            n = len(prose_words(longest))
            if n > limit or len(prose) > max_sentences:
                rows.append((len(prose) > max_sentences, n, len(prose),
                             path, ln, name, longest))
    rows.sort(reverse=True)
    for too_many, n, ns, path, ln, name, s in rows:
        why = (f'{ns} prose sentences' if too_many
               else f'longest sentence {n} words')
        print(f'{path}:{ln}: {name}: {why}')
        print(f'    {s}')
    if rows:
        print(f'{len(rows)} statement comments break the limit '
              f'({max_sentences} prose sentences, {limit} words each)')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
