#!/usr/bin/env python3
"""P-G (request 7.7, dependency half): live import DAG of pgg-smc modules,
acyclicity check, and no-cycle check for the proposed adapter placements.

Proposed placements checked:
  A. pgg-smc/protocol/<exec-adapter>.v importing
     {pgg_run, pgg_monodromy_profile, pgg_input_commitment, card_exchange_pismc,
      pgg_interface, pgg_session_types} + pgg_reconstruct.{covering_scheme,
      pgg_sharing_framework, input_encoding}
  B. pgg-smc/security/<dist-adapter>.v importing A + pgg_trace_secrecy.
A new node importing only existing nodes can create a cycle only if some module
in its import closure transitively imports a module that would import the new
node (i.e., an instance). So the check is: nothing in the proposed import
closure lives under instances/.
"""
import os, re, sys
from collections import defaultdict

ROOT = "/Users/cheng-huiweng/Projects/coq/infotheo-pgg"
DIRS = ["pgg-smc/protocol", "pgg-smc/groups", "pgg-smc/security",
        "pgg-smc/reconstruct", "pgg-smc/lib",
        "pgg-smc/instances/pgl27", "pgg-smc/instances/kim2025",
        "pgg-smc/instances/denboer1989", "pgg-smc/instances/s5",
        "pgg-smc/instances/s5x5"]

mod2file = {}
for d in DIRS:
    full = os.path.join(ROOT, d)
    if not os.path.isdir(full):
        continue
    for f in os.listdir(full):
        if f.endswith(".v"):
            mod2file[f[:-2]] = os.path.join(d, f)

req_re = re.compile(r"^\s*(?:From\s+\S+\s+)?Require\s+(?:Import|Export)\s+(.*?)\.\s*$")
edges = defaultdict(set)   # module -> set of imported pgg modules
for mod, rel in mod2file.items():
    with open(os.path.join(ROOT, rel)) as fh:
        for line in fh:
            m = req_re.match(line)
            if m:
                for name in m.group(1).split():
                    if name in mod2file:
                        edges[mod].add(name)

# Kahn topological sort for acyclicity
indeg = {m: 0 for m in mod2file}
for m, ds in edges.items():
    for d in ds:
        indeg[m] = indeg[m]  # noqa
for m in mod2file:
    indeg[m] = 0
for m, ds in edges.items():
    indeg[m] = len(ds)
order, ready = [], [m for m, k in indeg.items() if k == 0]
rev = defaultdict(set)
for m, ds in edges.items():
    for d in ds:
        rev[d].add(m)
while ready:
    n = ready.pop()
    order.append(n)
    for m in rev[n]:
        indeg[m] -= 1
        if indeg[m] == 0:
            ready.append(m)
cyclic = [m for m, k in indeg.items() if k > 0]

def closure(mods):
    seen = set()
    stack = list(mods)
    while stack:
        m = stack.pop()
        if m in seen or m not in mod2file:
            continue
        seen.add(m)
        stack.extend(edges.get(m, ()))
    return seen

def report_placement(label, imports):
    cl = closure(imports)
    bad = sorted(m for m in cl if "instances" in mod2file[m])
    print(f"placement {label}: imports={sorted(imports)}")
    print(f"  closure size={len(cl)}; instance modules in closure: {bad or 'NONE'}")
    print(f"  verdict: {'NO CYCLE POSSIBLE' if not bad else 'CYCLE RISK'}")

print(f"modules scanned: {len(mod2file)}")
print(f"live graph acyclic: {'YES' if not cyclic else 'NO — cyclic: ' + str(cyclic)}")
print()

# directory-level edges (for the response's module analysis)
dir_edges = set()
for m, ds in edges.items():
    dm = os.path.dirname(mod2file[m])
    for d in ds:
        dd = os.path.dirname(mod2file[d])
        if dm != dd:
            dir_edges.add((dm, dd))
print("directory-level edges (importer -> imported):")
for a, b in sorted(dir_edges):
    print(f"  {a} -> {b}")
print()

report_placement("A (protocol exec adapter)",
    ["pgg_run", "pgg_monodromy_profile", "pgg_input_commitment",
     "card_exchange_pismc", "pgg_interface", "pgg_session_types",
     "covering_scheme", "pgg_sharing_framework", "input_encoding"])
report_placement("B (security dist adapter)",
    ["pgg_run", "pgg_monodromy_profile", "pgg_input_commitment",
     "card_exchange_pismc", "pgg_interface", "pgg_session_types",
     "covering_scheme", "pgg_sharing_framework", "input_encoding",
     "pgg_trace_secrecy"])

# sanity: which non-instance modules import instance modules (would block placements)
print()
print("non-instance modules importing instance modules (must be empty):")
viol = [(m, d) for m, ds in edges.items() if "instances" not in mod2file[m]
        for d in ds if "instances" in mod2file[d]]
print(f"  {viol or 'NONE'}")
