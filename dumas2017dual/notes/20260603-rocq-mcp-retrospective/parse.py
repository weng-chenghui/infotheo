#!/usr/bin/env python3
"""
rocq-mcp usage retrospective — read-only transcript analyzer.

Walks the itp project's Claude Code transcripts (main + subagent), extracts every
rocq-mcp tool_use joined to its tool_result, computes the retrospective metrics,
prints sanity gates, and emits:
  - metrics.tex   LaTeX data macros + pgf-pie / pgfplots coordinate lists
  - metrics.json  full computed metrics (for inspection / appendix)
  - samples.txt   raw failure samples per defect class (for the D4 audit)

Read-only: never writes outside this folder, never touches the transcripts.
"""
import json, glob, os, re, collections, statistics, sys
from datetime import datetime, timezone

ROOT = os.path.expanduser("~/.claude/projects/-Users-cheng-huiweng-Projects-coq-infotheo-itp")
OUT  = os.path.dirname(os.path.abspath(__file__))
PRIORS = {  # rough grep priors from planning, for the sanity gate
    "rocq_check":1300, "rocq_start":315, "rocq_query":150, "rocq_step_multi":114,
    "rocq_compile_file":64, "rocq_compile":29, "rocq_assumptions":21, "rocq_toc":4,
    "rocq_verify":0, "rocq_notations":0,
}

# ---------------------------------------------------------------- error taxonomy
# Each rule: (compiled regex, display category, defect class).  First match wins.
CLASS_RULES = [
    (re.compile(r"No node at point", re.I),                          "No node at point",            "tool-defect"),
    (re.compile(r"timed out after", re.I),                           "Timeout",                     "tool-defect/infra"),
    (re.compile(r"Restart cannot be used through the Load", re.I),   "Restart-through-Load",        "tool-defect/edge"),
    (re.compile(r"Theorem_not_found|was not found in the current",re.I),"Reference/theorem not found","ambiguous"),
    (re.compile(r"Unable to unambiguously interpret", re.I),         "Notation ambiguity",          "operator-usage"),
    (re.compile(r"Expected a single focused goal but \d+", re.I),    "Focus discipline",            "operator-usage"),
    (re.compile(r"[Ss]yntax error|Illegal application|expected", re.I),"Syntax/parse",              "operator-usage"),
    (re.compile(r"Cannot apply|Unable to unify|not.*convertible|"
                r"goals?.*(remain|are focused)|not finished|"
                r"No such (assumption|hypothesis)|no.*goals", re.I),  "Proof-state (apply/unify/unfinished)","legitimate-proof-state"),
]
# Human-readable labels for Claude's auto-generated session slugs (this corpus).
# (short axis label, full description) — derived from each session's plan / first
# prompt / dominant files+theorems. Unknown slugs fall back to the raw slug.
SESSION_LABELS = {
    "sprightly-finding-robin":
        ("DSDP secrecy + entropy",
         "DSDP Alice-secrecy: V2-aware SSProve chain, concrete corollaries, and entropy-form bound "
         "(dsdp\\_alice\\_secrecy\\_indcpa, secrecy\\_random\\_guess)."),
    "read-plan-claude-plans-sprightly-finding-vast-coral":
        ("DSDP secrecy (PISMC)",
         "Continuation of the secrecy plan: the PISMC variant of the chain "
         "(game\\_real\\_eq\\_pismc, dsdp\\_alice\\_secrecy\\_pismc, entropy\\_ge\\_bound\\_pismc)."),
    "transient-juggling-flurry":
        ("DSDP IND-CPA shell/trace",
         "DSDP IND-CPA shell-link and trace-bridge lemmas "
         "(valid\\_boolean\\_shell\\_link, log\\_id, alice\\_trace\\_eq\\_concrete)."),
    "so-according-to-what-fluttering-goose":
        ("DSDP Charlie game-equiv",
         "DSDP Charlie game-equivalence (game\\_real\\_equiv\\_charlie\\_real); "
         "session also covered merged-flow workflow planning."),
    "focus-on-the-rstep-squishy-alpaca":
        ("SMC interp. soundness",
         "SMC interpreter rstep soundness port between branches (smc/smc\\_interpreter\\_sound.v)."),
    "(no slug)":
        ("main-thread / misc",
         "Main-thread direct calls with no recorded session slug."),
}

def classify(err):
    if not err:
        return ("Unknown (no error text)", "ambiguous")
    for rx, cat, dc in CLASS_RULES:
        if rx.search(err):
            return (cat, dc)
    return ("Other", "ambiguous")

# ---------------------------------------------------------------- helpers
def parse_ts(s):
    if not s or not isinstance(s, str):
        return None
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(timezone.utc)
    except Exception:
        return None

def decode_result(c):
    """tool_result content -> parsed dict (or None). content is str or list-of-{text}."""
    if isinstance(c, str):
        txt = c
    elif isinstance(c, list):
        txt = "".join(x.get("text", "") for x in c if isinstance(x, dict))
    else:
        return None
    txt = txt.strip()
    if not txt:
        return None
    try:
        v = json.loads(txt)
        return v if isinstance(v, dict) else {"_raw": v}
    except Exception:
        return {"_unparsed": txt[:400]}

def result_success(parsed, tool):
    """Return (status, error_text). status in {True, False, None}."""
    if parsed is None:
        return (None, None)
    if "_unparsed" in parsed:
        return (None, parsed["_unparsed"])
    s = parsed.get("success", None)
    err = parsed.get("error") or parsed.get("failed_command") or parsed.get("hint")
    if s is None:
        # rocq_query etc. may omit `success`; infer from presence of error text
        if err:
            return (False, err)
        # treat a populated, error-free query result as success
        return (True, None)
    return (bool(s), err if not s else None)

# ---------------------------------------------------------------- ingest
files = sorted(glob.glob(os.path.join(ROOT, "**", "*.jsonl"), recursive=True))
n_main = sum(1 for f in files if "/subagents/" not in f)
n_sub  = sum(1 for f in files if "/subagents/" in f)

uses = {}          # call_id -> dict(tool, file, is_subagent, sessionId, agentName, ts, line_no)
results = {}       # call_id -> dict(parsed, ts, file)
file_agent = collections.Counter()  # (file)->agentName majority helper
session_title = {}                  # sessionId -> aiTitle
dup_uses = 0
bad_lines = 0

def attr_str(v):
    if v is None:
        return None
    return v if isinstance(v, str) else json.dumps(v)[:40]

for fp in files:
    is_sub = "/subagents/" in fp
    # pre-scan the file's session slug + agent type (constant within a subagent file)
    local_slug = None
    local_attr = None
    with open(fp, "r", errors="replace") as f:
        for ln, line in enumerate(f):
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except Exception:
                bad_lines += 1
                continue
            if rec.get("slug") and local_slug is None:
                local_slug = rec["slug"]
            aa = attr_str(rec.get("attributionAgent"))
            if aa and local_attr is None:
                local_attr = aa
            sid = rec.get("sessionId")
            ts = parse_ts(rec.get("timestamp"))
            msg = rec.get("message")
            content = msg.get("content") if isinstance(msg, dict) else None
            if not isinstance(content, list):
                continue
            for c in content:
                if not isinstance(c, dict):
                    continue
                typ = c.get("type")
                if typ == "tool_use" and str(c.get("name", "")).startswith("mcp__rocq-mcp__"):
                    cid = c.get("id")
                    if cid in uses:
                        dup_uses += 1
                        continue
                    uses[cid] = dict(
                        tool=c["name"].split("mcp__rocq-mcp__")[-1],
                        file=fp, is_subagent=is_sub, sessionId=sid,
                        slug=rec.get("slug"), attr=aa,
                        ts=ts, line_no=ln, input=c.get("input") or {},
                    )
                elif typ == "tool_result":
                    tid = c.get("tool_use_id")
                    if tid and tid not in results:
                        results[tid] = dict(parsed=decode_result(c.get("content")),
                                             ts=ts, file=fp)
    # backfill the per-file constants for any tool_use that lacked them on its own line
    for u in uses.values():
        if u["file"] == fp:
            if not u["slug"]:
                u["slug"] = local_slug
            if not u["attr"]:
                u["attr"] = local_attr if is_sub else "(main thread, direct)"

# ---------------------------------------------------------------- join + records
records = []
for cid, u in uses.items():
    r = results.get(cid)
    parsed = r["parsed"] if r else None
    status, err = result_success(parsed, u["tool"])
    lat = None
    if r and r["ts"] and u["ts"]:
        lat = (r["ts"] - u["ts"]).total_seconds()
    records.append(dict(
        cid=cid, tool=u["tool"], is_subagent=u["is_subagent"], file=u["file"],
        sessionId=u["sessionId"], slug=u["slug"], attr=u["attr"],
        ts=u["ts"], line_no=u["line_no"], input=u["input"],
        matched=(r is not None), parsed=parsed, status=status, err=err, latency=lat,
    ))

records.sort(key=lambda x: (x["ts"] or datetime.min.replace(tzinfo=timezone.utc), x["line_no"]))

# ---------------------------------------------------------------- metrics
total = len(records)
by_tool = collections.defaultdict(lambda: collections.Counter())
for r in records:
    t = r["tool"]
    by_tool[t]["n"] += 1
    if not r["matched"]:
        by_tool[t]["unmatched"] += 1
    elif r["status"] is True:
        by_tool[t]["succ"] += 1
    elif r["status"] is False:
        by_tool[t]["fail"] += 1
    else:
        by_tool[t]["unknown"] += 1

n_subc = sum(1 for r in records if r["is_subagent"])
n_mainc = total - n_subc

# failure classification (D2/D4)
err_cat = collections.Counter()
defect_cat = collections.Counter()
tool_cat = collections.defaultdict(collections.Counter)   # tool -> error-category counts
tool_dc = collections.defaultdict(collections.Counter)    # tool -> defect-class counts
samples = collections.defaultdict(list)
for r in records:
    if r["status"] is False:
        cat, dc = classify(r["err"])
        err_cat[cat] += 1
        defect_cat[dc] += 1
        tool_cat[r["tool"]][cat] += 1
        tool_dc[r["tool"]][dc] += 1
        if len(samples[dc]) < 15:
            samples[dc].append((r["tool"], (r["err"] or "")[:200]))

# timeouts (D8) & force_restart (D9)
timeouts = collections.Counter()
force_restart = 0
for r in records:
    if r["status"] is False and r["err"] and re.search(r"timed out after", r["err"], re.I):
        timeouts[r["tool"]] += 1
    if isinstance(r["input"], dict) and r["input"].get("force_restart") is True:
        force_restart += 1

# daily activity (D15)
daily = collections.defaultdict(lambda: [0, 0])  # date -> [succ, fail]
for r in records:
    if r["ts"]:
        d = r["ts"].date().isoformat()
        if r["status"] is True:
            daily[d][0] += 1
        elif r["status"] is False:
            daily[d][1] += 1

# latency per tool (D14)  — drop negatives / >600s outliers
lat_by_tool = collections.defaultdict(list)
lat_dropped = 0
for r in records:
    if r["latency"] is not None:
        if 0 <= r["latency"] <= 600:
            lat_by_tool[r["tool"]].append(r["latency"])
        else:
            lat_dropped += 1
def quant(xs, q):
    if not xs:
        return 0.0
    xs = sorted(xs)
    i = min(len(xs) - 1, int(q * len(xs)))
    return xs[i]

# per-session breakdown by slug (D16) — "for what session, in short"
sess_ct = collections.defaultdict(lambda: [0, 0])  # slug -> [n, succ]
for r in records:
    nm = r["slug"] or "(no slug)"
    sess_ct[nm][0] += 1
    if r["status"] is True:
        sess_ct[nm][1] += 1
top_sess = sorted(sess_ct.items(), key=lambda kv: -kv[1][0])[:12]

# per agent-TYPE breakdown by attributionAgent (D3 enrichment)
attr_ct = collections.defaultdict(lambda: [0, 0])  # type -> [n, succ]
for r in records:
    nm = r["attr"] or "(unattributed)"
    attr_ct[nm][0] += 1
    if r["status"] is True:
        attr_ct[nm][1] += 1
top_attr = sorted(attr_ct.items(), key=lambda kv: -kv[1][0])

# recovery patterns (D5): next call in the same agent timeline (= one subagent file) after a failure
seqs = collections.defaultdict(list)
for r in records:
    seqs[r["file"]].append(r)
recovery = collections.Counter()
for key, seq in seqs.items():
    seq.sort(key=lambda x: (x["ts"] or datetime.min.replace(tzinfo=timezone.utc), x["line_no"]))
    for i, r in enumerate(seq):
        if r["status"] is False:
            nxt = seq[i + 1] if i + 1 < len(seq) else None
            if nxt is None:
                recovery["abandoned (no further rocq call)"] += 1
            else:
                inp = nxt["input"] if isinstance(nxt["input"], dict) else {}
                if inp.get("force_restart") is True:
                    recovery["force_restart"] += 1
                elif inp.get("from_state") is not None:
                    recovery["retry from_state"] += 1
                elif nxt["tool"] != r["tool"]:
                    recovery["switched tool"] += 1
                else:
                    recovery["different input, same tool"] += 1

# stuck episodes (D6): >=3 consecutive failures within one agent timeline,
# broken on target file/theorem change so unrelated work isn't merged into one run.
def target_of(r):
    inp = r["input"] if isinstance(r["input"], dict) else {}
    return inp.get("file") or inp.get("theorem") or inp.get("name")
stuck = []
for fpath, seq in seqs.items():
    label = (seq[0]["slug"] or seq[0]["attr"] or os.path.basename(fpath))
    run = 0
    cur_t = object()
    for r in seq:
        if r["status"] is False and target_of(r) == cur_t:
            run += 1
        elif r["status"] is False:
            if run >= 3:
                stuck.append((label, run))
            run = 1
            cur_t = target_of(r)
        else:
            if run >= 3:
                stuck.append((label, run))
            run = 0
            cur_t = object()
    if run >= 3:
        stuck.append((label, run))
stuck.sort(key=lambda x: -x[1])

# step_multi per-tactic (D12)
sm_call_succ = sm_call_n = sm_tac_succ = sm_tac_n = 0
for r in records:
    if r["tool"] == "rocq_step_multi" and isinstance(r["parsed"], dict):
        sm_call_n += 1
        if r["parsed"].get("success"):
            sm_call_succ += 1
        for t in r["parsed"].get("results", []) or []:
            if isinstance(t, dict) and "success" in t:
                sm_tac_n += 1
                if t["success"]:
                    sm_tac_succ += 1

matched = sum(1 for r in records if r["matched"])
unmatched = total - matched
succ_all = sum(1 for r in records if r["status"] is True)
fail_all = sum(1 for r in records if r["status"] is False)
unknown_all = sum(1 for r in records if r["status"] is None and r["matched"])

# ---------------------------------------------------------------- sanity gates
print("=" * 64)
print("SANITY GATES")
print("=" * 64)
print(f"transcripts: {len(files)}  (main {n_main} + subagent {n_sub})")
print(f"bad json lines: {bad_lines}   duplicate call_ids collapsed: {dup_uses}")
print(f"total rocq-mcp calls (deduped): {total}   [expect ~1997]")
print(f"  main-thread: {n_mainc}   subagent: {n_subc}  (subagent share {100*n_subc/max(1,total):.1f}%)")
print(f"  matched={matched}  unmatched={unmatched}  | success={succ_all} fail={fail_all} unknown={unknown_all}")
print(f"  latency outliers dropped (<0 or >600s): {lat_dropped}")
print("per-tool [n / prior]:")
ok = True
for t, prior in sorted(PRIORS.items(), key=lambda kv: -kv[1]):
    n = by_tool[t]["n"]
    flag = "" if abs(n - prior) <= max(20, 0.2 * prior) else "  <-- DIVERGES"
    if flag:
        ok = False
    print(f"   {t:20s} n={n:5d}  prior={prior:5d}{flag}")
assert n_mainc + n_subc == total, "provenance split must sum to total"
assert n_subc / max(1, total) > 0.90, "subagent share must exceed 90% (recursion check)"
print(f"GATE subagent>90%: PASS   GATE provenance-sum: PASS   per-tool priors: {'PASS' if ok else 'CHECK'}")

# ---------------------------------------------------------------- emit metrics.tex
def texesc(s):
    return s.replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("&", r"\&").replace("%", r"\%").replace("#", r"\#")

def pielabel(s, n=20):
    # pgf-pie splits slices on commas and "/", so strip those + parens; hyphenate underscores
    s = s.replace(",", " ").replace("(", "").replace(")", "").replace("/", "-").replace("_", "-")
    s = " ".join(s.split())
    return (s[:n] + "..") if len(s) > n + 2 else s

def pct(a, b):
    return 100.0 * a / b if b else 0.0

lines = []
A = lines.append
A("% AUTO-GENERATED by parse.py — do not edit by hand.")
A(f"\\newcommand{{\\Ntotal}}{{{total}}}")
A(f"\\newcommand{{\\Ntranscripts}}{{{len(files)}}}")
A(f"\\newcommand{{\\Nmain}}{{{n_main}}}")
A(f"\\newcommand{{\\Nsub}}{{{n_sub}}}")
A(f"\\newcommand{{\\Nmaincalls}}{{{n_mainc}}}")
A(f"\\newcommand{{\\Nsubcalls}}{{{n_subc}}}")
A(f"\\newcommand{{\\Subpct}}{{{pct(n_subc,total):.1f}}}")
A(f"\\newcommand{{\\Nmatched}}{{{matched}}}")
A(f"\\newcommand{{\\Nunmatched}}{{{unmatched}}}")
A(f"\\newcommand{{\\Nsucc}}{{{succ_all}}}")
A(f"\\newcommand{{\\Nfail}}{{{fail_all}}}")
A(f"\\newcommand{{\\Nunknown}}{{{unknown_all}}}")
A(f"\\newcommand{{\\Succpct}}{{{pct(succ_all, succ_all+fail_all):.1f}}}")
A(f"\\newcommand{{\\Forcerestart}}{{{force_restart}}}")
A(f"\\newcommand{{\\Latdropped}}{{{lat_dropped}}}")
A(f"\\newcommand{{\\Dupcollapsed}}{{{dup_uses}}}")

# defect-class headline numbers
defect_total = sum(defect_cat.values())
def dc_get(k): return defect_cat.get(k, 0)
tool_defect = dc_get("tool-defect") + dc_get("tool-defect/infra") + dc_get("tool-defect/edge")
A(f"\\newcommand{{\\Ftooldefect}}{{{tool_defect}}}")
A(f"\\newcommand{{\\Fusage}}{{{dc_get('operator-usage')}}}")
A(f"\\newcommand{{\\Flegit}}{{{dc_get('legitimate-proof-state')}}}")
A(f"\\newcommand{{\\Fambig}}{{{dc_get('ambiguous')}}}")
A(f"\\newcommand{{\\Ffail}}{{{defect_total}}}")
A(f"\\newcommand{{\\Ftooldefectpct}}{{{pct(tool_defect,defect_total):.1f}}}")
A(f"\\newcommand{{\\Flegitpct}}{{{pct(dc_get('legitimate-proof-state'),defect_total):.1f}}}")

# headline error counts for prose
A(f"\\newcommand{{\\Nnode}}{{{err_cat.get('No node at point',0)}}}")
A(f"\\newcommand{{\\Ntimeout}}{{{sum(timeouts.values())}}}")
A(f"\\newcommand{{\\Qbroken}}{{{by_tool['rocq_query']['fail']}}}")
A(f"\\newcommand{{\\Qtotal}}{{{by_tool['rocq_query']['n']}}}")
A(f"\\newcommand{{\\Asmbroken}}{{{by_tool['rocq_assumptions']['fail']}}}")
A(f"\\newcommand{{\\Asmtotal}}{{{by_tool['rocq_assumptions']['n']}}}")
A(f"\\newcommand{{\\Checkn}}{{{by_tool['rocq_check']['n']}}}")
A(f"\\newcommand{{\\Checksucc}}{{{pct(by_tool['rocq_check']['succ'], by_tool['rocq_check']['succ']+by_tool['rocq_check']['fail']):.0f}}}")
A(f"\\newcommand{{\\Checkmed}}{{{quant(lat_by_tool.get('rocq_check',[]),0.5):.3f}}}")
A(f"\\newcommand{{\\Startptimeout}}{{{quant(lat_by_tool.get('rocq_start',[]),0.9):.1f}}}")
# step_multi
A(f"\\newcommand{{\\SMcallrate}}{{{pct(sm_call_succ,sm_call_n):.0f}}}")
A(f"\\newcommand{{\\SMtacrate}}{{{pct(sm_tac_succ,sm_tac_n):.0f}}}")
A(f"\\newcommand{{\\SMtacn}}{{{sm_tac_n}}}")

# pgf-pie needs LITERAL data inside a tikzpicture (it cannot take a macro arg),
# so each pie is emitted as a complete self-contained chart macro.
def pie_macro(name, data, colors, radius=2.0):
    return (f"\\newcommand{{\\{name}}}{{\\begin{{tikzpicture}}"
            f"\\pie[radius={radius},text=legend,sum=auto,font=\\scriptsize,color={{{colors}}}]"
            f"{{{data}}}\\end{{tikzpicture}}}}")

# Chart 1: per-tool volume pie
def short(t): return t.replace("rocq_", "").replace("_", "-")
tool_order = sorted(by_tool.items(), key=lambda kv: -kv[1]["n"])
pie1 = ", ".join(f"{by_tool[t]['n']}/{short(t)}" for t, _ in tool_order if by_tool[t]["n"] > 0)
A(pie_macro("ChartToolVolPie", pie1,
            "blue!60,cyan!60,teal!60,olive!60,orange!60,red!50,violet!50,gray!50", radius=2.2))

# Chart 2: failure-classification pie (semantic colors)
pie2 = ", ".join(f"{v}/{texesc(k)}" for k, v in
                 [("tool-defect", tool_defect), ("operator-usage", dc_get("operator-usage")),
                  ("legitimate", dc_get("legitimate-proof-state")), ("ambiguous", dc_get("ambiguous"))] if v > 0)
A(pie_macro("ChartFailPie", pie2, "red!65,orange!70,green!55,black!25", radius=2.0))

def ticks(n):  # "0,1,2,...,n-1" for pgfplots xtick/ytick
    return ",".join(str(i) for i in range(n))

# Chart 3: error taxonomy bar coords (symbolic x via separate label macro)
ec = err_cat.most_common()
A(f"\\newcommand{{\\ErrBarCoords}}{{{' '.join(f'({i},{v})' for i,(k,v) in enumerate(ec))}}}")
A(f"\\newcommand{{\\ErrBarLabels}}{{{','.join(texesc(k) for k,_ in ec)}}}")
A(f"\\newcommand{{\\ErrBarTick}}{{{ticks(len(ec))}}}")

# Chart 4: daily timeline stacked coords
days = sorted(daily.keys())
A(f"\\newcommand{{\\DaySuccCoords}}{{{' '.join(f'({i},{daily[d][0]})' for i,d in enumerate(days))}}}")
A(f"\\newcommand{{\\DayFailCoords}}{{{' '.join(f'({i},{daily[d][1]})' for i,d in enumerate(days))}}}")
A(f"\\newcommand{{\\DayLabels}}{{{','.join(d[5:] for d in days)}}}")  # MM-DD
A(f"\\newcommand{{\\DayTick}}{{{ticks(len(days))}}}")

# Chart 5: per-tool latency median/p90 coords
lat_tools = [t for t, _ in tool_order if lat_by_tool.get(t)]
A(f"\\newcommand{{\\LatMedCoords}}{{{' '.join(f'({i},{quant(lat_by_tool[t],0.5):.2f})' for i,t in enumerate(lat_tools))}}}")
A(f"\\newcommand{{\\LatPCoords}}{{{' '.join(f'({i},{quant(lat_by_tool[t],0.9):.2f})' for i,t in enumerate(lat_tools))}}}")
A(f"\\newcommand{{\\LatLabels}}{{{','.join(short(t) for t in lat_tools)}}}")
A(f"\\newcommand{{\\LatTick}}{{{ticks(len(lat_tools))}}}")

# Chart 6: per-session breakdown (slug) horizontal bar (count), success rate annotated
def trim(nm, n=30):
    # no "..." marker: three dots trip pgfplots' foreach dots-range parser under /.expanded
    return nm[:n] if len(nm) > n + 1 else nm
ss_labels = [texesc(SESSION_LABELS.get(nm, (trim(nm, 24), nm))[0]) for nm, _ in top_sess]
A(f"\\newcommand{{\\SessBarCoords}}{{{' '.join(f'({v[0]},{i})' for i,(nm,v) in enumerate(top_sess))}}}")
A(f"\\newcommand{{\\SessLabels}}{{{','.join(ss_labels)}}}")
A(f"\\newcommand{{\\SessTick}}{{{ticks(len(top_sess))}}}")
# legend mapping each readable label back to its raw session slug + a description
leg = []
for nm, v in top_sess:
    sh, full = SESSION_LABELS.get(nm, (trim(nm, 24), nm))
    leg.append(f"\\item \\textbf{{{texesc(sh)}}} "
               f"(\\texttt{{{texesc(nm)}}}, {v[0]} calls, {pct(v[1],v[0]):.0f}\\% ok): {full}")
A("\\newcommand{\\SessLegend}{" + " ".join(leg) + "}")
# success-rate annotation nodes for the session bars
sess_anno = " ".join(
    f"\\node[anchor=west,font=\\tiny] at (axis cs:{v[0]},{i}) {{{pct(v[1],v[0]):.0f}\\%}};"
    for i, (nm, v) in enumerate(top_sess))
A(f"\\newcommand{{\\SessAnno}}{{{sess_anno}}}")

# Chart 8: calls by agent type (attributionAgent) pie
attr_pie = ", ".join(f"{v[0]}/{pielabel(nm)}" for nm, v in top_attr if v[0] > 0)
A(pie_macro("ChartAttrPie", attr_pie, "blue!55,orange!65,gray!45", radius=1.9))
attr_rows = " ".join(f"{texesc(nm)} & {v[0]} & {pct(v[1],v[0]):.1f}\\% \\\\" for nm, v in top_attr)
A(f"\\newcommand{{\\AttrTableRows}}{{{attr_rows}}}")

# Chart 7: per-tool success-rate bar (matched only)
sr_tools = [t for t, _ in tool_order if (by_tool[t]['succ'] + by_tool[t]['fail']) > 0]
A(f"\\newcommand{{\\SuccRateCoords}}{{{' '.join(f'({i},{pct(by_tool[t][chr(115)+chr(117)+chr(99)+chr(99)], by_tool[t][chr(115)+chr(117)+chr(99)+chr(99)]+by_tool[t][chr(102)+chr(97)+chr(105)+chr(108)]):.1f})' for i,t in enumerate(sr_tools))}}}")
A(f"\\newcommand{{\\SuccRateLabels}}{{{','.join(short(t) for t in sr_tools)}}}")
A(f"\\newcommand{{\\SuccRateTick}}{{{ticks(len(sr_tools))}}}")

# table rows: per tool
tool_rows = []
for t, c in tool_order:
    sr = pct(c['succ'], c['succ'] + c['fail'])
    med = quant(lat_by_tool.get(t, []), 0.5)
    tool_rows.append(f"{texesc(short(t))} & {c['n']} & {c['succ']} & {c['fail']} & {c['unknown']} & {c['unmatched']} & {sr:.1f}\\% & {med:.2f} \\\\")
A(f"\\newcommand{{\\ToolTableRows}}{{{chr(10).join(tool_rows)}}}")

# recovery table
rec_rows = " ".join(f"{texesc(k)} & {v} \\\\" for k, v in recovery.most_common())
A(f"\\newcommand{{\\RecoveryRows}}{{{rec_rows}}}")
A(f"\\newcommand{{\\Stuckcount}}{{{len(stuck)}}}")
A(f"\\newcommand{{\\Stuckmax}}{{{stuck[0][1] if stuck else 0}}}")

with open(os.path.join(OUT, "metrics.tex"), "w") as f:
    f.write("\n".join(lines) + "\n")

# ---------------------------------------------------------------- metrics.json + samples
metrics = dict(
    total=total, main=n_mainc, sub=n_subc, matched=matched, unmatched=unmatched,
    succ=succ_all, fail=fail_all, unknown=unknown_all,
    by_tool={t: dict(c) for t, c in by_tool.items()},
    err_cat=dict(err_cat), defect_cat=dict(defect_cat),
    timeouts=dict(timeouts), force_restart=force_restart,
    daily={d: daily[d] for d in days},
    lat_median={t: round(quant(v, 0.5), 3) for t, v in lat_by_tool.items()},
    lat_p90={t: round(quant(v, 0.9), 3) for t, v in lat_by_tool.items()},
    top_sessions=[(nm, v) for nm, v in top_sess],
    by_agent_type=[(nm, v) for nm, v in top_attr],
    recovery=dict(recovery), stuck_top=stuck[:15],
    step_multi=dict(call_n=sm_call_n, call_succ=sm_call_succ, tac_n=sm_tac_n, tac_succ=sm_tac_succ),
    tool_cat={t: dict(c) for t, c in tool_cat.items()},
    tool_defect={t: dict(c) for t, c in tool_dc.items()},
)
with open(os.path.join(OUT, "metrics.json"), "w") as f:
    json.dump(metrics, f, indent=2, default=str)

with open(os.path.join(OUT, "samples.txt"), "w") as f:
    for dc in ["tool-defect", "tool-defect/infra", "tool-defect/edge", "operator-usage",
               "legitimate-proof-state", "ambiguous"]:
        f.write(f"\n===== {dc} =====\n")
        for tool, e in samples.get(dc, []):
            f.write(f"  [{tool}] {e}\n")

print("\nwrote metrics.tex, metrics.json, samples.txt")
print("error categories:", dict(err_cat))
print("defect classes:", dict(defect_cat))
print("recovery:", dict(recovery))
print("by agent type:", [(nm, v[0]) for nm, v in top_attr])
print("top sessions:", [(nm, v[0]) for nm, v in top_sess[:8]])
print("latency median by tool (s):", {t: round(quant(v,0.5),2) for t,v in lat_by_tool.items()})
print("latency p90 by tool (s):", {t: round(quant(v,0.9),2) for t,v in lat_by_tool.items()})
print("stuck episodes (top 8):", stuck[:8])
print("\nper-tool error categories:")
for t in ["rocq_check","rocq_start","rocq_query","rocq_assumptions","rocq_compile_file","rocq_step_multi"]:
    if tool_cat.get(t):
        print(f"   {t:18s} {dict(tool_cat[t])}")
