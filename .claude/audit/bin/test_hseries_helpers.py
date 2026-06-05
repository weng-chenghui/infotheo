#!/usr/bin/env python3
"""Unit checks for the H-series tag helpers in stage1-regex.py.
Run: .claude/audit/venv/bin/python3 .claude/audit/bin/test_hseries_helpers.py
"""
import importlib.util, sys
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "stage1regex", str(Path(__file__).resolve().parent / "stage1-regex.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def ok(cond, msg):
    if not cond:
        print("FAIL:", msg); sys.exit(1)

# content floor
ok(m._content_floor_ok("abelian words leak no identity", "x"), "floor: real prose passes")
ok(not m._content_floor_ok("x", "word_collapse"), "floor: one char fails")
ok(not m._content_floor_ok("TODO", "x"), "floor: TODO fails")
ok(not m._content_floor_ok("word_collapse", "word_collapse"), "floor: equals identifier fails")

# tag parsing
e = {"preceding_comment": "(** f.  @main security: hides the deck. *)"}
t = m._comment_role_tag(e)
ok(t and t["kind"] == "main" and t["labels"] == ["security"] and t["value"] == "hides the deck.", "main tag")
e = {"preceding_comment": "(** g.  @composes: foo, bar *)"}
t = m._comment_role_tag(e)
ok(t and t["kind"] == "composes" and t["targets"] == ["foo", "bar"], "composes tag")
e = {"preceding_comment": "(** d.  @intent: canonical shuffle action. *)"}
t = m._comment_role_tag(e)
ok(t and t["kind"] == "intent" and t["value"].startswith("canonical"), "intent tag")
ok(m._comment_role_tag({"preceding_comment": "(* plain comment *)"}) is None, "no tag -> None")
print("ok test_hseries_helpers")
