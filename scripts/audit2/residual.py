#!/usr/bin/env python3
"""Compile and verify the record-based portion of the remaining regional audit checks."""
import argparse
from collections import Counter, defaultdict
import csv
import json
from pathlib import Path
import re
import sys
import time

from audit import ROOT, Failure, closure, imports_of, write_json
from coverage import load_db

MAPPING = ROOT / "research/audit-review/stage2-mapping.csv"
LAYOUT = ROOT / "scripts/refactor/targets/bulk-kl-module-map.json"
NAME = r"SerrePositivity(?:\.[\w'!?]+)+"
IMPORT = re.compile(r"(?m)^[ \t]*(?:public )?(?:meta )?import (?:all )?(" + NAME + r")\b")
PRINT = re.compile(r"(?m)^[ \t]*(#check[ \t]+@?|#print[ \t]+axioms[ \t]+)(" + NAME + r")[ \t]*$")
PREFIX = re.compile(r"let oldAuditPrefix\d+ := `(" + NAME + r")")
QUOTED = re.compile(r"`(" + NAME + r")")
SOURCE_TOKEN = re.compile(r'/-|--[^\n]*|"(?:[^"\\]|\\.)*"|«[^»]*»')
BLOCK_TOKEN = re.compile(r"/-|-/")


def under(name, prefix):
    return name == prefix or name.startswith(prefix + ".")


def named_array(source, name):
    result = re.search(r"\blet " + re.escape(name) + r"[^\n]*:=\s*#\[(.*?)\]", source, re.S)
    if result is None:
        raise Failure(f"missing legacy array {name}")
    values = sorted(set(QUOTED.findall(result[1])))
    if not values:
        raise Failure(f"empty legacy array {name}")
    return values


def command_text(source):
    """Mask comments and strings without changing offsets or line numbers."""
    fragments = []
    start = 0
    cursor = 0
    depth = 0
    blank = re.compile(r"[^\n]")
    while token := (BLOCK_TOKEN if depth else SOURCE_TOKEN).search(source, cursor):
        cursor = token.end()
        spelling = token[0]
        if depth == 0:
            fragments.append(source[start:token.start()])
            if spelling != "/-":
                fragments.append(blank.sub(" ", spelling))
                start = token.end()
                continue
            start = token.start()
        if spelling == "/-":
            depth += 1
        elif spelling == "-/":
            depth -= 1
            if depth == 0:
                fragments.append(blank.sub(" ", source[start:token.end()]))
                start = token.end()
    fragments.append(blank.sub(" ", source[start:]) if depth else source[start:])
    return "".join(fragments)


def plain_names(db, scope, source, path):
    selected, remaining, displays = {}, [], []
    for match in PRINT.finditer(command_text(source)):
        name = match[2]
        line = source.count("\n", 0, match.start(1)) + 1
        matches = [(m, name, public) for m, public in db.execute(
            "SELECT module,public FROM decl WHERE name=?", (name,)) if m in scope]
        if len(matches) != 1:
            remaining.append([path, line, name, len(matches)])
            continue
        m, n, public = matches[0]
        selected[m, n] = bool(public)
        displays.append([path, line, m, n, match[1].startswith("#print")])
    return selected, remaining, displays


def scopes_for_script(path, source, graph, layout):
    roots = sorted(set(IMPORT.findall(source)))
    scope = closure(graph, roots)
    scopes = []
    for prefix in PREFIX.findall(source):
        destinations = sorted({new for old, new in layout.items() if under(old, prefix)})
        scopes.append(dict(kind="scope", path=path, roots=roots, prefix=prefix, destinations=destinations))
    if path == "scripts/audit_homotopical_general_tools.lean":
        scopes.append(dict(kind="boundary", path=path, roots=roots,
                           required=named_array(source, "required"), forbidden=named_array(source, "forbidden"),
                           forbidden_prefixes=["SerrePositivity.HomotopicalAlgebra.Rectification"]))
    if path == "scripts/audit_infinity_f1.lean":
        target = source.split('throwError "Ind-S (8): forbidden direct KST import', 1)
        if len(target) != 2:
            raise Failure(f"missing Ind-S (8) condition in {path}")
        modules = named_array("let modules := #[" + target[0].rsplit("let modules := #[", 1)[1], "modules")
        scopes.append(dict(kind="direct-import", path=path, modules=modules, forbidden="SerrePositivity.KST"))
        scopes.append(dict(kind="type-ref-substring", path=path, modules=modules, forbidden="ModelCategory"))
    return scope, scopes


def classify(detail, path, source):
    condition = detail["条件"]
    if "印字出力" in condition:
        return {
            "a": "所有元と名前が一意の、単一の完全修飾定数に対する検査は記録へ移す。placements を参照。",
            "b": "短名、適用、局所例、外部解決と候補が0件または複数の名前は Lean に残す。",
            "c": "記録と一致した単一定数の型・公理の印字文字列を合否から外す。存在と公理集合は記録から取得できる。",
        }
    if "個別の条件を移植" in condition:
        if path == "scripts/audit_infinity_f1.lean" and 10012 in detail["行"]:
            return {"a": "Ind-S (8) 指定8本の直接KST import禁止と型中の ModelCategory 禁止を記録で検査する。"}
        if PREFIX.search(source):
            return {"a": "旧接頭辞と移動表を実際の import 閉包と突き合わせ、宣言があることを記録で検査する。"}
    if "環境での宣言存在" in condition:
        return {"a": "F2 の C3 互換名と正規名の所有元を検査する。",
                "b": "実効の deprecated 属性、since、メッセージ、正規名に属性がないことは Lean に残す。"}
    if "指定所有元と推移 import" in condition:
        return {"a": "GeneralTools の必須モジュール・禁止モジュール・禁止接頭辞を閉包から検査する。"}
    if "移動表で旧接頭辞" in condition:
        return {"a": "旧接頭辞に対応する移動先が宣言を持つことを記録で検査する。"}
    if ("assert_no_sorry" in condition or "厳格条件" in condition or "厳格な" in condition or
            "照合・実行漏れ" in condition or "宣言型の禁止依存" in condition or
            "禁止宣言・禁止所有" in condition or "旧 BS surjectivity" in condition):
        return {"stage3": "公理・strict 名・訪問・禁止辺の判定は段3の移植規則を参照。固有の環境条件は別行で扱う。"}
    if "ソース直接 sorry/admit" in condition:
        return {"stage3": "カーネルの直接依存と許可ファイルを判定。",
                "b": "コメントやマクロを含むソース構文側の旧検査は残す。"}
    if "推移 import 境界" in condition:
        return {"stage3": "段3の S1 import 境界規則を参照。"}
    return {"b": "旧 Lean/ソース検査を維持。指定型・適用例・登録・公開性などの実効条件を監査する。"}


def verify(db, expected_keys, rules, scripts, placements):
    graph = imports_of(db)
    misses = []
    for (owner, name), public in sorted(expected_keys.items()):
        row = db.execute("SELECT public FROM decl WHERE module=? AND name=?", (owner, name)).fetchone()
        if row is None or (public and not row[0]):
            misses.append(["name-or-visibility", owner, name])
    scoped = {path: closure(graph, roots) for path, roots in scripts.items()}
    for path, line, owner, name, _ in placements:
        if owner not in scoped[path]:
            misses.append(["name-outside-imports", path, line, owner, name])
    declarations = dict(db.execute("SELECT name,declarations FROM module"))
    for rule in rules:
        kind = rule["kind"]
        path = rule["path"]
        if kind in ("scope", "boundary"):
            scope = closure(graph, rule["roots"])
        if kind == "scope":
            selected = set(rule["destinations"]) | {m for m in scope if under(m, rule["prefix"])}
            if not any(declarations.get(m, 0) for m in selected & scope):
                misses.append([kind, path, rule["prefix"], sorted(selected & scope)])
        elif kind == "boundary":
            for m in sorted(set(rule["required"]) - scope):
                misses.append([kind, path, "required module", m])
            for m in sorted(scope):
                if m in rule["forbidden"] or any(under(m, prefix) for prefix in rule["forbidden_prefixes"]):
                    misses.append([kind, path, "forbidden module", m])
        elif kind in ("direct-import", "type-ref-substring"):
            for m in rule["modules"]:
                if m not in graph:
                    misses.append([kind, path, "missing module", m])
                    continue
                if kind == "direct-import":
                    for dep in graph[m]:
                        if under(dep, rule["forbidden"]):
                            misses.append([kind, path, m, dep])
                else:
                    for name, refs in db.execute("SELECT name,type_refs FROM decl WHERE module=?", (m,)):
                        prohibited = [ref for ref in json.loads(refs) if rule["forbidden"] in ref]
                        if prohibited:
                            misses.append([kind, path, m, name, prohibited])
    return misses


def migrate(baseline, out):
    graph = imports_of(baseline)
    layout = json.loads(LAYOUT.read_text())
    classified = []
    diagnostics = []
    names = {}
    placements, retained, rules = [], [], []
    scripts = {}
    with MAPPING.open(newline="") as stream:
        for row in csv.DictReader(stream):
            if row["manifest"] != "True":
                continue
            path = row["path"]
            source = (ROOT / path).read_text()
            scope, own_rules = scopes_for_script(path, source, graph, layout)
            scripts[path] = sorted(set(IMPORT.findall(source)))
            selected, indeterminate, printed = plain_names(baseline, scope, source, path)
            retained.extend(indeterminate)
            placements.extend(printed)
            names.update(selected)
            rules.extend(own_rules)
            for detail in json.loads(row["residual_details"]):
                classified.append(dict(path=path, detail=detail, decision=classify(detail, path, source)))
            if path == "scripts/audit_infinity_f2.lean":
                for name in named_array(source, "replacements"):
                    rows = [(m, public) for m, public in baseline.execute(
                        "SELECT module,public FROM decl WHERE name=?", (name,)) if m in scope]
                    if len(rows) != 1:
                        diagnostics.append([path, "ambiguous or missing C3 declaration", name, rows])
                    else:
                        m, public = rows[0]
                        names[m, name] = bool(public)
    write_json(out / "residual-classification.json", classified)
    write_json(out / "residual-predicates.json", dict(
        names=[[*k, v] for k, v in sorted(names.items())], rules=rules, script_roots=scripts))
    write_json(out / "residual-placements.json", dict(placements=placements, keep_lean=retained))
    return classified, diagnostics, names, placements, retained, rules, scripts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path, help="record used to fix the exact owned-name expectations")
    parser.add_argument("after", type=Path, help="record to check")
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    args.out.mkdir(parents=True, exist_ok=True)
    with load_db(args.before) as before, load_db(args.after) as after:
        rows, diagnostics, names, placements, retained, rules, scripts = migrate(before, args.out)
        violations = diagnostics + verify(after, names, rules, scripts, placements)
    report = dict(pass_=not violations, classifications=Counter(x for row in rows for x in row["decision"]),
                  exact_names=len(names), print_placements=len(placements), retained_lean=len(retained),
                  graph_rules=Counter(rule["kind"] for rule in rules), violations=violations,
                  seconds=time.monotonic() - start)
    write_json(args.out / "residual-summary.json", report)
    return bool(violations)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (Failure, OSError, ValueError) as error:
        sys.exit(str(error))
