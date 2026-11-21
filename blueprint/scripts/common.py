"""Render only links supplied by the record audit and check each generated card."""
import hashlib
import json
import os
from pathlib import Path
import re

CARD = re.compile(r'^:::\w+ "([^"]+)"(.*)$', re.M)
LINK = re.compile(r'\(lean := ("(?:[^"\\]|\\.)*")\)')


def rendered_links(text):
    result = {}
    for label, options in CARD.findall(text):
        if label in result:
            raise ValueError(f"duplicate blueprint card: {label}")
        values = LINK.findall(options)
        if len(values) > 1 or ("(lean :=" in options and not values):
            raise ValueError(f"invalid Lean link field: {label}")
        result[label] = json.loads(values[0]).split(", ") if values else []
    return result


class Resolver:
    def __init__(self):
        path = os.environ.get("AUDIT2_BLUEPRINT_PLAN")
        if not path:
            raise SystemExit("Use scripts/audit2/coverage_blueprint.py to generate with a checked reference plan.")
        plan = json.loads(Path(path).read_text())
        self.preview = plan["preview"]
        if plan["root"] != str(Path.cwd().resolve()):
            raise SystemExit("The reference plan is for a different generation directory.")
        for file, expected in plan["inputs"].items():
            if hashlib.sha256(Path(file).read_bytes()).hexdigest() != expected:
                raise SystemExit(f"Stale blueprint input: {file}")
        self.references = plan["links"]
        self.name_only = plan.get("name_only", {})
        self.provenance = (f"-- audit2: {plan['commit']} inputs sha256 {plan['input_hash']}"
                           + (" (diagnostic preview)" if self.preview else ""))
        baseline_commits = plan.get("baseline_commits", [plan["commit"]])
        if baseline_commits != [plan["commit"]]:
            self.provenance += "\n-- audit2 baselines: " + ", ".join(baseline_commits)
        self.expected = {}
        self.shown = {}

    def links(self, label, raw, imports, enabled):
        names = []
        shown = []
        if enabled:
            parts = [e.strip() for e in raw.split(" | ") if e.strip()]
            if not parts and not self.preview:
                raise SystemExit(f"Missing declaration at blueprint card {label}")
            for entry in parts:
                x = self.references.get(entry)
                if not x:
                    if self.preview:
                        continue
                    raise SystemExit(f"Unresolved blueprint link at {label}: {entry}")
                if entry in self.name_only:
                    shown.append(self.name_only[entry])
                    continue
                names.append(x[0])
                imports.add(x[1])
        self.expected[label] = names
        self.shown[label] = shown
        return names

    def declaration_note(self, label, raw, linked):
        entries = [e.strip() for e in raw.split(" | ") if e.strip()]
        shown = self.shown[label]
        if shown:
            return "宣言（リンクなし）：" + "、".join(f"`{d}`" for d in shown) + "\n"
        if entries and not linked:
            names = [e.split(" @ ", 1)[0].strip().replace("`", "") for e in entries]
            return "宣言：" + "、".join(f"`{d}`" for d in names) + "\n"
        return ""

    def write(self, path, text):
        actual = rendered_links(text)
        if actual != self.expected:
            keys = sorted(k for k in actual.keys() | self.expected.keys()
                          if actual.get(k) != self.expected.get(k))
            raise SystemExit(f"Wrong blueprint links in {path}: {keys[:12]}")
        Path(path).write_text(self.provenance + "\n" + text, encoding="utf-8")
        self.expected.clear()
        self.shown.clear()


def esc(s):
    return re.sub(r'([\\*_\x60\[\]{}#$<>|~^])', r'\\\1', s)
