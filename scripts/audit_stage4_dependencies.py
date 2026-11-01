"""Check that L/E/S use only the pre-generalization proof closure.

The baseline is the commit completing S3 in archive/k-theory-v1.md §223. The report
records direct imports and mapping-space references for every root, and
checks every transitive project dependency against that immutable tree.
This source audit complements the Lean kernel axiom audit.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", default="99696439")
    parser.add_argument("--output", default="/tmp/stage4-dependencies.json")
    args = parser.parse_args()
    baseline = subprocess.check_output(
        ["git", "rev-parse", args.baseline + "^{commit}"], text=True
    ).strip()
    files = {
        str(p)[:-5].replace("/", "."): p
        for p in Path("SerrePositivity").rglob("*.lean")
    }
    sources = {m: p.read_text() for m, p in files.items()}
    imports = {
        m: re.findall(r"^(?:public |private )?import\s+(\S+)", s, re.M)
        for m, s in sources.items()
    }

    def closure(root):
        seen, pending = set(), [root]
        while pending:
            mod = pending.pop()
            if mod not in seen:
                seen.add(mod)
                pending.extend(imports.get(mod, []))
        return sorted(seen & files.keys())

    roots = sorted(
        m for m in files if m.startswith((
            "SerrePositivity.HomotopicalAlgebra.Localization.",
            "SerrePositivity.Spectra.Stable.",
        ))
    ) + [
        "SerrePositivity.Spectra.ModelCategory.Combinatorial",
        "SerrePositivity.Spectra.ModelCategory.LeftProper",
    ]
    old = set(subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", baseline, "--", "SerrePositivity"],
        text=True,
    ).splitlines())
    references = re.compile(
        r"\b(?:chosenResolutionHom\w*|resolutionHom\w*|smallHom\w*|"
        r"(?:ChosenComparison|ChosenMapComparison|ResolutionComparison|"
        r"FrameComparison|SmallHomComparison)\.\w+)"
    )
    report = {}
    for mod in roots:
        deps = closure(mod)
        report[mod] = {
            "imports": imports[mod],
            "mapping_references": sorted(set(references.findall(sources[mod]))),
            "project_closure": deps,
            "after_223": [m for m in deps if str(files[m]) not in old],
        }
    all_deps = sorted({m for item in report.values() for m in item["project_closure"]})
    changed = []
    for mod in all_deps:
        path = str(files[mod])
        if path not in old:
            continue
        original = subprocess.check_output(["git", "show", baseline + ":" + path])
        if original != files[mod].read_bytes():
            changed.append(mod)
    result = {"baseline": baseline, "roots": report, "changed": changed}
    Path(args.output).write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    new = {m for item in report.values() for m in item["after_223"]}
    print(f"Stage 4 dependencies: {len(roots)} roots, {len(all_deps)} project modules.")
    print(f"Post-§223 dependencies: {len(new)}; changed reachable modules: {len(changed)}.")
    if new or changed:
        raise SystemExit("Review the dependency report before declaring independence.")


if __name__ == "__main__":
    main()
