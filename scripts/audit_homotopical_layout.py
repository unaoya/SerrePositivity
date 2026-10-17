"""Check general-tool independence and the rectification compatibility layout."""
import json
from pathlib import Path
import re

manifest = json.loads(Path("scripts/homotopical_generalization_manifest.json").read_text())
imports = {
    str(p)[:-5].replace("/", "."): re.findall(
        r"^(?:public |private )?import\s+(\S+)", p.read_text(), re.M
    )
    for p in Path("SerrePositivity").rglob("*.lean")
}

def closure(root):
    seen, pending = set(), [root]
    while pending:
        mod = pending.pop()
        if mod in seen or mod not in imports:
            continue
        seen.add(mod)
        pending.extend(imports[mod])
    return seen


general = "SerrePositivity.HomotopicalAlgebra.GeneralTools"
shared = "SerrePositivity.HomotopicalAlgebra.Foundations"
dedicated = "SerrePositivity.HomotopicalAlgebra.Rectification"
a = {x["module"] for x in manifest["entries"] if x["class"] == "A"}
b = {x["module"] for x in manifest["entries"] if x["class"] == "B"}
general_closure = closure(general)
assert a <= general_closure, f"Missing A entries: {sorted(a - general_closure)}"
assert set(manifest["cores"]) <= general_closure
assert not general_closure & b, "General tools import legacy B modules"
assert not any(m.startswith(dedicated + ".") for m in general_closure)
assert not any(set(imports[m]) & b for m in a), "An A-to-B edge remains"
print(f"General tools: {len(general_closure)} project modules, all {len(a)} A entries, B/Rectification zero.")

if manifest.get("phase", 1) >= 2:
    shared_closure = closure(shared)
    assert a <= shared_closure
    assert not shared_closure & b
    assert not any(m.startswith(dedicated + ".") for m in shared_closure)
    for old, new in manifest["relocations"].items():
        assert old in imports and new in imports, (old, new)
        assert imports[old] == [new], f"Invalid compatibility import: {old}"
        assert not set(imports[new]) & b, f"Canonical module imports legacy B: {new}"
    optional_closure = closure(dedicated + ".Foundations")
    assert set(manifest["relocations"].values()) <= optional_closure
    assert a <= optional_closure
    print(f"Shared Foundations: {len(shared_closure)} project modules, B/Rectification zero.")
    print(f"Rectification: {len(manifest['relocations'])} canonical modules and compatible old imports; closure {len(optional_closure)}.")
