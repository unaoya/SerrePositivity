"""Table rules used by the regional migration comparison."""
import json

from audit import Failure, closure, imports_of


class World:
    def __init__(self, db):
        self.db = db
        self.graph = imports_of(db)

    def declaration(self, key):
        return self.db.execute("SELECT * FROM decl WHERE module=? AND name=?", key).fetchone()

    def by_name(self, name):
        return self.db.execute("SELECT * FROM decl WHERE name=?", (name,)).fetchall()


def refs(row, edge):
    channels = {"type": ("type_refs",), "value": ("value_refs",),
                "both": ("type_refs", "value_refs", "ctors")}
    return {name for col in channels[edge] for name in json.loads(row[col])}


def check(world, rule):
    kind = rule["kind"]
    bad = []
    if kind == "visited-modules":
        return sorted(set(rule["expected"]) - set(rule["actual"]))
    if kind == "import-components":
        visited = closure(world.graph, rule["roots"])
        prefix = rule["prefix"]
        return sorted(m for m in visited if (m == prefix or m.startswith(prefix + "."))
                      and set(m.split(".")) & set(rule["forbidden"]))
    if kind == "reachable":
        roots = rule["starts"]
        if missing := [n for n in roots if len(world.by_name(n)) != 1]:
            return [f"missing or ambiguous start {n}" for n in missing]
        seen = set()
        todo = list(roots)
        forbid = set(rule["forbidden"])
        edge = rule.get("edge", "both")
        forbidden_modules = rule.get("forbidden_modules", [])
        while todo:
            name = todo.pop()
            if name in seen:
                continue
            seen.add(name)
            if name in forbid:
                bad.append(name)
            for row in world.by_name(name):
                if any(row["module"] == p or row["module"].startswith(p + ".")
                       for p in forbidden_modules):
                    bad.append([row["module"], name])
                todo.extend(refs(row, edge) - seen)
        return bad
    for key in rule["declarations"]:
        row = world.declaration(key)
        if row is None:
            bad.append([*key, "missing from table"])
            continue
        if kind == "strict-sorry":
            if row["axioms"] is None or "sorryAx" in json.loads(row["axioms"]):
                bad.append([*key, "sorry dependency or missing axiom result"])
        elif kind == "direct-edge":
            references = refs(row, rule["edge"])
            extra = references & set(rule["forbidden"])
            extra.update(n for n in references if n.rsplit(".", 1)[-1] in rule.get("suffixes", []))
            if extra:
                bad.append([*key, sorted(extra)])
        elif kind == "forbidden-kind":
            if row["kind"] in rule["forbidden"]:
                bad.append([*key, row["kind"]])
        elif kind == "direct-sorry-files":
            path = row["module"].replace(".", "/") + ".lean"
            if "sorryAx" in refs(row, "both") and path not in rule["allowed"]:
                bad.append([*key, path])
        elif kind == "shape":
            for field, value in rule["expect"].items():
                if field not in ("kind", "public", "private", "module"):
                    raise Failure(f"invalid shape field {field}")
                if row[field] != value:
                    bad.append([*key, field, row[field], value])
        else:
            raise Failure(f"unknown regional rule {kind}")
    return bad
