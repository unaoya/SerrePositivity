#!/usr/bin/env python3
"""IC-2 placement, reachability decisions and static import simulation."""
from collections import Counter, defaultdict
from copy import deepcopy
from graphlib import TopologicalSorter
from hashlib import sha256
import json
from pathlib import Path
import re

from stage0 import OUT, ROOT, PREFIX, GENERAL, dump, module, read_csv, reverse, traverse, under, write_csv
from layer_check import classify, code_only, direct_reasons, forbidden, TIERS
from klw1_layer_check import check

IC = PREFIX + "InfinityCategories."
MODEL = re.compile(
    r"\b(?:OmegaSpectrum|OmegaSpectra|SymmetricSpectrum|DGCategory|DGModule|DGFunctor|"
    r"DGAlgebra|DGCat|DGAlgebraCat|StableModelCategory|PointedKanLoopSpectrum)\b"
)
S_ROUTE = re.compile(r"\b(?:sConstruction|sStableModel|sEndofunctor|sPostcomp\w*|monicK\w*)\b")
DECL_HEADER = re.compile(
    r"^(?:(?:@\[[^\n]*\]|private|public|protected|noncomputable|local|scoped|unsafe|partial) +)*"
    r"(?:def|abbrev|theorem|lemma|instance|structure|class|inductive|opaque|axiom|variable)"
    r"(?=\s)\s*([^\n]*(?:\n[ \t]+[^\n]*)*)", re.M
)
ORDINARY = {
    "CechFunctorComparison": "加法的関手と有限 Čech 複体。型は通常の圏・複体。",
    "FormalCoproductCechFunctor": "有限積を保つ通常関手と余単体 Čech の比較。",
    "ColimitMapStability": "通常の関手圏の colimMap と MorphismProperty。",
    "MonoQuasiIsoCellClosure": "アーベル圏の複体で monic quasi-isomorphism の閉性。",
    "TriangulatedKernel": "通常の前三角圏の零対象閉性。",
    "CoproductClosure": "HTT A.1.2.5/A.1.2.7 の生成持上げ類の補助。主型は通常圏。",
    "ClosedGeneratedClass": "HTT A.1.2.5/A.1.2.7 の生成持上げ類の補助。主型は通常圏。",
}
# These wrappers were already moved in substance by the rectification lane.
COMPAT = {"SmallKanHomotopy", "SmallTargetKernelQuotient", "StarDiagramSmallQuotient",
          "WeightedWordHom", "WordSegmentComparison"}


def signatures(source):
    masked = code_only(source)
    for match in DECL_HEADER.finditer(masked):
        # An explicit declaration type/context is required; do not scan proofs.
        prefix = match[0].partition(":=")[0]
        yield masked.count("\n", 0, match.start()) + 1, " ".join(prefix.split())


def classification(path, source, imports):
    stem = Path(path).stem
    if path.startswith("SerrePositivity/HomotopicalAlgebra/Simplicial/") and stem in COMPAT:
        assert imports == {PREFIX + "HomotopicalAlgebra.Rectification.Simplicial." + stem}
        assert not list(signatures(source))
        return "互換入口", "単独 public import のみ。中断した厳密化本体は Rectification にある。", ""
    sig = list(signatures(source))
    if match := next(((line, s) for line, s in sig if MODEL.search(s)), None):
        return "模型境界・保留", "宣言の型または局所 instance が特定の模型に固定。一般部分との切り分けを確認する。", f"L{match[0]} {match[1][:240]}"
    if stem in ORDINARY:
        return "通常圏・ホモトピー論側に据置", ORDINARY[stem], f"L{sig[0][0]} {sig[0][1][:240]}"
    if match := next(((line, s) for line, s in sig if "ReedyStructure" in s), None):
        return "通常圏・ホモトピー論側に据置", "通常の Reedy 図式・制限・延長の構成。", f"L{match[0]} {match[1][:240]}"
    if "/KST/SConstruction/Cofinality/" in path:
        anchor = re.compile(r"coreS|multiSEndofunctor|completion|WideStageData|StableWideCofinalitySupply")
        line, chunk = next((line, s) for line, s in sig if anchor.search(s))
        return "S構成との混在・保留", "多重Sの完成像・coreS・wide cofinality の比較層。一般部分との境界を分けてから検討。", f"L{line} {chunk[:320]}"
    # StableModel itself packages an arbitrary stable quasicategory. Treat it
    # as K-specific only when the exposed endpoint refers to the actual S route.
    if match := next(((line, s) for line, s in sig if S_ROUTE.search(s) and "KST/SConstruction/" in path), None):
        return "S構成との混在・保留", "S構成の実装で用いる型・比較に固定された箇所がある。一般部と分割する判断を残す。", f"L{match[0]} {match[1][:240]}"
    return GENERAL, "", ""


def coverage_items(items):
    return [(m[1], m[2]) for m in re.finditer(r"(Kerodon|HTT|HA) ([\w.]+)", items)]


def placement(row, records, sections):
    directory = row["destination"].rstrip("/")
    refs = sorted({(r["review"].split("/")[1].removesuffix("-coverage"), r["number"]) for r in records})
    authoritative = [("Kerodon" if k == "kerodon" else k.upper(), n)
                     for k, n in refs if k in {"kerodon", "ha", "htt"}]
    old_items = coverage_items(row["coverage_items"])
    primary = next((p for p in authoritative if p[0] == "Kerodon"), None)
    if not primary:
        primary = next((p for p in authoritative if p[0] == "HA" and p[1].startswith("1.1.")), None)
    if not primary:
        primary = next((p for p in authoritative if p[0] == "HA"), None)
    if not primary:
        primary = next((p for p in authoritative if p[0] == "HTT" and not p[1].startswith("A.")), None)
    if primary:
        book, number = primary
        if book == "Kerodon":
            section = tuple(map(int, number.split(".")[:2]))
            directory = next(p.replace(".", "/") for p, s in sections.items() if tuple(s) == section)
        elif book == "HA" and number.startswith("1.1."):
            directory = "SerrePositivity/InfinityCategories/HA/StableInfinityCategories"
        else:
            directory = f"SerrePositivity/InfinityCategories/{book}/Section{number.rsplit('.', 1)[0].replace('.', '_')}"
        provenance = "対応表の宣言参照"
    else:
        book_dir = directory.split("/")[2]
        primary = next((p for p in old_items if p[0] == book_dir), None)
        provenance = "旧表の補助番号・主題"
    # Keep non-numbered support next to the reviewed construction rather than
    # creating new coverage assertions; also subdivide the broad HA 1.1 group.
    if directory.endswith("/StableInfinityCategories"):
        groups = {"1": "ZeroObjectsAndCofibers", "3": "StableSubcategories", "4": "Exact"}
        number = primary[1] if primary else ""
        part = number.split(".")
        if len(part) >= 3 and part[2] in groups:
            directory += "/" + groups[part[2]]
    return directory, (" ".join(primary) if primary else ""), provenance, refs


def layer_preview(graph, paths, moves):
    config = json.loads((ROOT / "scripts/refactor/layers.json").read_text())
    kl = config["klw1"]
    # Match KL-W1's filesystem node names, including its existing
    # blueprint/ prefix convention. Keep true names in reachability.
    by_check_name = {m: paths[m].removesuffix(".lean").replace("/", ".") for m in graph}
    g = {by_check_name[m]: deps for m, deps in graph.items()
         if not any(under(by_check_name[m], p) for p in kl["exclude_prefixes"])}
    planned = {m: moves.get(m, m) for m in g}
    assert len(set(planned.values())) == len(g)
    after = {planned[m]: {moves.get(d, d) for d in ds} for m, ds in g.items()}
    assert sum(map(len, after.values())) == sum(map(len, g.values()))
    list(TopologicalSorter({m: ds & g.keys() for m, ds in g.items()}).static_order())
    list(TopologicalSorter({m: ds & after.keys() for m, ds in after.items()}).static_order())
    unknown = sorted(m for m in g if m.startswith(IC) and m not in kl["modules"])
    assert not (set(kl["modules"]) - g.keys())
    before_config = deepcopy(kl)
    before_config["modules"].update(dict.fromkeys(unknown, "Consumers"))
    after_config = deepcopy(before_config)
    after_config["modules"] = {moves.get(m, m): tier for m, tier in before_config["modules"].items()}
    for m, new in moves.items():
        after_config["modules"][new] = before_config["modules"].get(m, "Consumers")
    # Both ends and the implementation predicate travel with the file.
    old_impl = kl["implementation_prefixes"]
    after_config["implementation_prefixes"] += [new for m, new in moves.items()
                                                if any(under(m, p) for p in old_impl)]
    inherited_impl = {m for m in g if any(under(m, p) for p in old_impl)}
    projected_impl = {m for m in g if any(under(planned[m], p) for p in after_config["implementation_prefixes"])}
    assert inherited_impl == projected_impl
    for k in ("implementation_edges", "reverse_edges"):
        for row in after_config[k]:
            for endpoint in ("from", "to"):
                row[endpoint] = moves.get(row[endpoint], row[endpoint])
    print("Running existing KL-W1 static diagnostics", flush=True)
    before_report = check(g, before_config)
    after_report = check(after, after_config)
    expected = {(v["kind"], tuple(moves.get(m, m) for m in v["path"]))
                for v in before_report["violations"]}
    actual = {(v["kind"], tuple(v["path"])) for v in after_report["violations"]}
    additions = actual - expected
    assert all(kind == "reverse-section" and path[0] in moves.values() for kind, path in additions)
    held_dest = {path[0] for _, path in additions}
    held_sources = {m for m, new in moves.items() if new in held_dest}
    subset = {m: new for m, new in moves.items() if m not in held_sources}
    subset_graph = {subset.get(m, m): {subset.get(d, d) for d in ds} for m, ds in g.items()}
    subset_config = deepcopy(after_config)
    for m in held_sources:
        subset_config["modules"].pop(moves[m])
        if m in before_config["modules"]:
            subset_config["modules"][m] = before_config["modules"][m]
    inverse_held = {moves[m]: m for m in held_sources}
    subset_config["implementation_prefixes"] = [
        inverse_held.get(p, p) for p in after_config["implementation_prefixes"]
    ]
    for k in ("implementation_edges", "reverse_edges"):
        for row in subset_config[k]:
            for end in ("from", "to"):
                row[end] = inverse_held.get(row[end], row[end])
    subset_report = check(subset_graph, subset_config)
    subset_expected = {(kind, tuple(subset.get(m, m) for m in path))
                       for kind, path in ((v["kind"], v["path"]) for v in before_report["violations"])}
    subset_actual = {(v["kind"], tuple(v["path"])) for v in subset_report["violations"]}
    assert subset_actual == subset_expected
    blocker_edges = defaultdict(list)
    for _, path in sorted(additions):
        blocker_edges[path[0]].append(path[1])
    write_csv("layer-holds.csv", [
        dict(old_module=m, candidate_module=moves[m], reverse_section_edges=len(blocker_edges[moves[m]]),
             destinations=" | ".join(blocker_edges[moves[m]]), proposal="留保し、利用節または shared helper を再検討")
        for m in sorted(held_sources)
    ])
    old_unknown = set(unknown)
    ambiguous = [(m, d) for m, ds in g.items() for d in ds
                 if (m in moves or d in moves) and (m in old_unknown or d in old_unknown)]

    # W1/W2a/W2b invariant outside moved endpoints: same graph up to bijection,
    # unchanged root/layer and forbidden predicates except documented deltas.
    model_mentions = {m for m in graph if under(m, config["model_category_rule"]["prefix"])
                      and "ModelCategory" in code_only((ROOT / paths[m]).read_text())}
    after_model = {moves.get(m, m) for m in model_mentions
                   if under(moves.get(m, m), config["model_category_rule"]["prefix"])}
    core = {m for m in g if classify(m, config) in config["core"]}
    changed_core = [m for m, new in moves.items() if classify(m, config) != classify(new, config)]
    assert not changed_core
    w2 = {}
    for tier in TIERS:
        exceptions = {(e["from"], e["to"]) for e in config["exceptions"]
                      if TIERS.index(tier) <= TIERS.index(e["expires"])}
        assert not any(m in moves or n in moves for m, n in exceptions)
        effective = {m: {d for d in ds if (m, d) not in exceptions} for m, ds in g.items()}
        backwards = reverse(effective)
        diff = []
        for m, new in moves.items():
            old_flag = forbidden(m, tier, config, model_mentions)
            new_flag = forbidden(new, tier, config, after_model)
            if old_flag != new_flag:
                impacted = sorted(core & traverse({m}, backwards).keys())
                diff.append(dict(old=m, new=new, before_forbidden=old_flag,
                                 after_forbidden=new_flag, affected_core=impacted))
        w2[tier] = diff
    direct = []
    for m, ds in g.items():
        for d in ds:
            if m in moves or d in moves:
                old = direct_reasons(m, d, config)
                new = direct_reasons(moves.get(m, m), moves.get(d, d), config)
                if old != new:
                    direct.append(dict(old=[m, d], new=[moves.get(m, m), moves.get(d, d)],
                                       before_rules=old, after_rules=new))
    dump("layer-preview.json", dict(
        modules=len(g), edges=sum(map(len, g.values())), cycles=0,
        baseline=len(expected), projected=len(actual), baseline_kinds=dict(Counter(k for k, _ in expected)),
        added=[dict(kind=k, path=p) for k, p in sorted(additions)],
        hold_variant=dict(held=len(held_sources), remaining=len(subset), projected=len(subset_actual),
                          new=len(subset_actual - subset_expected), removed=len(subset_expected - subset_actual)),
        removed=[dict(kind=k, path=p) for k, p in sorted(expected - actual)],
        temporary_consumers=unknown, unregistered_moved_incident_edges=sorted(ambiguous),
        legacy_w_direct_rule_changes=direct, legacy_w_forbidden_predicate_changes=w2,
        method="Transport existing tiers, implementation membership and edge exceptions. New nodes inherit old tier. Use existing KL checker on both sides and preserve legacy W classifications. No new exceptions."))


def main():
    x = json.loads(Path("/private/tmp/ic2-stage0-intermediate.json").read_text())
    graph = {m: set(deps) for m, deps in x["graph"].items()}
    paths = x["paths"]
    rev = reverse(graph)
    sections = json.loads((ROOT / "scripts/refactor/layers.json").read_text())["klw1"]["sections"]
    moves, inventory, unreached, changes, placements, public_names, leaf_candidates = ([] for _ in range(7))
    proposed_paths = set()
    treatment_count = Counter()
    for m, row in sorted(x["candidates"].items()):
        path = row["path"]
        file = ROOT / path
        text = file.read_text()
        lines = len(text.splitlines())
        assert lines == int(row["lines"])
        category, reason, evidence = classification(path, text, graph[m])
        notes = x["coverage"].get(m, [])
        directory, anchor, provenance, refs = placement(row, notes, sections)
        a, b, c = x["a"][m], x["b"][m], x["c"].get(m, [])
        audit, docs, drafts = (x[key][m] for key in ("audit", "docs", "drafts"))
        names = x["declarations"][m]
        destination = directory + "/" + file.name
        placement_note = ""
        if destination in proposed_paths or (ROOT / destination).exists():
            parent = Path(path).parent.name
            destination = directory + "/From" + parent + "/" + file.name
            placement_note = "同名衝突を避け、章内に旧主題別の下位ディレクトリを提案。"
            assert destination not in proposed_paths and not (ROOT / destination).exists()
        treatment = "移す"
        if category == "互換入口":
            treatment = "据置（非正式検査の利用あり）" if rev[m] else "Archive候補（互換終了の判断待ち）"
        elif category != GENERAL:
            treatment = "据置（分類境界）"
        if treatment == "移す":
            proposed_paths.add(destination)
            family = directory.removeprefix("SerrePositivity/InfinityCategories/").replace("/", "-")
            namespace = sorted(set(n.rpartition(".")[0] for n, _, _ in names if "." in n))
            moves.append(dict(id="IC2-" + family, old_path=path, new_path=destination, old_module=m,
                              new_module=module(destination), family=family, classification=category,
                              lines=lines, old_namespace_prefix=" | ".join(namespace),
                              new_namespace_prefix=" | ".join(namespace), source_named_candidates=len(names),
                              source_rename_candidates=0, sha256=sha256(file.read_bytes()).hexdigest()))
            for name, _, line in names:
                public_names.append(dict(old_name=name, new_name=name, path=path, line=line))
            placements.append(dict(old_path=path, proposed_path=destination, primary=anchor, basis=provenance,
                                   direct_review=" | ".join(f"{k} {n}" for k, n in refs),
                                   previous_items=row["coverage_items"], note=placement_note))
        else:
            changes.append(dict(path=path, lines=lines, files_csv_classification=row["classification"],
                                proposed_classification=category, old_destination=row["destination"],
                                handling=treatment, reason=reason, source_evidence=evidence,
                                inputs=" | ".join(sorted(graph[m]))))
        treatment_count[treatment] += 1
        row_out = dict(path=path, module=m, lines=lines, a_witness=a, b_witness=b,
                       c_witness=" | ".join(f'{r["branch"]}: {r["witness"]}' for r in c),
                       audit_witness=audit, blueprint_witness=docs, draft_witness=drafts,
                       treatment=treatment, direct_importer_count=len(rev[m]), primary=anchor,
                       candidate_classification=category)
        inventory.append(row_out)
        if not (a or b or c):
            importers = sorted(rev[m])
            why = ("正式監査の import 閉包に含む。保持し、分類が合えば通常の移動候補。" if audit else
                   "非正式チェックの利用を確認。旧パスの扱いは別判断。" if importers else
                   "本体は別モジュールにあり、旧入口には宣言と現行直接 importer がない。互換廃止の可否をユーザーが判断。")
            archive_path = ("SerrePositivity/Archive/IC2/Compatibility/" + file.name
                            if treatment.startswith("Archive") else "")
            unreached.append(row_out | {"direct_importers": " | ".join(importers),
                                       "archive_candidate_path": archive_path, "handling_basis": why})
    assert len(moves) + len(changes) == len(inventory) == 1725
    assert len(unreached) == sum(not (r["a_witness"] or r["b_witness"] or r["c_witness"]) for r in inventory)
    assert list(moves[0]) == list(read_csv("research/infinity-consolidation-w1/moves.csv")[0])
    mapping = {r["old_module"]: r["new_module"] for r in moves}
    assert len(mapping) == len(set(mapping.values()))
    list(TopologicalSorter({m: deps & graph.keys() for m, deps in graph.items()}).static_order())
    family = {r["old_module"]: r["family"] for r in moves}
    for row in moves:
        m = row["old_module"]
        if row["lines"] > 80 or any(family.get(p) == family[m] for p in rev[m]):
            continue
        leaf_candidates.append(dict(
            path=row["old_path"], lines=row["lines"], chapter=family[m],
            namespace=row["old_namespace_prefix"], total_importers=len(rev[m]),
            direct_imports=" | ".join(sorted(graph[m])), audit_witness=x["audit"][m],
            importers=" | ".join(sorted(rev[m])),
        ))
    branch_report = json.loads((OUT / "branch-impact.json").read_text())
    for branch, report in branch_report.items():
        branch_graph = x["branch_graphs"].get(branch, {})
        branch_affected = traverse(mapping.keys() & branch_graph.keys(), reverse(branch_graph))
        current_affected = traverse(mapping, rev)
        report["planned_move_dependents_on_branch"] = sorted(set(report["roots"]) & branch_affected.keys())
        report["planned_move_dependents_on_main"] = sorted(set(report["roots"]) & current_affected.keys())
        report["planned_move_direct"] = [r for r in report["direct"] if set(r["imports"]) & mapping.keys()]
    dump("branch-impact.json", branch_report)
    affected = traverse(mapping, rev)
    outside = {m: graph[m] & mapping.keys() for m in graph if m not in mapping and graph[m] & mapping.keys()}
    impact = [dict(path=paths[m], direct_imports=len(deps), modules=" | ".join(sorted(deps)),
                   draft=paths[m].startswith("formalization-plans/")) for m, deps in sorted(outside.items())]
    write_csv("inventory.csv", inventory)
    write_csv("moves.csv", moves)
    write_csv("unreached.csv", unreached)
    write_csv("classification-differences.csv", changes)
    write_csv("placement.csv", placements)
    write_csv("source-names.csv", public_names)
    write_csv("import-followups.csv", impact)
    write_csv("b1-leaves.csv", leaf_candidates)
    write_csv("excluded-previous-moves.csv", [{"path": p} for p in x["prior_moves"]])
    root_closure = traverse({"SerrePositivity"}, graph)
    summary = dict(
        base=x["base"], graph_nodes=len(graph), graph_edges=sum(map(len, graph.values())),
        candidates=len(inventory), candidate_lines=sum(r["lines"] for r in inventory),
        by_area=dict(Counter(r["path"].split("/")[1] for r in inventory)),
        reached_patterns=dict(Counter("".join(k for k in "abc" if r[f"{k}_witness"]) or "none"
                                      for r in inventory)),
        unreached=len(unreached), unreached_lines=sum(r["lines"] for r in unreached),
        unreached_by_treatment=dict(Counter(r["treatment"] for r in unreached)),
        unreached_audit=sum(bool(r["audit_witness"]) for r in unreached),
        unreached_audit_lines=sum(r["lines"] for r in unreached if r["audit_witness"]),
        root_only_candidates=len(x["root_only"]), treatments=treatment_count,
        moves=len(moves), moves_lines=sum(r["lines"] for r in moves), moved_unreached=sum(not any(x[k].get(m) for k in "abc") for m in mapping),
        units=dict(Counter(r["id"] for r in moves)), source_named_candidates=len(public_names),
        classification_differences=dict(Counter(r["proposed_classification"] for r in changes)),
        placement_direct_review=sum(r["basis"] == "対応表の宣言参照" for r in placements),
        placement_without_number=sum(not r["primary"] for r in placements),
        placements_changed_section=sum(not r["proposed_path"].startswith(x["candidates"][module(r["old_path"])]["destination"]) for r in placements),
        collisions_resolved=sum(bool(r["note"]) for r in placements),
        direct_external_followups=len(impact), direct_external_import_tokens=sum(
            sum(d in mapping for d in x["headers"][r["path"]]) for r in impact),
        inverse_graph=len(affected), inverse_library=sum(under(m, "SerrePositivity") for m in affected),
        inverse_root_library=sum(under(m, "SerrePositivity") for m in affected.keys() & root_closure.keys()),
        affected_formal_audits=len(set(json.loads((OUT / "roots.json").read_text())["formal_audit_modules"]) & affected.keys()),
        B1_chapter_leaves=len(leaf_candidates), B1_leaf_lines=sum(r["lines"] for r in leaf_candidates),
        B1_whole_graph_leaves=sum(not r["total_importers"] for r in leaf_candidates),
    )
    dump("summary.json", summary)
    layer_preview(graph, paths, mapping)
    print("Proposal:", json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    main()
