/-
Copyright (c) 2026 SerrePositivity contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import SerrePositivity.Util.Citation

/-!
# The citation registry and the query commands

The registry of citation keys and editions, generated from `research/bibliography.json` by
`scripts/refactor/bulk_citation_registry.py`, and the commands that read it: `#cite_tags KEY`
lists citations with their defining module and declaration range, `#cite_tags! KEY` also displays
their types, `#cite_check NAME` inspects a candidate, and `#cite_registry_check` fails on any
recorded citation whose key is not registered. No mathematical module imports this file, so a new
key rebuilds only this module and the citation audit (BR54, 2026-11-17).
-/

public meta section

namespace SerrePositivity.Citation

open Lean Elab Command

-- BEGIN GENERATED REGISTRY
private def knownKeys : List String := [
  "AGH",
  "BGT",
  "BM18",
  "BS17",
  "BS19",
  "BST13",
  "BalmerSchlichting",
  "Barwick",
  "DAGXIII",
  "Drinfeld",
  "Goodwillie",
  "HA",
  "HTT",
  "KL",
  "KST",
  "Kerodon",
  "LT",
  "NS",
  "Neeman",
  "Paper",
  "Rydh",
  "Schlichting",
  "Stacks",
  "TT",
  "Tamme",
  "Thomason",
  "Waldhausen"]

private def knownEditions : List (String × String) := [
  ("AGH", "arXiv:2009.07224v5"),
  ("BGT", "arXiv:1001.2282v4"),
  ("BM18", "arXiv:1807.04725v4"),
  ("BS17", "arXiv:1507.06490v3"),
  ("BS19", "author version"),
  ("BST13", "arXiv:1307.3763v3"),
  ("BalmerSchlichting", "2001 刊行版, J. Algebra 236"),
  ("Barwick", "arXiv:1204.3607v6"),
  ("DAGXIII", "2011-12-15"),
  ("Drinfeld", "arXiv:math/0210114v7"),
  ("Goodwillie", "1986 刊行版, Ann. Math. 124"),
  ("HA", "2017-09-18"),
  ("HTT", "2017-04-09"),
  ("KL", "arXiv:1212.6170v1"),
  ("KST", "arXiv:1611.08466v4"),
  ("Kerodon", "stable Tags"),
  ("LT", "arXiv:1808.05559v3"),
  ("NS", "arXiv:1707.01799v2"),
  ("Neeman", "1992 刊行版, Ann. ENS 25"),
  ("Paper", "2026-09-23; upstream adc7f1241b42e322a6451854ab7e4b4c146bf78a"),
  ("Rydh", "arXiv:0710.2488v3"),
  ("Schlichting", "公開稿（11.4・11.7・11.10・6.4）"),
  ("Stacks", "stable Tags"),
  ("TT", "1990 刊行版, Grothendieck Festschrift III"),
  ("Tamme", "arXiv:1703.03331v3"),
  ("Thomason", "1993 刊行版, Invent. Math. 112"),
  ("Waldhausen", "1985 刊行版, LNM 1126")]
-- END GENERATED REGISTRY

private def editionFor (key : String) : String :=
  ((knownEditions.find? fun pair => pair.1 == key).map Prod.snd).getD ""

/-- Fail if a recorded citation uses a key that is not in the registry. -/
elab "#cite_registry_check" : command => do
  let entries := citationExt.getState (← getEnv)
  let bad := entries.filter fun e => !knownKeys.contains e.key
  unless bad.isEmpty do
    let listed := bad.toList.map fun e => (e.key, e.declName)
    throwError "Unknown citation keys (register them in research/bibliography.json): {listed}"
  logInfo m!"citation registry check passed: {entries.size} citations, {knownKeys.length} keys"

private def nativeEntries (env : Environment) (key : String) : Array Entry := Id.run do
  let state := PersistentEnvExtension.getState Mathlib.CrossRef.tagExt env
  let tags := state.2.flatten.appendList state.1
  return tags.filterMap fun t =>
    if (key == "Kerodon" && t.database == .kerodon) ||
       (key == "Stacks" && t.database == .stacks) then
      some ⟨key, t.tag, t.declName, .exact, t.comment⟩
    else none

/-- Stable citation output. Missing declaration ranges are explicit JSON nulls. -/
def traceCitations (key : String) (verbose : Bool) : CommandElabM Unit := do
  unless knownKeys.contains key do throwError "Unknown citation key '{key}'"
  let env ← getEnv
  let entries := ((citationExt.getState env).filter (·.key == key) ++ nativeEntries env key)
    |>.qsort fun a b => a.number < b.number ||
      (a.number == b.number && a.declName.toString < b.declName.toString)
  for entry in entries do
    let owner := (env.getModuleIdxFor? entry.declName).map fun idx =>
      env.header.modules[idx.toNat]!.module.toString
    let owner := owner.getD ((← getMainModule).toString)
    let ranges ← findDeclarationRanges? entry.declName
    let record := Json.mkObj [
      ("key", toJson entry.key), ("number", toJson entry.number),
      ("edition", toJson (editionFor entry.key)),
      ("relation", toJson
        (if key == "Kerodon" || key == "Stacks" then "native" else entry.relation.label)),
      ("comment", toJson entry.comment),
      ("declaration", toJson entry.declName.toString), ("module", toJson owner),
      ("path", toJson (owner.replace "." "/" ++ ".lean")),
      ("line", toJson (ranges.map (·.range.pos.line)))]
    logInfo record.compress
    if verbose then
      if let some info := env.find? entry.declName then logInfo m!"{info.type}"

private partial def requiresExplicitSSetModel : Expr → Bool
  | .forallE _ domain body _ =>
    let head := domain.getAppFn.constName?.map Name.toString
    let model := head.any fun n => n == "ModelCategory" || n.endsWith ".ModelCategory"
    let sset := domain.getAppArgs.any fun arg => arg.getAppFn.constName? == some `SSet
    (model && sset) || requiresExplicitSSetModel body
  | .letE _ _ value body _ => requiresExplicitSSetModel (body.instantiate1 value)
  | _ => false

/-- Inspect a candidate in its own imported environment, without adding a citation.
This supports the reviewed citation plan; it does not re-elaborate the declaration. -/
elab "#cite_check" decl:ident : command => do
  let name ← liftTermElabM <| withoutExporting <| realizeGlobalConstNoOverloadWithInfo decl
  let env ← getEnv
  let info ← getConstInfo name
  let owner := ((env.getModuleIdxFor? name).map fun idx =>
    env.header.modules[idx.toNat]!.module.toString).getD ((← getMainModule).toString)
  let ranges ← findDeclarationRanges? name
  let type ← liftTermElabM do
    withOptions (fun opts => opts.setBool `pp.fullNames true |>.setBool `pp.universes true) do
      return (← Meta.ppExpr info.type).pretty
  let axioms ← collectAxioms name
  logInfo (Json.mkObj [
    ("inspection", toJson true), ("declaration", toJson name.toString),
    ("module", toJson owner), ("path", toJson (owner.replace "." "/" ++ ".lean")),
    ("line", toJson (ranges.map (·.range.pos.line))), ("type", toJson type),
    ("private", toJson (isPrivateName name)),
    ("requires_explicit_sset_model", toJson (requiresExplicitSSetModel info.type)),
    ("type_constants", toJson (info.type.getUsedConstants.map Name.toString)),
    ("axioms", toJson (axioms.map Name.toString))]).compress

/-- List literature correspondences in the imported environment. -/
elab "#cite_tags" key:ident : command => traceCitations key.getId.toString false
/-- List literature correspondences and their declaration types. -/
elab "#cite_tags!" key:ident : command => traceCitations key.getId.toString true

end SerrePositivity.Citation
