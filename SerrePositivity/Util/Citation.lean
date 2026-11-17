/-
Copyright (c) 2026 SerrePositivity contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Mathlib.Tactic.CrossRefAttribute
public meta import Lean.DeclarationRange
public meta import Lean.Util.CollectAxioms

/-!
# Literature citations

`@[cite KEY "number"]` records an exact correspondence with the registered edition.
`@[cite KEY "number" (partial := special) "reason"]` records only the stated part.
The other partial kinds are `direction`, `stronger-hyp`, and `component`.
`#cite_tags KEY` lists citations with their defining module and declaration range;
`#cite_tags! KEY` also displays their types. Kerodon and Stacks use Mathlib's attributes.
The registry is generated from `research/bibliography.json` and checked with that source.
-/

public meta section

namespace SerrePositivity.Citation

open Lean Elab Command

/-- The relationship between a declaration and a literature item. -/
inductive Relation where
  | exact | special | direction | strongerHyp | component
  deriving BEq, Inhabited

/-- Stable machine-readable spelling of a relationship. -/
def Relation.label : Relation → String
  | .exact => "exact"
  | .special => "special"
  | .direction => "direction"
  | .strongerHyp => "stronger-hyp"
  | .component => "component"

/-- A citation attached to its actual declaration, independently of file layout. -/
structure Entry where
  key : String
  number : String
  declName : Name
  relation : Relation
  edition : String
  comment : String
  deriving BEq, Inhabited

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

/-- Persistent citations, including imports. No source paths are cached here. -/
initialize citationExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.flatten
    addEntryFn := Array.push
  }

declare_syntax_cat citationRelation
syntax ident : citationRelation
syntax ident "-" ident : citationRelation

/-- Exact correspondence or a specified partial correspondence with a registered reference. -/
syntax (name := citeAttr) "cite" ident str
  ("(" "partial" ":=" citationRelation ")")? (ppSpace str)? : attr

private def parseRelation (stx : TSyntax `citationRelation) : CoreM Relation := do
  let spelling ← match stx with
    | `(citationRelation| $kind:ident) => pure kind.getId.toString
    | `(citationRelation| $left:ident - $right:ident) =>
      pure (left.getId.toString ++ "-" ++ right.getId.toString)
    | _ => throwError "Unknown citation relation"
  match spelling with
  | "special" => pure .special
  | "direction" => pure .direction
  | "stronger-hyp" => pure .strongerHyp
  | "component" => pure .component
  | _ => throwError "Unknown citation relation '{spelling}'"

initialize registerBuiltinAttribute {
  name := `citeAttr
  descr := "Record a literature citation with its precise correspondence."
  applicationTime := .beforeElaboration
  add := fun decl stx kind => do
    unless kind matches .global do
      throwError "Literature citations must be global"
    let `(attr| cite $key:ident $number:str $[(partial := $part)]? $[$comment:str]?) := stx
      | throwUnsupportedSyntax
    let key := key.getId.toString
    unless knownKeys.contains key do
      throwError "Unknown citation key '{key}'; register its edition in research/bibliography.json"
    if key == "Kerodon" || key == "Stacks" then
      throwError "Use Mathlib's native kerodon/stacks attribute for Tag references"
    let number := number.getString
    if number.trimAscii.toString.isEmpty then throwError "Citation number must not be empty"
    let relation ← part.mapM parseRelation
    let comment := (comment.map (·.getString)).getD ""
    if relation.isSome && comment.trimAscii.toString.isEmpty then
      throwError "A partial citation requires a nonempty reason"
    let entry : Entry := ⟨key, number, decl, relation.getD .exact, editionFor key, comment⟩
    let entries := citationExt.getState (← getEnv)
    if let some previous := entries.find? fun e =>
        e.key == key && e.number == number && e.declName == decl then
      if previous == entry then return
      throwError "Conflicting citation for {decl}: {key} {number}"
    let qualifier := if entry.relation == .exact then "" else
      s!" (partial:{entry.relation.label}; {comment})"
    let note := if entry.relation == .exact && !comment.isEmpty then s!" ({comment})" else ""
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let citation := s!"[{key} {number}]{qualifier}{note}"
    addDocStringCore decl <| "\n\n".intercalate ([oldDoc, citation].filter (· != ""))
    modifyEnv (citationExt.addEntry · entry)
}

private def nativeEntries (env : Environment) (key : String) : Array Entry := Id.run do
  let state := PersistentEnvExtension.getState Mathlib.CrossRef.tagExt env
  let tags := state.2.flatten.appendList state.1
  return tags.filterMap fun t =>
    if (key == "Kerodon" && t.database == .kerodon) ||
       (key == "Stacks" && t.database == .stacks) then
      some ⟨key, t.tag, t.declName, .exact, editionFor key, t.comment⟩
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
      ("edition", toJson entry.edition),
      ("relation", toJson (if key == "Kerodon" || key == "Stacks" then "native" else entry.relation.label)),
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
