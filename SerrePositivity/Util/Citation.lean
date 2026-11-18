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
Kerodon and Stacks use Mathlib's attributes.
The citation keys and editions are not checked here: the registry generated from
`research/bibliography.json` lives in `SerrePositivity.Util.CitationRegistry`, which no mathematical
module imports, so adding a key does not rebuild the library (BR54, 2026-11-17). Unknown keys are
reported by `#cite_registry_check` (run by `scripts/audit_citations.lean`). The query commands
`#cite_tags`, `#cite_tags!` and `#cite_check` are in the registry module.
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
  comment : String
  deriving BEq, Inhabited



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
    if key == "Kerodon" || key == "Stacks" then
      throwError "Use Mathlib's native kerodon/stacks attribute for Tag references"
    let number := number.getString
    if number.trimAscii.toString.isEmpty then throwError "Citation number must not be empty"
    let relation ← part.mapM parseRelation
    let comment := (comment.map (·.getString)).getD ""
    if relation.isSome && comment.trimAscii.toString.isEmpty then
      throwError "A partial citation requires a nonempty reason"
    let entry : Entry := ⟨key, number, decl, relation.getD .exact, comment⟩
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

end SerrePositivity.Citation
