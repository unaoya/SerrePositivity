/-
Adapted from Batteries/Tactic/Alias.lean (Apache 2.0).
Original authors: Mario Carneiro, David Renshaw, François G. Dorais.
-/
module

public meta import Mathlib.Util.AliasIn
public meta import Lean.Compiler.LCNF.PhaseExt

/-!
# 名前空間移動後の互換 alias

概要：宇宙・束縛子を保つ deprecated な略記と定理 alias を生成する。
方針：型では登録済みの旧名を使い、旧型の field notation を保つ。
規約：本体は新名の定数そのもの。生成宣言は kernel が検査する。
使われ方：IF-F F-2。instance・simp は新名側にのみ登録する。
-/

public meta section
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open Lean Elab Parser.Command Batteries.Tactic.Alias

private def insertAlias (s : NameMap Name) (e : Name × Name) : NameMap Name :=
  s.insert e.1 e.2

initialize typeAliases : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := insertAlias
    addImportedFn := mkStateFromImportedEntries insertAlias {}
  }

/-- A deprecated abbreviation (or theorem alias) with exact binders and legacy type names. -/
elab mods:declModifiers "deprecated_alias " oldStx:ident " := " newStx:ident : command => do
  Lean.withExporting (isExporting := (← Command.getScope).isPublic) do
  Command.liftTermElabM do
    let name ← withoutExporting <| realizeGlobalConstNoOverloadWithInfo newStx
    let ci ← withoutExporting <| getConstInfo name
    if isPrivateName name then throwError "deprecated_alias cannot publish a private declaration"
    let dm ← elabModifiers mods
    Lean.withExporting (isExporting := dm.isInferredPublic (← getEnv)) do
    let env ← getEnv
    let (attrs, machineApplicable) := setDeprecatedTarget name dm.attrs
    let recursor := match ci with | .recInfo _ => true | _ => false
    let noncomp := isNoncomputable env name || recursor
    let dm := { dm with
      attrs := attrs
      computeKind :=
        if noncomp then .noncomputable
        else if isMarkedMeta env name then .meta
        else dm.computeKind
      isUnsafe := dm.isUnsafe || ci.isUnsafe || ci.isPartial }
    unless dm.isInferredPublic env do throwError "deprecated_alias requires public visibility"
    let currentNamespace ← getCurrNamespace
    let written := oldStx.getId
    let old := if (`_root_).isPrefixOf written then written.replacePrefix `_root_ Name.anonymous
      else currentNamespace ++ written
    checkIfShadowingStructureField old
    if (env.setExporting false).contains old then throwError "alias name is already declared: {old}"
    if old == name then throwError "alias must have a distinct name"
    -- Generated equation names are reserved by Lean's elaborator. They are deliberately
    -- supplied here as aliases of the original equations, not regenerated from the wrapper.
    -- addDecl still checks uniqueness, universes, type and value in the kernel.
    let aliases := typeAliases.getState env
    let type := ci.type.replace fun e => match e with
      | .const n ls => (aliases.find? n).map fun oldName => mkConst oldName ls
      | _ => none
    let val := mkConst name (ci.levelParams.map mkLevelParam)
    let decl := if wasOriginallyTheorem env name then
      Declaration.thmDecl { ci.toConstantVal with
        name := old
        type := type
        value := val }
    else
      Declaration.defnDecl { ci.toConstantVal with
        name := old
        type := type
        value := val
        hints := .abbrev
        safety := if dm.isUnsafe then .unsafe else .safe }
    addDecl decl
    unless wasOriginallyTheorem env name do setReducibilityStatus old .reducible
    -- LCNF compiles a `_unsafe_rec` declaration under its parent's name. A plain
    -- parent alias has already emitted that code, so compiling its auxiliary alias
    -- again would register the same impure declarations twice. Keep both kernel
    -- declarations and their computability while reusing the emitted parent code.
    let reusesParentCode : Bool ← match Compiler.isUnsafeRecName? old, Compiler.isUnsafeRecName? name with
      | some oldParent, some newParent => do
        if aliases.find? newParent == some oldParent then
          pure (← Compiler.LCNF.getBaseDecl? oldParent).isSome
        else pure false
      | _, _ => pure false
    if !dm.isNoncomputable then
      if dm.isMeta then modifyEnv (markMeta · old)
      unless reusesParentCode do compileDecl decl
    else modifyEnv (addNoncomputable · old)
    addDeclarationRangesFromSyntax old (← getRef) oldStx
    Term.addTermInfo' oldStx (← mkConstWithLevelParams old) (isBinder := true)
    enableRealizationsForConst old
    let info := AliasInfo.plain name
    setAliasInfo info old
    Term.applyAttributes old dm.attrs
    if machineApplicable then modifyEnv (Batteries.machineApplicableDeprecated.tag · old)
    addAliasDocstring old info
    modifyEnv (typeAliases.addEntry · (name, old))
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
