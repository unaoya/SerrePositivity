-- 5∞-0の新規モジュール全宣言を検査する小監査。対象制限は新規7モジュールの全宣言。
import SerrePositivity.CommutativeAlgebra.PowerTorsion.Bounded
import SerrePositivity.BhattScholze.Semiperfectoid.Basic
import SerrePositivity.BhattScholze.Prism.Basic.Category
import SerrePositivity.BhattScholze.Prism.Basic.PerfectBounded
import SerrePositivity.BhattScholze.Prismatic.Site.PrismOverSmall
import SerrePositivity.BhattScholze.Prismatic.Site.PerfectSite
import SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates
import Mathlib.Util.AssertNoSorry
import Lean

open Lean Elab Command

run_cmd do
  let mods : Array Name := #[
    `SerrePositivity.CommutativeAlgebra.PowerTorsion.Bounded,
    `SerrePositivity.BhattScholze.Semiperfectoid.Basic,
    `SerrePositivity.BhattScholze.Prism.Basic.Category,
    `SerrePositivity.BhattScholze.Prism.Basic.PerfectBounded,
    `SerrePositivity.BhattScholze.Prismatic.Site.PrismOverSmall,
    `SerrePositivity.BhattScholze.Prismatic.Site.PerfectSite,
    `SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates]
  let required : Array Name := #[
    `SerrePositivity.HasBoundedPTorsion,
    `SerrePositivity.BhattScholze.IsSemiperfectoid,
    `SerrePositivity.BhattScholze.OrientedPrismCat,
    `SerrePositivity.BhattScholze.OrientedPrism.Hom.IsFlat,
    `SerrePositivity.BhattScholze.OrientedPrism.Hom.IsFaithfullyFlat,
    `SerrePositivity.BhattScholze.OrientedPrism.isDistinguished_of_span_eq,
    `SerrePositivity.BhattScholze.Prismatic.isBoundedPrism_of_perfect,
    `SerrePositivity.BhattScholze.Prismatic.PrismOver.essentiallySmall,
    `SerrePositivity.BhattScholze.Prismatic.perfectPrismaticTopology,
    `SerrePositivity.DerivedInfinity.IsConnectiveAt,
    `SerrePositivity.DerivedInfinity.IsPComplete]
  let env ← getEnv
  for name in required do
    unless env.contains name do throwError "5inf-0: missing required declaration {name}"
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless mods.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "5inf-0: unexpected axioms in {name}: {axioms}"
    count := count + 1
    if !seen.contains mod then seen := seen.push mod
  for mod in mods do
    unless seen.contains mod do throwError "5inf-0: no declarations checked in {mod}"
  logInfo m!"5inf-0 audit passed: {count} declarations, all seven modules, standard three axioms only."
