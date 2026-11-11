import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveReflectsQuasiEquivalence
import Lean

/-! 新二葉の全宣言を標準三公理で監査し、前三角な始域だけを仮定する公開型を照合する。 -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets := #[
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedGradedShift,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveReflectsQuasiEquivalence]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless targets.contains env.header.modules[index.toNat]!.module do continue
    for dependency in ← collectAxioms name do
      unless allowed.contains dependency do
        throwError "Forbidden axiom {dependency} in {name}"
    count := count + 1
  unless count > 0 do throwError "No declarations checked"
  logInfo m!"DG nerve reflection audit passed: {count} declarations."

open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

universe u v

-- 依頼された u+1 の対象宇宙で、始域だけの前三角性から準同値を得る。
example (R : Type u) [CommRing R] (C E : Type (u + 1))
    [DGCategory R C] [Small.{u} C] [DGCategory R E] [Small.{u} E]
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] (F : DGFunctor R C E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)) : QuasiEquivalence F :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_quasiEquivalence_of_nerve R C E F hF

-- 標的の Small・前三角性は要求しない強い公開型。
example (R : Type u) [CommRing R] (C E : Type v)
    [DGCategory R C] [Small.{u} C] [DGCategory R E]
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] (F : DGFunctor R C E)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)) : HomQuasiIso F :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_homQuasiIso_of_nerve R C E F hF

#print axioms _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulated_gradedShiftWitness
#print axioms _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_onHomotopy_isEquivalence_of_nerve
#print axioms _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_homQuasiIso_of_nerve
#print axioms _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_quasiEquivalence_of_nerve
