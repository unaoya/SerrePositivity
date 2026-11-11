module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEnrichedExactFunctor

/-! # 元の全 dg 入力からの安定 ∞ 圏値 Perf 関手
概要：厳密豊穣完全 Perf 関手に γ1 を適用し、安定 ∞ 圏と完全関手の ∞ 関手を得る。
方針：既存の coherentNerveMap に元の非離散な豊穣関手を渡す。
規約：BF K・Sp 値化は後続。使われ方：K の厳密豊穣作用に先立つ完全な Perf 入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全 native dg 入力を持つ、安定 ∞ 圏と完全関手への実 Perf ∞ 関手。 -/
def presentedPerfectDGExactInfinityFunctor :
    perfDGInputInfinity.{u, v} A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGEnrichedExactFunctor A)

/-- 元の各 dg 圏での ∞ 関手の値は、同じラベル付き実安定 Perf 模型。 -/
lemma presentedPerfectDGExactInfinityFunctor_vertex (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGExactInfinityFunctor A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex C) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (presentedPerfectDGStableQCat A C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ C

end SerrePositivity.KST.SConstruction
