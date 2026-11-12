module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGSEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGExactInfinityFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-! # 全高次入力を保つ S_n の安定 ∞ 圏値関手
概要：厳密豊穣 S_n と厳密 dg 入力との合成に γ1 を適用する。
方針：元の非離散な Hom と実豊穣合成を coherentNerveMap の関手性で移す。
規約：S• の反復・実現・BF は後続。使われ方：実 S_n Perf の ∞ 関手化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の全パラメータ S_n の、安定 ∞ 圏と完全関手への実 ∞ 自己関手。 -/
def sExactInfinityEndofunctor (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (sExactCoreEnrichedEndofunctor n)

/-- 元の安定 ∞ 圏での値は、同じ全 gapped S_n の実安定模型。 -/
lemma sExactInfinityEndofunctor_vertex (n : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (sExactInfinityEndofunctor n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((sExactCoreEnrichedEndofunctor n).obj C) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ C

variable (A : Type u) [CommRing A]

/-- 元の全 native dg 入力族から、同じ実 S_n Perf を与える安定 ∞ 圏値関手。 -/
def presentedPerfectDGSInfinityFunctor (n : ℕ) :
    perfDGInputInfinity.{u, v} A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGSEnrichedFunctor A n)

/-- 元の実 Perf ∞ 関手と同じ実 S_n ∞ 自己関手の合成を回収する。 -/
lemma presentedPerfectDGSInfinityFunctor_comp (n : ℕ) :
    presentedPerfectDGSInfinityFunctor.{u, v} A n =
      presentedPerfectDGExactInfinityFunctor A ≫ sExactInfinityEndofunctor n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp (presentedPerfectDGEnrichedExactFunctor A)
    (sExactCoreEnrichedEndofunctor n)

/-- 元の dg 入力での ∞ 関手の値は、同じラベル付き実 Perf の全 gapped S_n。 -/
lemma presentedPerfectDGSInfinityFunctor_vertex (n : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGSInfinityFunctor A n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((presentedPerfectDGSEnrichedFunctor A n).obj C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ C

end SerrePositivity.KST.SConstruction
