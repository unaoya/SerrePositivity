module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEnrichedRecovery
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-! # 元の全高次厳密 dg 入力からの Cat∞ 値 Perf 関手
概要：実単体的豊穣 Perf 関手に γ1 の coherent nerve の関手性を適用する。
方針：出力宇宙の入力も QCat も局所 Kan であり、同じ対象・Hom 宇宙で nerve を取る。
規約：元の全高次入力を保持。使われ方：安定性・完全性を介した Sp 値 K への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 出力宇宙に移した元の厳密 dg 入力の、全 native Kan Hom を保つ coherent nerve。 -/
def perfDGInputInfinity : SSet.{max (u + 2) (v + 1)} :=
  SimplicialNerve (PerfDGInput.{u, v} A)

/-- 出力宇宙の元の厳密 dg 入力の nerve は、局所 Kan 性から ∞ 圏。 -/
instance perfDGInputInfinity_quasicategory : Quasicategory (perfDGInputInfinity.{u, v} A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (PerfDGInput.{u, v} A)

/-- 元の全高次入力を保つ厳密豊穣 Perf 関手から、γ1 で得る Cat∞ 値 ∞ 関手。 -/
def presentedPerfectDGInfinityFunctor :
    perfDGInputInfinity.{u, v} A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGEnrichedFunctor A)

/-- γ1 による実 Perf 関手は、元の dg 入力の頂点を同じ native Perf の頂点へ送る。 -/
lemma presentedPerfectDGInfinityFunctor_vertex (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGInfinityFunctor A).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (presentedPerfectDGQCat A C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (presentedPerfectDGEnrichedFunctor A) C

end SerrePositivity.KST.SConstruction
