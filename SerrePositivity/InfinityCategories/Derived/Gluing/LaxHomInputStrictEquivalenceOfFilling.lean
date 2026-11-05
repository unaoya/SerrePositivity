module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputPathInverseOfFilling
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedInputStrictKanComplex
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputCoordinateComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition
/-! # 指定境界充填から元二入力付き同一対角比較の同値性へ

概要：入力付き path 比較の実逆射を、同じ二入力の厳密模型とその四座標模型へ移す。
方針：既存の厳密模型から path 模型への同値を相殺し、元二入力を保つ座標同型を合成する。
規約：入力を忘れず、指定境界充填だけを補助入力とする。
使われ方：元入力付きの正本比較の同値性を主比較の標的へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
  (hfill : ∃ T, (boundary 2).ι ≫ T = dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y)

include hfill in
lemma dgGluingLaxHomInputStrictComparison_equivalence_of_filling :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomInputStrictComparison R C D M X Y) := by
  have hs := dgGluingDerivedCompositionInputStrictPullback_kanComplex R C D M X Y
  have hp := dgGluingDerivedCompositionInputPathPullback_kanComplex R C D M X Y
  have he := dgGluingDerivedCompositionInputStrictPathComparison_equivalence R C D M X Y
  have hc : IsQCatEquivalence (dgGluingLaxHomInputStrictComparison R C D M X Y ≫
      dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y) := by
    have hpath := dgGluingLaxHomInputPathComparison_equivalence_of_filling R C D M X Y hfill
    exact hpath.isQCatEquivalence
  exact (he.isQCatEquivalence.cancel_right hc).isSimplicialHomotopyEquivalence

include hfill in
lemma dgGluingLaxHomInputCoordinateComparison_equivalence_of_filling :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomInputCoordinateComparison R C D M X Y) :=
  (dgGluingHomotopyEquivalence_postcomp_iso_iff
    (dgGluingLaxHomInputStrictComparison R C D M X Y)
    (dgGluingCompositionInputStrictCoordinatesIso R C D M X Y)).mpr
    (dgGluingLaxHomInputStrictComparison_equivalence_of_filling R C D M X Y hfill)
end SerrePositivity.InfinityCategories
