module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomInputPathInverseOfFilling
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DerivedInputStrictKanComplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomInputCoordinateComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyIsoPrecomposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (hfill : ∃ T, (boundary 2).ι ≫ T = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y)

include hfill in
lemma dgGluingLaxHomInputStrictComparison_equivalence_of_filling :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputStrictComparison R C D M X Y) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputStrictPullback_kanComplex R C D M X Y
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathPullback_kanComplex R C D M X Y
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputStrictPathComparison_equivalence R C D M X Y
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputStrictComparison R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y) := by
    have hpath := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputPathComparison_equivalence_of_filling R C D M X Y hfill
    exact hpath.isQCatEquivalence
  exact (he.isQCatEquivalence.cancel_right hc).isSimplicialHomotopyEquivalence

include hfill in
lemma dgGluingLaxHomInputCoordinateComparison_equivalence_of_filling :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputCoordinateComparison R C D M X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_postcomp_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputStrictComparison R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionInputStrictCoordinatesIso R C D M X Y)).mpr
    (dgGluingLaxHomInputStrictComparison_equivalence_of_filling R C D M X Y hfill)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
