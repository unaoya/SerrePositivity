module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoubleConeIndex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeSimplex

/-!
概要：二重 cone の対象と全前面制限は、元の任意作用素による制限と整合する。
方針：対象は終点と前面に分け、前面全体は既存の cone の全自然性へ戻す。
規約：退化も含む全作用素。使われ方：全通常成分の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSimplex_obj_reindex {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).obj (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ i) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj i := by
  induction i using Fin.lastCases with
  | last => rw [_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_last, _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_last,
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_last]
  | cast i =>
    rw [_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_castSucc]
    change _root_.SerrePositivity.ComplexLimits.complexRightConeObj A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c) X
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i).castSucc =
      _root_.SerrePositivity.ComplexLimits.complexRightConeObj A (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) X i.castSucc
    rw [_root_.SerrePositivity.ComplexLimits.complexRightConeObj_castSucc, _root_.SerrePositivity.ComplexLimits.complexRightConeObj_castSucc]
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_obj_prepend_map A X Y c θ i

lemma normalizedTensorDoubleConeSimplex_pullback_front {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c).pullback (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).pullback
        Fin.castSuccOrderEmb.toOrderHom := by
  have hindex : (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) := by
    apply DFunLike.ext
    intro i
    exact _root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_castSucc θ i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_front, _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex_front,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex_pullback_map]

end SerrePositivity.ComplexLimits
