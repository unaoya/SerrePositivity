module
public import SerrePositivity.EInfinity.ComplexLimits.DoubleConeIndex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeSimplex

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSimplex_obj_reindex {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) :
    (normalizedTensorDoubleConeSimplex A X Y c).obj (doubleConeOrderHom θ i) =
      (normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj i := by
  induction i using Fin.lastCases with
  | last => rw [doubleConeOrderHom_last, normalizedTensorDoubleConeSimplex_last,
      normalizedTensorDoubleConeSimplex_last]
  | cast i =>
    rw [doubleConeOrderHom_castSucc]
    change complexRightConeObj A (normalizedTensorConeSimplex A X Y c) X
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i).castSucc =
      complexRightConeObj A (normalizedTensorConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) X i.castSucc
    rw [complexRightConeObj_castSucc, complexRightConeObj_castSucc]
    exact normalizedTensorConeData_obj_prepend_map A X Y c θ i

lemma normalizedTensorDoubleConeSimplex_pullback_front {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((normalizedTensorDoubleConeSimplex A X Y c).pullback (doubleConeOrderHom θ)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      (normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).pullback
        Fin.castSuccOrderEmb.toOrderHom := by
  have hindex : (doubleConeOrderHom θ).comp Fin.castSuccOrderEmb.toOrderHom =
      Fin.castSuccOrderEmb.toOrderHom.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) := by
    apply DFunLike.ext
    intro i
    exact doubleConeOrderHom_castSucc θ i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hindex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp,
    normalizedTensorDoubleConeSimplex_front, normalizedTensorDoubleConeSimplex_front,
    normalizedTensorConeSimplex_pullback_map]

end SerrePositivity.EInfinity.ComplexLimits
