module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeTerminalValue

/-!
概要：二重 cone の終端を含む成分は、選択集合上単射な任意作用素の制限と一致する。
方針：元の終端成分と同じ閉 augmentation の再添字を、両側の実 cochain へ戻す。
規約：作用素全体の単射性は要求しない。使われ方：全終端成分の自然性。
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

lemma normalizedTensorDoubleConeSimplex_pullback_hom_terminal_injOn {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 3))) (a b : Fin (m + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (m + 2))
    (hi : Set.InjOn (doubleConeOrderHom θ) (I : Set (Fin (m + 3)))) :
    HEq (((normalizedTensorDoubleConeSimplex A X Y c).toSimplexData.pullback
      (doubleConeOrderHom θ)).hom I a b k hI ha hb hk)
      ((normalizedTensorDoubleConeSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk) := by
  let α := doubleConeOrderHom θ
  have hII := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI
  have haI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
    (show IsLeast (I : Set (Fin (m + 3))) a by rw [ha]; exact I.isLeast_min' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hbI := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
    (show IsGreatest (I : Set (Fin (m + 3))) b by rw [hb]; exact I.isGreatest_max' _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII)
  have hkI : k = 2 - ((I.image α).card : ℤ) := by
    rw [Finset.card_image_of_injOn hi]
    exact hk
  have hbl' : α b = Fin.last (n + 2) := by rw [hbl]; exact doubleConeOrderHom_last θ
  have han : a ≠ Fin.last (m + 2) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have hl := complexRightConeData_hom_last A (normalizedTensorConeSimplexAugmentation A X Y c)
    (I.image α) (α a) (α b) k hII haI hbI hkI hbl'
  have hr := complexRightConeData_hom_last A (normalizedTensorConeSimplexAugmentation A X Y
    ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) I a b k hI ha hb hk hbl
  exact hl.trans ((normalizedTensorDoubleConeTerminalValue_reindex A X Y c θ a k han).trans hr.symm)

end SerrePositivity.EInfinity.ComplexLimits
