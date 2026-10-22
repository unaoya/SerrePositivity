module
public import SerrePositivity.EInfinity.ComplexLimits.DoubleConeEndEdgeIndex
public import SerrePositivity.InfinityCategories.Derived.DGSimplexComponentExt

/-!
概要：元の二重 cone の先端と終端を結ぶ実辺を、同じ恒等射の通常単体へ同定する。
方針：終端成分の実 augmentation を回収し、先端の恒等射を全一単体の等式へ戻す。
規約：対象と実辺全体の厳密な一致。使われ方：slice 内の最初の頂点の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorDoubleConeSimplex_end_edge {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (normalizedTensorDoubleConeSimplex A X Y c).pullback (doubleConeEndEdgeOrderHom n) =
      closedNerveSimplex ((Functor.const (Fin 2)).obj X ⋙ complexToClosed A) := by
  apply Simplex.ext
  apply dgSimplexData_ext_of_components A (Complex A)
  · intro i
    fin_cases i
    · change complexRightConeObj A (normalizedTensorConeSimplex A X Y c) X
        (0 : Fin (n + 2)).castSucc = X
      rw [complexRightConeObj_castSucc]
      rfl
    · exact normalizedTensorDoubleConeSimplex_last A X Y c
  · intro I a b k hI ha hb hk
    have hU := two_eq_univ I hI
    subst I
    have ha0 : a = 0 := ha.trans ((Finset.min'_eq_iff _ _ 0).2
      ⟨by simp, fun i _ => Fin.zero_le i⟩)
    have hb1 : b = 1 := hb.trans ((Finset.max'_eq_iff _ _ 1).2
      ⟨by simp, fun i _ => Fin.le_last i⟩)
    have hk0 : k = 0 := by simpa using hk
    subst ha0 hb1 hk0
    rw [Simplex.pullback_data, SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
      (doubleConeEndEdgeOrderHom_injective n).injOn]
    change HEq _ (closedNerveHom ((complexToClosed A).map (𝟙 X)) 0)
    have hII := Index.image_two (doubleConeEndEdgeOrderHom_injective n).injOn hI
    have he := complexRightConeData_hom_last A (normalizedTensorConeSimplexAugmentation A X Y c)
      (Finset.univ.image (doubleConeEndEdgeOrderHom n))
      (doubleConeEndEdgeOrderHom n 0) (doubleConeEndEdgeOrderHom n 1) 0 hII
      (Index.image_min (doubleConeEndEdgeOrderHom n).monotone
        (by rw [ha]; exact Finset.univ.isLeast_min' _) (Index.nonempty hII))
      (Index.image_max (doubleConeEndEdgeOrderHom n).monotone
        (by rw [hb]; exact Finset.univ.isGreatest_max' _) (Index.nonempty hII))
      (by rw [Finset.card_image_of_injective _ (doubleConeEndEdgeOrderHom_injective n)]; exact hk)
      (doubleConeEndEdgeOrderHom_one n)
    have hi0 : (Fin.last (n + 1)).predAboveOrderHom (doubleConeEndEdgeOrderHom n 0) = 0 := by
      rw [doubleConeEndEdgeOrderHom_zero]
      change (Fin.last (n + 1)).predAbove ((0 : Fin (n + 2)).castSucc) = 0
      exact Fin.predAbove_last_castSucc
    have ht : ∀ i j : Fin (n + 2), i = j →
        HEq (closedNerveHom ((complexToClosed A).map
          (normalizedTensorConeAugmentationAt A X Y c i)) 0)
          (closedNerveHom ((complexToClosed A).map
            (normalizedTensorConeAugmentationAt A X Y c j)) 0) := by
      intro i j h
      subst j
      rfl
    have hv := ht _ _ hi0
    change HEq _ (closedNerveHom ((complexToClosed A).map (𝟙 X)) 0) at hv
    exact he.trans hv
end SerrePositivity.EInfinity.ComplexLimits
