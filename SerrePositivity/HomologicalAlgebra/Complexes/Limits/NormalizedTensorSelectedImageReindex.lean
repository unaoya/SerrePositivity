module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedCardImage

/-!
概要：元の最大点付き選択 cochain は、順序埋め込みの像で選択した実 cochain と一致する。
方針：濃度の保存で明示次数をそろえ、同じ選択列の比較から元の表示へ戻す。
規約：元の cochain・最大点・次数を保持する。
使われ方：実 cone の混合成分と同じ単射による制限の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_image_reindex {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk) := by
  have hcard : (J.image e).card = J.card := Finset.card_image_of_injective _ e.injective
  have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  have hki : k = 1 - ((J.image e).card : ℤ) := by rw [hcard]; exact hk
  have hl := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_eq_ofCard
    A X Y c (J.image e) k (hJ.image e) hki
  have hdim := congrArg (fun t : ℕ => t - 1) hcard
  have ht := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMaxOfCard_congr
    A X Y c (J.image e) k (hJ.image e) hki _ _ hdim
    (by have := Finset.card_pos.mpr (hJ.image e); omega) (hcard.trans hc)
  have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMaxOfCard_image A X Y c e J k hJ hk
    (J.card - 1) hc
  have hr := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_eq_ofCard A X Y
    ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c) J k hJ hk
  exact (heq_of_eq (hl.trans ht)).trans (he.trans (heq_of_eq hr.symm))

lemma normalizedTensorElementSelectedCochainAtMax_image_reindex_smul {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (r : ℤˣ) :
    HEq (r • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk))
      (r • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk) := by
  have hm : (J.image e).max' (hJ.image e) = e (J.max' hJ) :=
    Finset.max'_image e.monotone J _
  have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_image_reindex A X Y c e J k hJ hk
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj i)) k)
      (w : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj j)) k),
      HEq v w → HEq (r • v) (r • w) := by
    intro i j h v w hv
    subst j
    cases eq_of_heq hv
    rfl
  exact ht _ _ hm _ _ he

end SerrePositivity.ComplexLimits
