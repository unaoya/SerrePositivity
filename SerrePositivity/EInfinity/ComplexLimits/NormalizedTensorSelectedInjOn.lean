module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedCardInjOn

/-!
概要：元の最大点付き選択 cochain は、選択集合上で単射な作用素の像で選択した実 cochain と一致する。
方針：濃度の保存で明示次数をそろえ、同じ選択列の比較から元の表示へ戻す。
規約：元の cochain・最大点・次数を保持する。
使われ方：実 cone の混合成分と同じ単射による制限の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementSelectedCochainAtMax_image_reindex_of_injOn {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    HEq (normalizedTensorElementSelectedCochainAtMax A X Y c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk))
      (normalizedTensorElementSelectedCochainAtMax A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk) := by
  have hcard : (J.image θ.toOrderHom).card = J.card := Finset.card_image_of_injOn hi
  have hc : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  have hki : k = 1 - ((J.image θ.toOrderHom).card : ℤ) := by rw [hcard]; exact hk
  have hl := normalizedTensorElementSelectedCochainAtMax_eq_ofCard
    A X Y c (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom) hki
  have hdim := congrArg (fun t : ℕ => t - 1) hcard
  have ht := normalizedTensorElementSelectedCochainAtMaxOfCard_congr
    A X Y c (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom) hki _ _ hdim
    (by have := Finset.card_pos.mpr (hJ.image θ.toOrderHom); omega) (hcard.trans hc)
  have he := normalizedTensorElementSelectedCochainAtMaxOfCard_image_of_injOn A X Y c θ J k hJ hk hi
    (J.card - 1) hc
  have hr := normalizedTensorElementSelectedCochainAtMax_eq_ofCard A X Y
    ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) J k hJ hk
  exact (heq_of_eq (hl.trans ht)).trans (he.trans (heq_of_eq hr.symm))

lemma normalizedTensorElementSelectedCochainAtMax_image_reindex_of_injOn_smul {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) (r : ℤˣ) :
    HEq (r • normalizedTensorElementSelectedCochainAtMax A X Y c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk))
      (r • normalizedTensorElementSelectedCochainAtMax A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk) := by
  have hm : (J.image θ.toOrderHom).max' (hJ.image θ.toOrderHom) = θ.toOrderHom (J.max' hJ) :=
    Finset.max'_image θ.toOrderHom.monotone J _
  have he := normalizedTensorElementSelectedCochainAtMax_image_reindex_of_injOn
    A X Y c θ J k hJ hk hi
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A X ((normalizedTensorElementDiagram A X Y).obj (c.obj i)) k)
      (w : GradedHom A X ((normalizedTensorElementDiagram A X Y).obj (c.obj j)) k),
      HEq v w → HEq (r • v) (r • w) := by
    intro i j h v w hv
    subst j
    cases eq_of_heq hv
    rfl
  exact ht _ _ hm _ _ he

end SerrePositivity.EInfinity.ComplexLimits
