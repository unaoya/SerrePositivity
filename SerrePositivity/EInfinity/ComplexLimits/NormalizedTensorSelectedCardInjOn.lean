module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedCard
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectionInjOn

/-!
概要：明示次数の選択 cochain を、元の集合上単射な作用素の像の選択 cochain と比較する。
方針：元の両選択列を同じ全列として一致させ、最大点への輸送を異種等号で保持する。
規約：非単射な frame 射の後合成による逆推論は使わない。
使われ方：実 cone の混合成分の全 pullback 整合性。
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

lemma normalizedTensorElementSelectedCochainAtMaxOfCard_image_of_injOn {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) (r : ℕ) (hc : J.card = r + 1) :
    HEq (normalizedTensorElementSelectedCochainAtMaxOfCard A X Y c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk) r
      (by rw [Finset.card_image_of_injOn hi]; exact hc))
      (normalizedTensorElementSelectedCochainAtMaxOfCard A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk r hc) := by
  have hcol :
      (SimplexCategory.toCat.map (normalizedTensorElementSelectionOfCard (J.image θ.toOrderHom) r
        (by rw [Finset.card_image_of_injOn hi]; exact hc))).toFunctor ⋙ c =
      (SimplexCategory.toCat.map (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
    have hs := normalizedTensorElementSelectionOfCard_image_of_injOn J θ hc hi
    have hf := congrArg (fun θ : ⦋r⦌ ⟶ ⦋n⦌ =>
      (SimplexCategory.toCat.map θ).toFunctor ⋙ c) hs
    exact hf.trans (by simp only [CategoryTheory.Functor.map_comp]; rfl)
  have hd : k = 1 - ((Finset.univ : Finset (Fin (r + 1))).card : ℤ) := by
    simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk
  have ht : ∀ (c d : ComposableArrows (normalizedTensorElementIndex A X Y) r) (he : c = d),
      HEq ((normalizedTensorElementUniversalLinear A X Y c).val.component
        Finset.univ k Finset.univ_nonempty hd)
        ((normalizedTensorElementUniversalLinear A X Y d).val.component
          Finset.univ k Finset.univ_nonempty hd) := by
    intro c d he
    subst d
    rfl
  have hl := normalizedTensorElementSelectedCochainAtMaxOfCard_raw A X Y c (J.image θ.toOrderHom)
    k (hJ.image θ.toOrderHom) (by rw [Finset.card_image_of_injOn hi]; exact hk) r
    (by rw [Finset.card_image_of_injOn hi]; exact hc)
  have hr := normalizedTensorElementSelectedCochainAtMaxOfCard_raw A X Y
    ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
    J k hJ hk r hc
  exact hl.trans ((ht _ _ hcol).trans hr.symm)

end SerrePositivity.EInfinity.ComplexLimits
