module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectedCard

/-!
概要：明示次数の選択 cochain を、元の順序埋め込みの像の選択 cochain と比較する。
方針：元の両選択列を同じ全列として一致させ、最大点への輸送を異種等号で保持する。
規約：非単射な frame 射の後合成による逆推論は使わない。
使われ方：実 cone の混合成分の単射 pullback 整合性。
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

lemma normalizedTensorElementSelectedCochainAtMaxOfCard_image {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (normalizedTensorElementSelectedCochainAtMaxOfCard A X Y c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk) r
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hc))
      (normalizedTensorElementSelectedCochainAtMaxOfCard A X Y
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk r hc) := by
  have hcol :
      (SimplexCategory.toCat.map (normalizedTensorElementSelectionOfCard (J.image e) r
        (by rw [Finset.card_image_of_injective _ e.injective]; exact hc))).toFunctor ⋙ c =
      (SimplexCategory.toCat.map (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c) := by
    have hs := normalizedTensorElementSelectionOfCard_image J e hc
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
  have hl := normalizedTensorElementSelectedCochainAtMaxOfCard_raw A X Y c (J.image e)
    k (hJ.image e) (by rw [Finset.card_image_of_injective _ e.injective]; exact hk) r
    (by rw [Finset.card_image_of_injective _ e.injective]; exact hc)
  have hr := normalizedTensorElementSelectedCochainAtMaxOfCard_raw A X Y
    ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
    J k hJ hk r hc
  exact hl.trans ((ht _ _ hcol).trans hr.symm)

end SerrePositivity.EInfinity.ComplexLimits
