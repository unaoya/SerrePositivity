module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedCard
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
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_image_of_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk) r
      (by rw [Finset.card_image_of_injOn hi]; exact hc))
      (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q
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
  have ht : ∀ (c d : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) r) (he : c = d),
      HEq ((strictRawModuleTensorElementLinear A X P Q c).val.component
        Finset.univ k Finset.univ_nonempty hd)
        ((strictRawModuleTensorElementLinear A X P Q d).val.component
          Finset.univ k Finset.univ_nonempty hd) := by
    intro c d he
    subst d
    rfl
  have hl := strictRawModuleTensorElementSelectedCochainAtMaxOfCard_raw A X P Q c (J.image θ.toOrderHom)
    k (hJ.image θ.toOrderHom) (by rw [Finset.card_image_of_injOn hi]; exact hk) r
    (by rw [Finset.card_image_of_injOn hi]; exact hc)
  have hr := strictRawModuleTensorElementSelectedCochainAtMaxOfCard_raw A X P Q
    ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
    J k hJ hk r hc
  exact hl.trans ((ht _ _ hcol).trans hr.symm)

end SerrePositivity.EInfinity.BarrattEccles
