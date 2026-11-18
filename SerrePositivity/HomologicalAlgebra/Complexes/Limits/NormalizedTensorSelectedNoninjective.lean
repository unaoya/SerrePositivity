module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorNoninjectiveTop
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectedCard
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：選択集合上で非単射な作用素による元の選択 cochain は零である。
方針：同じ集合の昇順選択と作用素の合成を非単射とし、元の最上位成分の消滅を使う。
規約：元の最大点への輸送を保つ。使われ方：実 cone の全退化混合成分の自然性。
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

lemma normalizedTensorElementSelectedCochainAtMax_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hn : ¬Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) J k hJ hk = 0 := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp only [r]; omega
  let ε := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectionOfCard J r hc
  let φ := ε ≫ θ
  let c' := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  have hφ : ¬Function.Injective φ.toOrderHom := by
    intro hi
    apply hn
    intro i hii j hjj hij
    have henum := J.image_orderEmbOfFin_univ hc
    have hi' : i ∈ (Finset.univ : Finset (Fin (r + 1))).image (J.orderEmbOfFin hc) := by
      rw [henum]
      exact hii
    have hj' : j ∈ (Finset.univ : Finset (Fin (r + 1))).image (J.orderEmbOfFin hc) := by
      rw [henum]
      exact hjj
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hi'
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hj'
    have huv : u = v := hi (by
      change θ.toOrderHom (J.orderEmbOfFin hc u) = θ.toOrderHom (J.orderEmbOfFin hc v)
      rw [hu, hv]
      exact hij)
    exact hu.symm.trans ((congrArg (J.orderEmbOfFin hc) huv).trans hv)
  have hd : k = 1 - ((Finset.univ : Finset (Fin (r + 1))).card : ℤ) := by
    simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk
  have hz := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear_top_noninjective A X Y c φ hφ k hd
  have hz' : (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y
      ((SimplexCategory.toCat.map ε).toFunctor ⋙ c')).val.component
        Finset.univ k Finset.univ_nonempty hd = 0 := by
    have hcol : (SimplexCategory.toCat.map φ).toFunctor ⋙ c =
        (SimplexCategory.toCat.map ε).toFunctor ⋙ c' := by
      simp only [φ, c', CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor,
        CategoryTheory.Functor.assoc]
    have ht : ∀ (d e : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) r) (he : d = e),
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y d).val.component
          Finset.univ k Finset.univ_nonempty hd = 0 →
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalLinear A X Y e).val.component
          Finset.univ k Finset.univ_nonempty hd = 0 := by
      intro d e he h
      subst e
      exact h
    exact ht _ _ hcol hz
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax_eq_ofCard A X Y c' J k hJ hk]
  have he := _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMaxOfCard_raw A X Y c' J k hJ hk r hc
  have hy : (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c'.obj (J.max' hJ)) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c'.obj (ε.toOrderHom (Fin.last r))) :=
    congrArg (fun i => (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c'.obj i))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectionOfCard_last J r hc hJ).symm
  have h0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (x := X) (x' := X) (k := k) (l := k) rfl hy rfl
  exact eq_of_heq (he.trans ((heq_of_eq hz').trans h0.symm))

end SerrePositivity.ComplexLimits
