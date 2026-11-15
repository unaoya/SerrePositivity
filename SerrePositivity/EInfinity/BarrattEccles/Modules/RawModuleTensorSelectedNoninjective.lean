module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorNoninjectiveTop
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedCard
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
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hn : ¬Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    strictRawModuleTensorElementSelectedCochainAtMax A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) J k hJ hk = 0 := by
  let r := J.card - 1
  have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp only [r]; omega
  let ε := normalizedTensorElementSelectionOfCard J r hc
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
  have hz := strictRawModuleTensorElementLinear_top_noninjective A X P Q c φ hφ k hd
  have hz' : (strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map ε).toFunctor ⋙ c')).val.component
        Finset.univ k Finset.univ_nonempty hd = 0 := by
    have hcol : (SimplexCategory.toCat.map φ).toFunctor ⋙ c =
        (SimplexCategory.toCat.map ε).toFunctor ⋙ c' := by
      simp only [φ, c', CategoryTheory.Functor.map_comp, Cat.Hom.comp_toFunctor,
        CategoryTheory.Functor.assoc]
    have ht : ∀ (d e : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) r) (he : d = e),
        (strictRawModuleTensorElementLinear A X P Q d).val.component
          Finset.univ k Finset.univ_nonempty hd = 0 →
        (strictRawModuleTensorElementLinear A X P Q e).val.component
          Finset.univ k Finset.univ_nonempty hd = 0 := by
      intro d e he h
      subst e
      exact h
    exact ht _ _ hcol hz
  rw [strictRawModuleTensorElementSelectedCochainAtMax_eq_ofCard A X P Q c' J k hJ hk]
  have he := strictRawModuleTensorElementSelectedCochainAtMaxOfCard_raw A X P Q c' J k hJ hk r hc
  have hy : ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c'.obj (J.max' hJ))) =
      ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c'.obj (ε.toOrderHom (Fin.last r)))) :=
    congrArg (fun i => ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c'.obj i)))
      (normalizedTensorElementSelectionOfCard_last J r hc hJ).symm
  have h0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (x := (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))) (x' := (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))) (k := k) (l := k) rfl hy rfl
  exact eq_of_heq (he.trans ((heq_of_eq hz').trans h0.symm))

end SerrePositivity.EInfinity.BarrattEccles
