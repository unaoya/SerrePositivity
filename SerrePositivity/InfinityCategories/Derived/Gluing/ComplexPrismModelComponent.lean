module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainPrismModelComponent
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainCorrectionValue
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainUnitHomCancellation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainAugmentationHomotopy

/-! 元 dg Hom 上の複体 prism の実出力は、単位 Hom の逆により同じ二作用・補正値へ戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex HomologicalComplex
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max u v)) [DGCategory R C]
  {a b : C} {L : Complex R} (f g : homObject R C a b ⟶ L)
  (h : Cochain (homObject R C a b) L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  {n : ℕ} (s : (DGNerve.pinchedHom R C a b) _⦋n⦌)

lemma dgGluingComplexPrismCorrectionValue_unit_cancel
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    (complexUnitHomIso L).inv.f k
        (dgGluingCochainPrismCorrectionValue R C (DGComplexPinchedModel.{u, max u v} L)
          (complexPinchedSource L) (complexPinchedTarget L)
          (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1))) s β J k hk) =
      dgGluingComplexCochainCorrectionValue R C h s β J k hk := by
  change (complexUnitHomIso L).inv.f k (dgGluingComplexCochainCorrectionValue R C
    (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1))) s β J k hk) = _
  rw [dgGluingComplexCochainCorrectionValue_post, dgGluingCochainUnitHom_cancel]

lemma dgGluingComplexPrism_model_component (β : (Δ[1] : SSet.{max u v}) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (complexUnitHomIso L).inv.f k
        ((toLinearData ((dgGluingComplexCochainAugmentationPrism.{u, v} f g h he).app
          (Opposite.op ⦋n⦌)
          (β, (pinchedComplexModelIso a b).hom.app (Opposite.op ⦋n⦌) s))).component
          J k hJ hk) =
      if (SSet.stdSimplex.objEquiv β).toOrderHom (J.min' hJ) = 1 then
        g.f k ((toLinearData s).component J k hJ hk)
      else f.f k ((toLinearData s).component J k hJ hk) +
        dgGluingComplexCochainCorrectionValue R C h s (SSet.stdSimplex.objEquiv β).toOrderHom
          J k hk := by
  have hc := dgGluingCochainPrism_model_component R C (DGComplexPinchedModel.{u, max u v} L)
    (complexPinchedSource L) (complexPinchedTarget L)
    (f ≫ (complexUnitHomIso L).hom) (g ≫ (complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1)))
    (dgGluingCochainUnitHom_boundary f g h he) s β J k hJ hk
  have hr := congrArg (fun z => (complexUnitHomIso L).inv.f k z) hc
  by_cases hb : (SSet.stdSimplex.objEquiv β).toOrderHom (J.min' hJ) = 1
  · rw [ite_eq_left hb] at hr ⊢
    exact hr.trans (dgGluingComplexUnitHom_inv_apply L k
      (g.f k ((toLinearData s).component J k hJ hk)))
  · rw [ite_eq_right hb] at hr ⊢
    rw [map_add] at hr
    exact hr.trans (congrArg₂ (fun a b : L.X k => a + b)
      (dgGluingComplexUnitHom_inv_apply L k (f.f k ((toLinearData s).component J k hJ hk)))
      (dgGluingComplexPrismCorrectionValue_unit_cancel R C h s _ J k hk))

end SerrePositivity.InfinityCategories
