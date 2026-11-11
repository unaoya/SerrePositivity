module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainPrismModelComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexCochainCorrectionValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainUnitHomCancellation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexCochainAugmentationHomotopy

/-! 元 dg Hom 上の複体 prism の実出力は、単位 Hom の逆により同じ二作用・補正値へ戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex HomologicalComplex

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  {a b : C} {L : _root_.SerrePositivity.DifferentialGraded.Complex R} (f g : _root_.SerrePositivity.DifferentialGraded.homObject R C a b ⟶ L)
  (h : Cochain (_root_.SerrePositivity.DifferentialGraded.homObject R C a b) L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C a b) _⦋n⦌)

lemma dgGluingComplexPrismCorrectionValue_unit_cancel
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).inv.f k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPrismCorrectionValue R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
          (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1))) s β J k hk) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainCorrectionValue R C h s β J k hk := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).inv.f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainCorrectionValue R C
    (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1))) s β J k hk) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainCorrectionValue_post, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_cancel]

lemma dgGluingComplexPrism_model_component (β : (Δ[1] : SSet.{max u v}) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).inv.f k
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} f g h he).app
          (Opposite.op ⦋n⦌)
          (β, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso a b).hom.app (Opposite.op ⦋n⦌) s))).component
          J k hJ hk) =
      if (SSet.stdSimplex.objEquiv β).toOrderHom (J.min' hJ) = 1 then
        g.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)
      else f.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk) +
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainCorrectionValue R C h s (SSet.stdSimplex.objEquiv β).toOrderHom
          J k hk := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPrism_model_component R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
    (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_boundary f g h he) s β J k hJ hk
  have hr := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).inv.f k z) hc
  by_cases hb : (SSet.stdSimplex.objEquiv β).toOrderHom (J.min' hJ) = 1
  · rw [ite_eq_left hb] at hr ⊢
    exact hr.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexUnitHom_inv_apply L k
      (g.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)))
  · rw [ite_eq_right hb] at hr ⊢
    rw [map_add] at hr
    exact hr.trans (congrArg₂ (fun a b : L.X k => a + b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexUnitHom_inv_apply L k (f.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)))
      (dgGluingComplexPrismCorrectionValue_unit_cancel R C h s _ J k hk))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
