module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cylinders.CochainCylinderPrimitive

/-! 元円柱の比較 cochain は二端の差を微分に持ち、実射影により厳密に消える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] (K : Complex R)

lemma dgGluingCochainCylinderPrimitive_projection :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive K).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection K)) (add_zero (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection, biprod.inr_fst,
    Cochain.ofHom_zero, Cochain.comp_zero]

lemma dgGluingCochainCylinderPrimitive_boundary :
    δ (-1) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive K) =
      Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne K - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderZero K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive, δ_comp_ofHom, mappingCone.δ_inl,
    ← Cochain.ofHom_comp]
  congr 1
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderZero, biprod.lift_eq,
    Category.id_comp, add_sub_cancel_left]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
