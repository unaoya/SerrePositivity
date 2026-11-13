module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cylinders.CochainCylinderPrimitive

/-! 実円柱からの鎖写像は二端と全次数 primitive で一意に決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {K L : Complex R}

lemma dgGluingCochainCylinder_hom_ext (a b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinder K ⟶ L)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderZero K ≫ a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderZero K ≫ b)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne K ≫ a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne K ≫ b)
    (hP : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive K).comp (Cochain.ofHom a) (add_zero (-1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive K).comp (Cochain.ofHom b) (add_zero (-1))) : a = b := by
  change biprod.inl ≫ a = biprod.inl ≫ b at h₀
  have hr : mappingCone.inr (𝟙 K) ≫ biprod.inr ≫ a =
      mappingCone.inr (𝟙 K) ≫ biprod.inr ≫ b := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne] at h₁
    simp only [biprod.lift_eq, Preadditive.add_comp, Category.id_comp, Category.assoc] at h₁
    rw [h₀] at h₁
    exact add_left_cancel h₁
  have hC : (mappingCone.inl (𝟙 K)).comp
      (Cochain.ofHom (biprod.inr ≫ a)) (add_zero (-1)) =
      (mappingCone.inl (𝟙 K)).comp
      (Cochain.ofHom (biprod.inr ≫ b)) (add_zero (-1)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp] using hP
  apply biprod.hom_ext'
  · exact h₀
  · apply HomologicalComplex.hom_ext
    intro n
    apply mappingCone.ext_from (𝟙 K) (n + 1) n rfl
    · have hv := Cochain.congr_v hC (n + 1) n (by omega)
      simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using hv
    · exact HomologicalComplex.congr_hom hr n

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
