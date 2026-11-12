module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.YonedaHomCone

/-! 同じ加群円錐の左包含を、Yoneda 評価の逆を通して回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (x : C) {P Q : ModuleCategory R C} (f : P ⟶ Q)
local notation "T" => ForgetEnrichment.of (Complex R) (representable R x)
local notation "U" => ForgetEnrichment.to (Complex R) P
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R C f)

/-- 左包含の逆 Yoneda 評価は、同じ全 Hom 左包含への閉前合成。 -/
lemma dgGluingYonedaHomCone_inl_inv :
    (mappingCone.inl ((moduleEvaluation R C x).map f)).comp
      (Cochain.ofHom (dgYonedaIso R x K).inv) (add_zero (-1)) =
    (Cochain.ofHom (dgYonedaIso R x U).inv).comp
      (moduleHomConeLeftCochain R C T f) (zero_add (-1)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaHomCone_inl R C x f
  have hh := congrArg (fun z =>
    ((Cochain.ofHom (dgYonedaIso R x U).inv).comp z (zero_add (-1))).comp
      (Cochain.ofHom (dgYonedaIso R x K).inv) (add_zero (-1))) h
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    Iso.hom_inv_id, Cochain.comp_id] at hh
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    Iso.inv_hom_id, Cochain.id_comp] at hh
  exact hh.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
