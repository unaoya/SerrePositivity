module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainCylinderMap

/-! 円柱の次数 −1 の元を明示し、全次数の自然性と extension の実 primitive を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R]

def dgGluingCochainCylinderPrimitive (K : Complex R) :
    Cochain K (dgGluingCochainCylinder K) (-1) :=
  (mappingCone.inl (𝟙 K)).comp
    (Cochain.ofHom (biprod.inr : mappingCone (𝟙 K) ⟶ dgGluingCochainCylinder K)) (add_zero (-1))

lemma dgGluingCochainCylinderPrimitive_extension {K L : Complex R}
    (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f)) :
    (dgGluingCochainCylinderPrimitive K).comp
      (Cochain.ofHom (dgGluingCochainCylinderExtension f g h he)) (add_zero (-1)) = h := by
  rw [dgGluingCochainCylinderPrimitive, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, dgGluingCochainCylinderExtension, biprod.inr_desc,
    mappingCone.inl_desc]

lemma dgGluingCochainCylinderPrimitive_map {K L : Complex R} (a : K ⟶ L) :
    (dgGluingCochainCylinderPrimitive K).comp
      (Cochain.ofHom (dgGluingCochainCylinderMap a)) (add_zero (-1)) =
    (Cochain.ofHom a).comp (dgGluingCochainCylinderPrimitive L) (zero_add (-1)) := by
  rw [dgGluingCochainCylinderPrimitive, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, dgGluingCochainCylinderMap, biprod.inr_map,
    Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    dgGluingCochainCylinderConeMap_inl, Cochain.comp_assoc_of_first_is_zero_cochain]
  rfl

end SerrePositivity.InfinityCategories
