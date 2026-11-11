module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PrimitiveComparison
/-! 実 cocone の右包含と Hom の Yoneda 比較同型の厳密な整合性。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (μ : P ⟶ S) (ν : Q ⟶ T) (a : P ⟶ Q) (b : S ⟶ T) (h : μ ≫ b = a ≫ ν)
lemma dgGluingCoconeMap_inr :
    (mappingCocone.inr μ).val.comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap μ ν a b h)) (add_zero 1) =
    (Cochain.ofHom b).comp (mappingCocone.inr ν).val (zero_add 1) := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_X_ext ν q
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_fst_f,
      mappingCocone.inr_v_fst_f_assoc, mappingCocone.inr_v_fst_f, comp_zero, zero_comp]
  · obtain rfl : p = q - 1 := by omega
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v]
    simp only [Category.assoc, mappingCocone.inr_v_snd_v_assoc, mappingCocone.inr_v_snd_v,
      Category.comp_id]

lemma dgGluingCoconeMap_inl :
    (mappingCocone.inl μ).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap μ ν a b h)) (add_zero 0) =
    (Cochain.ofHom a).comp (mappingCocone.inl ν) (zero_add 0) := by
  apply Cochain.ext₀
  intro n
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_X_ext ν n
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_fst_f,
      mappingCocone.inl_v_fst_f_assoc, mappingCocone.inl_v_fst_f, Category.comp_id]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v]
    simp only [Category.assoc, mappingCocone.inl_v_snd_v_assoc,
      mappingCocone.inl_v_snd_v, comp_zero, zero_comp]

section Native
universe v w
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

lemma dgGluingHomRepresentableIso_inr :
    (mappingCocone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y)).val.comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom) (add_zero 1) =
    (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Y.right)).inv).comp
      (mappingCocone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R D (RightModule R C) M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y))).val (zero_add 1) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso, Iso.symm_hom]
  exact dgGluingCoconeMap_inr _ _ _ _ _

lemma dgGluingHomRepresentableIso_inl :
    (mappingCocone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom) (add_zero 0) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComponentsIso R C D M X Y).hom).comp
      (mappingCocone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R D (RightModule R C) M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y))) (zero_add 0) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso]
  exact dgGluingCoconeMap_inl _ _ _ _ _
end Native
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
