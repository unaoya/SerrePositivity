module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrimitiveComparison
/-! 実 cocone の右包含と Hom の Yoneda 比較同型の厳密な整合性。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (μ : P ⟶ S) (ν : Q ⟶ T) (a : P ⟶ Q) (b : S ⟶ T) (h : μ ≫ b = a ≫ ν)
lemma dgGluingCoconeMap_inr :
    (mappingCocone.inr μ).val.comp
      (Cochain.ofHom (complexMappingCoconeMap μ ν a b h)) (add_zero 1) =
    (Cochain.ofHom b).comp (mappingCocone.inr ν).val (zero_add 1) := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  apply complexMappingCocone_X_ext ν q
  · simp only [Category.assoc, complexMappingCoconeMap_f_fst_f,
      mappingCocone.inr_v_fst_f_assoc, mappingCocone.inr_v_fst_f, comp_zero, zero_comp]
  · obtain rfl : p = q - 1 := by omega
    rw [Category.assoc, complexMappingCoconeMap_f_snd_v]
    simp only [Category.assoc, mappingCocone.inr_v_snd_v_assoc, mappingCocone.inr_v_snd_v,
      Category.comp_id]

section Native
universe v w
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)

lemma dgGluingHomRepresentableIso_inr :
    (mappingCocone.inr (dgGluingDifference R C D M X Y)).val.comp
      (Cochain.ofHom (dgGluingHomRepresentableIso R C D M X Y).hom) (add_zero 1) =
    (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Y.right)).inv).comp
      (mappingCocone.inr (dgFunctorCommaDifference R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y))).val (zero_add 1) := by
  simp only [dgGluingHomRepresentableIso, complexMappingCoconeMapIso, Iso.symm_hom]
  exact dgGluingCoconeMap_inr _ _ _ _ _
end Native
end SerrePositivity.InfinityCategories
