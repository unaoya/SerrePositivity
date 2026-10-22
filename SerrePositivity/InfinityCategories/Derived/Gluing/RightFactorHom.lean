module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorSubcategories
public import SerrePositivity.InfinityCategories.Derived.Gluing.FactorZeroAcyclic
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeRightProjection

/-! D 因子から任意対象への右 Hom 射影は、元の D の Hom への擬同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingBimodule_acyclic_of_left_zero (c : C) (d : D)
    (hc : dgGluingFactorIsZero R C c) : (M.value c d).Acyclic :=
  dgGluingFactorIsZero_complex_acyclic R _
    (dgGluingFactorIsZero_map R Cᵒᵖ (M.rightAt d) (op c)
      (dgGluingFactorIsZero_op R C c hc))

/-- 同じ右 Hom 射影は、ホモトピー零の左成分を持つ始域に対して擬同型。 -/
lemma dgGluingRightHomMap_quasiIso_of_source_left_zero
    (X Y : DGGluingObject R C D M) (hX : dgGluingFactorIsZero R C X.left) :
    QuasiIso (dgGluingRightHomMap R C D M X Y) := by
  have ha : QuasiIso (-dgGluingLeftAction R C D M X Y) :=
    (complex_quasiIso_iff_acyclic_cone R _).2
      (SerrePositivity.cochainAcyclic_mappingCone _
        (dgGluingHom_acyclic_of_source_zero R C X.left Y.left hX)
        (dgGluingBimodule_acyclic_of_left_zero R C D M X.left Y.right hX))
  have hd : dgGluingDifference R C D M X Y =
      biprod.desc (-dgGluingLeftAction R C D M X Y) (dgGluingRightAction R C D M X Y) := by
    apply biprod.hom_ext'
    · simp only [dgGluingDifference, Preadditive.comp_sub, biprod.inl_snd_assoc,
        biprod.inl_fst_assoc, zero_comp, biprod.inl_desc, zero_sub]
    · simp only [dgGluingDifference, Preadditive.comp_sub, biprod.inr_snd_assoc,
        biprod.inr_fst_assoc, zero_comp, biprod.inr_desc, sub_zero]
  exact dgGluingCoconeRightProjection_quasiIso _ _ _ hd ha

end SerrePositivity.InfinityCategories
