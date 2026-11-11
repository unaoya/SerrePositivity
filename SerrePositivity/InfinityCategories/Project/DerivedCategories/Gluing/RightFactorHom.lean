module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorSubcategories
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorZeroAcyclic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconeRightProjection

/-! D 因子から任意対象への右 Hom 射影は、元の D の Hom への擬同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits Opposite HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingBimodule_acyclic_of_left_zero (c : C) (d : D)
    (hc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C c) : (M.value c d).Acyclic :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_complex_acyclic R _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_map R Cᵒᵖ (M.rightAt d) (op c)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_op R C c hc))

/-- 同じ右 Hom 射影は、ホモトピー零の左成分を持つ始域に対して擬同型。 -/
lemma dgGluingRightHomMap_quasiIso_of_source_left_zero
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (hX : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y) := by
  have ha : QuasiIso (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) :=
    (complex_quasiIso_iff_acyclic_cone R _).2
      (SerrePositivity.cochainAcyclic_mappingCone _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHom_acyclic_of_source_zero R C X.left Y.left hX)
        (dgGluingBimodule_acyclic_of_left_zero R C D M X.left Y.right hX))
  have hd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y =
      biprod.desc (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) := by
    apply biprod.hom_ext'
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inl_snd_assoc,
        biprod.inl_fst_assoc, zero_comp, biprod.inl_desc, zero_sub]
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inr_snd_assoc,
        biprod.inr_fst_assoc, zero_comp, biprod.inr_desc, sub_zero]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeRightProjection_quasiIso _ _ _ hd ha

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
