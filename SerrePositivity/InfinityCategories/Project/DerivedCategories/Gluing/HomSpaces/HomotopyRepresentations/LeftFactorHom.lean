module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FactorSubcategories
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FactorZeroAcyclic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ComplexMappingCoconeBiprodQuasiIso

/-! C 因子への左 Hom 射影の擬同型性と、順序 ⟨D,C⟩ の全 Hom 半直交性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- C 因子への任意 gluing 対象からの Hom は、同じ左 Hom 射影で元の C の Hom と擬同型。 -/
lemma dgGluingLeftHomMap_quasiIso_of_target_right_zero
    (hY : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D Y.right) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y) := by
  have hb : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) :=
    (complex_quasiIso_iff_acyclic_cone R _).2
      (SerrePositivity.cochainAcyclic_mappingCone _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHom_acyclic_of_target_zero R D X.right Y.right hY)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBimodule_acyclic_of_right_zero R C D M X.left Y.right hY))
  have hd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y =
      biprod.desc (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) := by
    apply biprod.hom_ext'
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inl_snd_assoc,
        biprod.inl_fst_assoc, zero_comp, biprod.inl_desc, zero_sub]
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inr_snd_assoc,
        biprod.inr_fst_assoc, zero_comp, biprod.inr_desc, sub_zero]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeProjection_quasiIso_of_eq _ _ _ hd hb

/-- D 因子から C 因子への実 Hom 複体は、全整数次数で acyclic。 -/
lemma dgGluingHom_acyclic_D_to_C
    (hX : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left) (hY : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D Y.right) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y).Acyclic := by
  have := dgGluingLeftHomMap_quasiIso_of_target_right_zero R C D M X Y hY
  intro n
  exact (exactAt_iff_of_quasiIsoAt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y) n).2
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHom_acyclic_of_source_zero R C X.left Y.left hX n)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
