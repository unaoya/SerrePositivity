module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeExplicit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.CoconeConeLeftInclusion

/-! 明示した native Hom 円錐比較の左包含と、その第三 cochain の符号。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f
local notation "μ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom R C D M X Y Z f
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitCoefficient R C D M X Y Z f

/-- 係数を明示した後も、左包含の第一成分は元の第一射影の左包含。 -/
lemma dgGluingHomConeExplicitIso_inl_fst :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso R C D M X Y Z f).hom ≫
        mappingCocone.fst d)) (add_zero (-1)) =
    (Cochain.ofHom (mappingCocone.fst μ)).comp (mappingCone.inl p) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso, Iso.trans_hom, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
  simp only [Iso.refl_hom, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso_inl_fst _ _ _ _ _

/-- 左包含の第三 cochain は、元の第三 cochain と係数左包含の合成の負。 -/
lemma dgGluingHomConeExplicitIso_inl_snd :
    (mappingCone.inl k).comp
      ((Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso R C D M X Y Z f).hom).comp
        (mappingCocone.snd d) (zero_add (-1))) (by omega : -1 + -1 = -2) =
    -(mappingCocone.snd μ).comp
      (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f))
      (by omega : -1 + -1 = -2) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso_inl_snd μ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Z) p k
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_fst R C D M X Y Z f)]
  rw [Cochain.neg_comp, Cochain.comp_assoc_of_third_is_zero_cochain]
  change -(mappingCocone.snd μ).comp
    ((mappingCone.inl g).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeActionIso R C D M X Y Z f).hom) (add_zero (-1)))
    (by omega : -1 + -1 = -2) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeActionIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInl_eqToIso _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom_action R C D M X Y Z f)]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
