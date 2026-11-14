module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeLeftInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeBiproductLeftInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeSplit

/-! 左右分解後の Hom 円錐比較の左包含を、第一成分と第三 cochain に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f
local notation "μ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "l" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso R C D M X Y Z f
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient R C D M X Y Z f

/-- 元の直和写像の左包含の左射影。 -/
lemma dgGluingHomConeBiproductIso_inl_fst :
    (mappingCone.inl p).comp (Cochain.ofHom ((b).hom ≫ biprod.fst))
      (add_zero (-1)) =
    (Cochain.ofHom biprod.fst).comp (mappingCone.inl l) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeDiagonalIso,
    Iso.trans_hom, Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInl_eqToIso _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso_inl_fst l r

/-- 元の直和写像の左包含の右射影。 -/
lemma dgGluingHomConeBiproductIso_inl_snd :
    (mappingCone.inl p).comp (Cochain.ofHom ((b).hom ≫ biprod.snd))
      (add_zero (-1)) =
    (Cochain.ofHom biprod.snd).comp (mappingCone.inl r) (zero_add (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeDiagonalIso,
    Iso.trans_hom, Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInl_eqToIso _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso_inl_snd l r

/-- 左右分解後の第一成分も、元の第一射影と同じ次数 −1 の左包含。 -/
lemma dgGluingHomConeSplitIso_inl_fst :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso R C D M X Y Z f).hom ≫
        mappingCocone.fst d)) (add_zero (-1)) =
    ((Cochain.ofHom (mappingCocone.fst μ)).comp (mappingCone.inl p)
      (zero_add (-1))).comp (Cochain.ofHom (b).hom) (add_zero (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso_inl_fst]

/-- 左右分解後の第三 cochain も、元の第三成分と係数左包含の合成の負。 -/
lemma dgGluingHomConeSplitIso_inl_snd :
    (mappingCone.inl k).comp
      ((Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso R C D M X Y Z f).hom).comp
        (mappingCocone.snd d) (zero_add (-1))) (by omega : -1 + -1 = -2) =
    -(mappingCocone.snd μ).comp
      (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f))
      (by omega : -1 + -1 = -2) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
  simp only [Iso.refl_hom, Cochain.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso_inl_snd R C D M X Y Z f

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
