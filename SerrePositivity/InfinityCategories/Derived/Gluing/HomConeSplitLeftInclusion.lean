module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeLeftInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeBiproductLeftInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeSplit

/-! 左右分解後の Hom 円錐比較の左包含を、第一成分と第三 cochain に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "k" => dgGluingPostcomposition R C D M X Y Z f
local notation "μ" => dgGluingDifference R C D M X Y
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "l" => dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => dgGluingHomConeRightArrow R C D M X Y Z f
local notation "b" => dgGluingHomConeBiproductIso R C D M X Y Z f
local notation "d" => dgGluingHomConeSplitCoefficient R C D M X Y Z f

/-- 元の直和写像の左包含の左射影。 -/
lemma dgGluingHomConeBiproductIso_inl_fst :
    (mappingCone.inl p).comp (Cochain.ofHom ((b).hom ≫ biprod.fst))
      (add_zero (-1)) =
    (Cochain.ofHom biprod.fst).comp (mappingCone.inl l) (zero_add (-1)) := by
  simp only [dgGluingHomConeBiproductIso, dgGluingHomConeDiagonalIso,
    Iso.trans_hom, Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [dgGluingConeInl_eqToIso _ _
    (dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)]
  exact dgGluingConeBiproductIso_inl_fst l r

/-- 元の直和写像の左包含の右射影。 -/
lemma dgGluingHomConeBiproductIso_inl_snd :
    (mappingCone.inl p).comp (Cochain.ofHom ((b).hom ≫ biprod.snd))
      (add_zero (-1)) =
    (Cochain.ofHom biprod.snd).comp (mappingCone.inl r) (zero_add (-1)) := by
  simp only [dgGluingHomConeBiproductIso, dgGluingHomConeDiagonalIso,
    Iso.trans_hom, Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [dgGluingConeInl_eqToIso _ _
    (dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)]
  exact dgGluingConeBiproductIso_inl_snd l r

/-- 左右分解後の第一成分も、元の第一射影と同じ次数 −1 の左包含。 -/
lemma dgGluingHomConeSplitIso_inl_fst :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((dgGluingHomConeSplitIso R C D M X Y Z f).hom ≫
        mappingCocone.fst d)) (add_zero (-1)) =
    ((Cochain.ofHom (mappingCocone.fst μ)).comp (mappingCone.inl p)
      (zero_add (-1))).comp (Cochain.ofHom (b).hom) (add_zero (-1)) := by
  simp only [dgGluingHomConeSplitIso, Iso.trans_hom, complexMappingCoconeMapIso,
    Category.assoc]
  rw [complexMappingCoconeMap_fst, ← Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, dgGluingHomConeExplicitIso_inl_fst]

/-- 左右分解後の第三 cochain も、元の第三成分と係数左包含の合成の負。 -/
lemma dgGluingHomConeSplitIso_inl_snd :
    (mappingCone.inl k).comp
      ((Cochain.ofHom (dgGluingHomConeSplitIso R C D M X Y Z f).hom).comp
        (mappingCocone.snd d) (zero_add (-1))) (by omega : -1 + -1 = -2) =
    -(mappingCocone.snd μ).comp
      (mappingCone.inl (dgGluingHomConeAction R C D M X Y Z f))
      (by omega : -1 + -1 = -2) := by
  simp only [dgGluingHomConeSplitIso, Iso.trans_hom, complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [complexMappingCoconeMap_snd]
  simp only [Iso.refl_hom, Cochain.comp_id]
  exact dgGluingHomConeExplicitIso_inl_snd R C D M X Y Z f

end SerrePositivity.InfinityCategories
