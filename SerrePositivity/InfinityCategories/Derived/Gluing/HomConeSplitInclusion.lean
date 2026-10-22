module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeModuleInclusions

/-! 左右分解後の Hom 円錐比較も、元の右包含の二成分と第三 cochain を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "k" => dgGluingPostcomposition R C D M X Y Z f
local notation "ν" => dgGluingDifference R C D M X Z
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "l" => dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => dgGluingHomConeRightArrow R C D M X Y Z f
local notation "d" => dgGluingHomConeSplitCoefficient R C D M X Y Z f

omit [Small.{u} D] in
/-- 左右の cone の直和同型は、元の直和の右包含を二つの右包含へ送る。 -/
lemma dgGluingHomConeBiproductIso_inr :
    mappingCone.inr p ≫ (dgGluingHomConeBiproductIso R C D M X Y Z f).hom =
      biprod.map (mappingCone.inr l) (mappingCone.inr r) := by
  simp only [dgGluingHomConeBiproductIso, dgGluingHomConeDiagonalIso, Iso.trans_hom]
  rw [← Category.assoc, dgGluingConeInr_eqToIso _ _
    (dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)]
  apply biprod.hom_ext
  · simp only [dgGluingConeBiproductIso, Category.assoc, biprod.lift_fst]
    rw [dgGluingConeLeftProjection, mappingCone.map, mappingCone.inr_desc]
    exact (biprod.map_fst _ _).symm
  · simp only [dgGluingConeBiproductIso, Category.assoc, biprod.lift_snd]
    rw [dgGluingConeRightProjection, mappingCone.map, mappingCone.inr_desc]
    exact (biprod.map_snd _ _).symm

omit [Small.{u} D] in
/-- 左右分解後の第一成分は、元の第一射影に二つの cone 右包含を続けたもの。 -/
lemma dgGluingHomConeSplitIso_inr_fst :
    mappingCone.inr k ≫ (dgGluingHomConeSplitIso R C D M X Y Z f).hom ≫
      mappingCocone.fst d =
    mappingCocone.fst ν ≫ biprod.map (mappingCone.inr l) (mappingCone.inr r) := by
  simp only [dgGluingHomConeSplitIso, Iso.trans_hom, complexMappingCoconeMapIso,
    Category.assoc]
  rw [complexMappingCoconeMap_fst, ← Category.assoc, ← Category.assoc,
    Category.assoc (mappingCone.inr k),
    dgGluingHomConeExplicitIso_inr_fst, Category.assoc, dgGluingHomConeBiproductIso_inr]

omit [Small.{u} D] in
/-- 左右分解後も第三 cochain は、元の第三 cochain と係数の右包含の合成。 -/
lemma dgGluingHomConeSplitIso_inr_snd :
    (Cochain.ofHom (mappingCone.inr k ≫
      (dgGluingHomConeSplitIso R C D M X Y Z f).hom)).comp
      (mappingCocone.snd d) (zero_add (-1)) =
    (mappingCocone.snd ν).comp
      (Cochain.ofHom (mappingCone.inr (dgGluingHomConeAction R C D M X Y Z f)))
      (add_zero (-1)) := by
  simp only [dgGluingHomConeSplitIso, Iso.trans_hom, complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [complexMappingCoconeMap_snd]
  simp only [Iso.refl_hom, Cochain.comp_id]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    dgGluingHomConeExplicitIso_inr_snd]

end SerrePositivity.InfinityCategories
