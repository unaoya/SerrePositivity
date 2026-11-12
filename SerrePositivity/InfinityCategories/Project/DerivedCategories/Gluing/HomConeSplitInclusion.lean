module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeModuleInclusions

/-! 左右分解後の Hom 円錐比較も、元の右包含の二成分と第三 cochain を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Z
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "l" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient R C D M X Y Z f

omit [Small.{u} D] in
/-- 左右の cone の直和同型は、元の直和の右包含を二つの右包含へ送る。 -/
lemma dgGluingHomConeBiproductIso_inr :
    mappingCone.inr p ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso R C D M X Y Z f).hom =
      biprod.map (mappingCone.inr l) (mappingCone.inr r) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeDiagonalIso, Iso.trans_hom]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr_eqToIso _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)]
  apply biprod.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso, Category.assoc, biprod.lift_fst]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftProjection, mappingCone.map, mappingCone.inr_desc]
    exact (biprod.map_fst _ _).symm
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso, Category.assoc, biprod.lift_snd]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightProjection, mappingCone.map, mappingCone.inr_desc]
    exact (biprod.map_snd _ _).symm

omit [Small.{u} D] in
/-- 左右分解後の第一成分は、元の第一射影に二つの cone 右包含を続けたもの。 -/
lemma dgGluingHomConeSplitIso_inr_fst :
    mappingCone.inr k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso R C D M X Y Z f).hom ≫
      mappingCocone.fst d =
    mappingCocone.fst ν ≫ biprod.map (mappingCone.inr l) (mappingCone.inr r) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc, ← Category.assoc,
    Category.assoc (mappingCone.inr k),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso_inr_fst, Category.assoc, dgGluingHomConeBiproductIso_inr]

omit [Small.{u} D] in
/-- 左右分解後も第三 cochain は、元の第三 cochain と係数の右包含の合成。 -/
lemma dgGluingHomConeSplitIso_inr_snd :
    (Cochain.ofHom (mappingCone.inr k ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso R C D M X Y Z f).hom)).comp
      (mappingCocone.snd d) (zero_add (-1)) =
    (mappingCocone.snd ν).comp
      (Cochain.ofHom (mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f)))
      (add_zero (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
  simp only [Iso.refl_hom, Cochain.comp_id]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso_inr_snd]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
