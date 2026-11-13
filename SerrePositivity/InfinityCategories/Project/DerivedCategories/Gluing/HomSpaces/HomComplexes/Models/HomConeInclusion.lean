module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeExplicit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.CoconeConeInclusion

/-! native Hom 円錐の明示比較は、右包含の二射影と同じ第三 cochain を保持する。 -/
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
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Z
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom R C D M X Y Z f
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitCoefficient R C D M X Y Z f

/-- 回収した Hom 円錐同型は、元の右包含を同じ厳密 cocone 写像に送る。 -/
lemma dgGluingHomConeIso_inr :
    mappingCone.inr k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeIso R C D M X Y Z f).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap ν (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeCoefficient R C D M X Y Z f)
      (mappingCone.inr p) (mappingCone.inr g)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_inr p g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) ν
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeHomotopy R C D M X Y Z f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRecovered_boundary R C D M X Y Z f)).symm :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso_inr _ _ _ _ _

/-- 明示係数への移送後も、第一成分は元の第一射影と cone 右包含の合成。 -/
lemma dgGluingHomConeExplicitIso_inr_fst :
    mappingCone.inr k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso R C D M X Y Z f).hom ≫
      mappingCocone.fst d = mappingCocone.fst ν ≫ mappingCone.inr p := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso, Iso.trans_hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc, ← Category.assoc,
    dgGluingHomConeIso_inr, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
  simp only [Iso.refl_hom, Category.comp_id]

/-- 明示係数への移送後の第三 cochain は、元の第三 cochain と係数 cone 右包含の合成。 -/
lemma dgGluingHomConeExplicitIso_inr_snd :
    (Cochain.ofHom (mappingCone.inr k ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso R C D M X Y Z f).hom)).comp
      (mappingCocone.snd d) (zero_add (-1)) =
    (mappingCocone.snd ν).comp
      (Cochain.ofHom (mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f)))
      (add_zero (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeExplicitIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.ofHom_comp, dgGluingHomConeIso_inr,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeActionIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr_eqToIso _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom_action R C D M X Y Z f)]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
