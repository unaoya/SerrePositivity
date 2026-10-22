module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeExplicit
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeConeInclusion

/-! native Hom 円錐の明示比較は、右包含の二射影と同じ第三 cochain を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "k" => dgGluingPostcomposition R C D M X Y Z f
local notation "ν" => dgGluingDifference R C D M X Z
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "g" => dgGluingHomConeBottom R C D M X Y Z f
local notation "d" => dgGluingHomConeExplicitCoefficient R C D M X Y Z f

/-- 回収した Hom 円錐同型は、元の右包含を同じ厳密 cocone 写像に送る。 -/
lemma dgGluingHomConeIso_inr :
    mappingCone.inr k ≫ (dgGluingHomConeIso R C D M X Y Z f).hom =
    complexMappingCoconeMap ν (dgGluingHomConeCoefficient R C D M X Y Z f)
      (mappingCone.inr p) (mappingCone.inr g)
      (dgGluingConeSquareMap_inr p g (dgGluingDifference R C D M X Y) ν
        (dgGluingHomConeHomotopy R C D M X Y Z f)
        (dgGluingHomConeRecovered_boundary R C D M X Y Z f)).symm :=
  dgGluingCoconeExtractConeIso_inr _ _ _ _ _

/-- 明示係数への移送後も、第一成分は元の第一射影と cone 右包含の合成。 -/
lemma dgGluingHomConeExplicitIso_inr_fst :
    mappingCone.inr k ≫ (dgGluingHomConeExplicitIso R C D M X Y Z f).hom ≫
      mappingCocone.fst d = mappingCocone.fst ν ≫ mappingCone.inr p := by
  simp only [dgGluingHomConeExplicitIso, Iso.trans_hom,
    complexMappingCoconeMapIso, Category.assoc]
  rw [complexMappingCoconeMap_fst, ← Category.assoc, ← Category.assoc,
    dgGluingHomConeIso_inr, complexMappingCoconeMap_fst]
  simp only [Iso.refl_hom, Category.comp_id]

/-- 明示係数への移送後の第三 cochain は、元の第三 cochain と係数 cone 右包含の合成。 -/
lemma dgGluingHomConeExplicitIso_inr_snd :
    (Cochain.ofHom (mappingCone.inr k ≫
      (dgGluingHomConeExplicitIso R C D M X Y Z f).hom)).comp
      (mappingCocone.snd d) (zero_add (-1)) =
    (mappingCocone.snd ν).comp
      (Cochain.ofHom (mappingCone.inr (dgGluingHomConeAction R C D M X Y Z f)))
      (add_zero (-1)) := by
  simp only [dgGluingHomConeExplicitIso, Iso.trans_hom, complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.ofHom_comp, dgGluingHomConeIso_inr,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, complexMappingCoconeMap_snd,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rw [dgGluingHomConeActionIso, dgGluingConeInr_eqToIso _ _
    (dgGluingHomConeBottom_action R C D M X Y Z f)]
  rfl

end SerrePositivity.InfinityCategories
