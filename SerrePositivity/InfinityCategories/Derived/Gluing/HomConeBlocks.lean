module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeSplit
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeSquareRestriction

/-! Hom cone の直和分解の実包含と、同じ比較ホモトピーを保持する左右の係数。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "l" => dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => dgGluingHomConeRightArrow R C D M X Y Z f
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "g" => dgGluingHomConeAction R C D M X Y Z f
local notation "μ" => dgGluingDifference R C D M X Y
local notation "ν" => dgGluingDifference R C D M X Z
local notation "h" => dgGluingHomConeThird R C D M X Y Z f
local notation "hh" => dgGluingHomConeThird_boundary R C D M X Y Z f

lemma dgGluingDifference_inl : biprod.inl ≫ μ = -dgGluingLeftAction R C D M X Y := by
  simp only [dgGluingDifference, Preadditive.comp_sub, biprod.inl_snd_assoc,
    biprod.inl_fst_assoc, zero_comp, zero_sub]

lemma dgGluingDifference_inr : biprod.inr ≫ μ = dgGluingRightAction R C D M X Y := by
  simp only [dgGluingDifference, Preadditive.comp_sub, biprod.inr_snd_assoc,
    biprod.inr_fst_assoc, zero_comp, sub_zero]

lemma dgGluingHomConeThird_inl : (Cochain.ofHom biprod.inl).comp h (zero_add (-1)) =
    -dgGluingCommaClosedSquareHomotopy R C D M (dgGluingCommaObject R C D M Y)
      (dgGluingCommaObject R C D M Z) ((dgGluingToComma R C D M).onClosed.map f) X.left := by
  rw [dgGluingHomConeThird, Cochain.comp_neg,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  erw [biprod.inl_fst, Cochain.id_comp]

lemma dgGluingHomConeThird_inr : (Cochain.ofHom biprod.inr).comp h (zero_add (-1)) = 0 := by
  rw [dgGluingHomConeThird, Cochain.comp_neg,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    biprod.inr_fst, Cochain.ofHom_zero, Cochain.zero_comp, neg_zero]

lemma dgGluingHomConeLeft_square : l ≫ biprod.inl = biprod.inl ≫ p := by
  rw [dgGluingPostcompositionComponents_eq_biprod]
  simp
lemma dgGluingHomConeRight_square : r ≫ biprod.inr = biprod.inr ≫ p := by
  rw [dgGluingPostcompositionComponents_eq_biprod]
  simp

def dgGluingHomConeLeftInclusion : mappingCone l ⟶ mappingCone p :=
  mappingCone.map l p biprod.inl biprod.inl (dgGluingHomConeLeft_square R C D M X Y Z f)
def dgGluingHomConeRightInclusion : mappingCone r ⟶ mappingCone p :=
  mappingCone.map r p biprod.inr biprod.inr (dgGluingHomConeRight_square R C D M X Y Z f)

lemma dgGluingHomConeLeftInclusion_diagonal :
    dgGluingHomConeLeftInclusion R C D M X Y Z f ≫
      (dgGluingHomConeDiagonalIso R C D M X Y Z f).hom = dgGluingConeLeftInclusion l r :=
  dgGluingConeMap_target_transport l p (biprod.map l r) biprod.inl biprod.inl
    _ _ (dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)

lemma dgGluingHomConeRightInclusion_diagonal :
    dgGluingHomConeRightInclusion R C D M X Y Z f ≫
      (dgGluingHomConeDiagonalIso R C D M X Y Z f).hom = dgGluingConeRightInclusion l r :=
  dgGluingConeMap_target_transport r p (biprod.map l r) biprod.inr biprod.inr
    _ _ (dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)

lemma dgGluingHomConeBiproductIso_inv_left :
    biprod.inl ≫ (dgGluingHomConeBiproductIso R C D M X Y Z f).inv =
      dgGluingHomConeLeftInclusion R C D M X Y Z f := by
  simp only [dgGluingHomConeBiproductIso, Iso.trans_inv, ← Category.assoc,
    dgGluingConeBiproductIso, biprod.inl_desc]
  apply (cancel_mono (dgGluingHomConeDiagonalIso R C D M X Y Z f).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    dgGluingHomConeLeftInclusion_diagonal]

lemma dgGluingHomConeBiproductIso_inv_right :
    biprod.inr ≫ (dgGluingHomConeBiproductIso R C D M X Y Z f).inv =
      dgGluingHomConeRightInclusion R C D M X Y Z f := by
  simp only [dgGluingHomConeBiproductIso, Iso.trans_inv, ← Category.assoc,
    dgGluingConeBiproductIso, biprod.inr_desc]
  apply (cancel_mono (dgGluingHomConeDiagonalIso R C D M X Y Z f).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    dgGluingHomConeRightInclusion_diagonal]

/-- 左 cone への制限。比較 cochain も同じ左包含で制限する。 -/
def dgGluingHomConeLeftCoefficient : mappingCone l ⟶ mappingCone g :=
  dgGluingConeSquareMap l g (biprod.inl ≫ μ) (biprod.inl ≫ ν)
    ((Cochain.ofHom biprod.inl).comp h (zero_add (-1)))
    (dgGluingConeSquareRestriction_boundary l p g biprod.inl biprod.inl
      (dgGluingHomConeLeft_square R C D M X Y Z f) μ ν h hh)

/-- 右 cone への制限。比較 cochain も同じ右包含で制限する。 -/
def dgGluingHomConeRightCoefficient : mappingCone r ⟶ mappingCone g :=
  dgGluingConeSquareMap r g (biprod.inr ≫ μ) (biprod.inr ≫ ν)
    ((Cochain.ofHom biprod.inr).comp h (zero_add (-1)))
    (dgGluingConeSquareRestriction_boundary r p g biprod.inr biprod.inr
      (dgGluingHomConeRight_square R C D M X Y Z f) μ ν h hh)

lemma dgGluingHomConeSplitCoefficient_left :
    biprod.inl ≫ dgGluingHomConeSplitCoefficient R C D M X Y Z f =
      dgGluingHomConeLeftCoefficient R C D M X Y Z f := by
  rw [dgGluingHomConeSplitCoefficient, ← Category.assoc,
    dgGluingHomConeBiproductIso_inv_left]
  exact dgGluingConeSquareRestriction l p g biprod.inl biprod.inl
    (dgGluingHomConeLeft_square R C D M X Y Z f) μ ν h hh

lemma dgGluingHomConeSplitCoefficient_right :
    biprod.inr ≫ dgGluingHomConeSplitCoefficient R C D M X Y Z f =
      dgGluingHomConeRightCoefficient R C D M X Y Z f := by
  rw [dgGluingHomConeSplitCoefficient, ← Category.assoc,
    dgGluingHomConeBiproductIso_inv_right]
  exact dgGluingConeSquareRestriction r p g biprod.inr biprod.inr
    (dgGluingHomConeRight_square R C D M X Y Z f) μ ν h hh

lemma dgGluingHomConeSplitCoefficient_eq :
    dgGluingHomConeSplitCoefficient R C D M X Y Z f =
      biprod.desc (dgGluingHomConeLeftCoefficient R C D M X Y Z f)
        (dgGluingHomConeRightCoefficient R C D M X Y Z f) := by
  apply biprod.hom_ext' <;>
    simp only [biprod.inl_desc, biprod.inr_desc, dgGluingHomConeSplitCoefficient_left,
      dgGluingHomConeSplitCoefficient_right]

end SerrePositivity.InfinityCategories
