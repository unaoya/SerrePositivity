module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeSplit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeSquareRestriction

/-! Hom cone の直和分解の実包含と、同じ比較ホモトピーを保持する左右の係数。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "l" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f
local notation "μ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Z
local notation "h" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird R C D M X Y Z f
local notation "hh" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird_boundary R C D M X Y Z f

lemma dgGluingDifference_inl : biprod.inl ≫ μ = -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inl_snd_assoc,
    biprod.inl_fst_assoc, zero_comp, zero_sub]

lemma dgGluingDifference_inr : biprod.inr ≫ μ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub, biprod.inr_snd_assoc,
    biprod.inr_fst_assoc, zero_comp, sub_zero]

lemma dgGluingHomConeThird_inl : (Cochain.ofHom biprod.inl).comp h (zero_add (-1)) =
    -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSquareHomotopy R C D M (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f) X.left := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird, Cochain.comp_neg,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  erw [biprod.inl_fst, Cochain.id_comp]

lemma dgGluingHomConeThird_inr : (Cochain.ofHom biprod.inr).comp h (zero_add (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird, Cochain.comp_neg,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    biprod.inr_fst, Cochain.ofHom_zero, Cochain.zero_comp, neg_zero]

lemma dgGluingHomConeLeft_square : l ≫ biprod.inl = biprod.inl ≫ p := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents_eq_biprod]
  simp
lemma dgGluingHomConeRight_square : r ≫ biprod.inr = biprod.inr ≫ p := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents_eq_biprod]
  simp

def dgGluingHomConeLeftInclusion : mappingCone l ⟶ mappingCone p :=
  mappingCone.map l p biprod.inl biprod.inl (dgGluingHomConeLeft_square R C D M X Y Z f)
def dgGluingHomConeRightInclusion : mappingCone r ⟶ mappingCone p :=
  mappingCone.map r p biprod.inr biprod.inr (dgGluingHomConeRight_square R C D M X Y Z f)

lemma dgGluingHomConeLeftInclusion_diagonal :
    dgGluingHomConeLeftInclusion R C D M X Y Z f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeDiagonalIso R C D M X Y Z f).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftInclusion l r :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMap_target_transport l p (biprod.map l r) biprod.inl biprod.inl
    _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)

lemma dgGluingHomConeRightInclusion_diagonal :
    dgGluingHomConeRightInclusion R C D M X Y Z f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeDiagonalIso R C D M X Y Z f).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightInclusion l r :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMap_target_transport r p (biprod.map l r) biprod.inr biprod.inr
    _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents_eq_biprod R C D M X Y Z f)

lemma dgGluingHomConeBiproductIso_inv_left :
    biprod.inl ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso R C D M X Y Z f).inv =
      dgGluingHomConeLeftInclusion R C D M X Y Z f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso, Iso.trans_inv, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso, biprod.inl_desc]
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeDiagonalIso R C D M X Y Z f).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    dgGluingHomConeLeftInclusion_diagonal]

lemma dgGluingHomConeBiproductIso_inv_right :
    biprod.inr ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso R C D M X Y Z f).inv =
      dgGluingHomConeRightInclusion R C D M X Y Z f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso, Iso.trans_inv, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeBiproductIso, biprod.inr_desc]
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeDiagonalIso R C D M X Y Z f).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    dgGluingHomConeRightInclusion_diagonal]

/-- 左 cone への制限。比較 cochain も同じ左包含で制限する。 -/
def dgGluingHomConeLeftCoefficient : mappingCone l ⟶ mappingCone g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap l g (biprod.inl ≫ μ) (biprod.inl ≫ ν)
    ((Cochain.ofHom biprod.inl).comp h (zero_add (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareRestriction_boundary l p g biprod.inl biprod.inl
      (dgGluingHomConeLeft_square R C D M X Y Z f) μ ν h hh)

/-- 右 cone への制限。比較 cochain も同じ右包含で制限する。 -/
def dgGluingHomConeRightCoefficient : mappingCone r ⟶ mappingCone g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap r g (biprod.inr ≫ μ) (biprod.inr ≫ ν)
    ((Cochain.ofHom biprod.inr).comp h (zero_add (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareRestriction_boundary r p g biprod.inr biprod.inr
      (dgGluingHomConeRight_square R C D M X Y Z f) μ ν h hh)

lemma dgGluingHomConeSplitCoefficient_left :
    biprod.inl ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient R C D M X Y Z f =
      dgGluingHomConeLeftCoefficient R C D M X Y Z f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient, ← Category.assoc,
    dgGluingHomConeBiproductIso_inv_left]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareRestriction l p g biprod.inl biprod.inl
    (dgGluingHomConeLeft_square R C D M X Y Z f) μ ν h hh

lemma dgGluingHomConeSplitCoefficient_right :
    biprod.inr ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient R C D M X Y Z f =
      dgGluingHomConeRightCoefficient R C D M X Y Z f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient, ← Category.assoc,
    dgGluingHomConeBiproductIso_inv_right]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareRestriction r p g biprod.inr biprod.inr
    (dgGluingHomConeRight_square R C D M X Y Z f) μ ν h hh

lemma dgGluingHomConeSplitCoefficient_eq :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient R C D M X Y Z f =
      biprod.desc (dgGluingHomConeLeftCoefficient R C D M X Y Z f)
        (dgGluingHomConeRightCoefficient R C D M X Y Z f) := by
  apply biprod.hom_ext' <;>
    simp only [biprod.inl_desc, biprod.inr_desc, dgGluingHomConeSplitCoefficient_left,
      dgGluingHomConeSplitCoefficient_right]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
