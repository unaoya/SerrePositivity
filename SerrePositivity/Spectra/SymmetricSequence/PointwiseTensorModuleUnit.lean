module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleUnit
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeUnit

/-! # 各段のテンソルの係数加群の単位同型と各段の比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]

/-- 各段のテンソルの係数加群の単位自然同型。 -/
def pointwiseTensorModuleUnitNatIso :
    pointwiseTensorModuleFunctor M (𝟙_ C) ≅ 𝟭 (Mod (SymmetricSequence C) M) :=
  (freeZeroTensorPointwiseModuleNatIso M (𝟙_ C)).symm ≪≫
    (curriedTensor (Mod (SymmetricSequence C) M)).mapIso (freeZeroModuleUnitIso M) ≪≫
      leftUnitorNatIso (Mod (SymmetricSequence C) M)

omit [HasEqualizers (SymmetricSequence C)] in
/-- 単位比較の基礎射はconvolutionの逆比較と基礎対称列の単位比較の合成。 -/
lemma pointwiseTensorModuleUnitNatIso_hom (A : Mod (SymmetricSequence C) M) :
    ((pointwiseTensorModuleUnitNatIso M).hom.app A).hom =
      (freeZeroConvolutionNatIso (𝟙_ C)).inv.app A.X ≫
        (freeZeroUnitIso (C := C)).hom ▷ A.X ≫ (λ_ A.X).hom := by
  change ((freeZeroConvolutionNatIso (𝟙_ C)).inv.app A.X ≫
    (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj (𝟙_ C)) A).inv.hom) ≫
      ((freeZeroModuleUnitIso M).hom ⊗ₘ 𝟙 A).hom ≫ (λ_ A).hom.hom = _
  rw [tensorHom_id]
  simp only [Category.assoc]
  change (freeZeroConvolutionNatIso (𝟙_ C)).inv.app A.X ≫
    ((MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj (𝟙_ C)) A).inv.hom ≫
      (((freeZeroModuleUnitIso M).hom ▷ A) ≫ (λ_ A).hom).hom) = _
  erw [MonoidalBalancedTensor.freeLeft_unit_comparison]

omit [HasEqualizers (SymmetricSequence C)] in
/-- 単位自然比較の各段は通常の左単位子。 -/
lemma pointwiseTensorModuleUnitNatIso_level (A : Mod (SymmetricSequence C) M) (q : ℕ) :
    ((pointwiseTensorModuleUnitNatIso M).hom.app A).hom.app (FiniteBijection.of q) =
      (λ_ (level A.X q)).hom := by
  rw [pointwiseTensorModuleUnitNatIso_hom]
  change (freeZeroConvolutionLevelIso (𝟙_ C) A.X q).inv ≫
    (((freeZeroUnitIso (C := C)).hom ▷ A.X) ≫ (λ_ A.X).hom).app (FiniteBijection.of q) = _
  rw [← freeZeroConvolutionGenerator_eq_inv]
  unfold freeZeroConvolutionGenerator
  simp only [Category.assoc]
  erw [NatTrans.naturality, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [convolutionUnit_whiskerRight_assoc]
  erw [← comp_whiskerRight_assoc, freeZeroUnitIso_generator_hom]
  have hl := convolution_leftUnitor_generator A.X (FiniteBijection.of q)
  erw [reassoc_of% hl]
  erw [← CategoryTheory.Functor.map_comp, ← indexLeftUnitor_eq, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- 単位自然比較の各段が通常の左単位子になるという法則。 -/
def pointwiseTensorModuleUnitLevelLaw (A : Mod (SymmetricSequence C) M) (q : ℕ) : Prop :=
  ((pointwiseTensorModuleUnitNatIso M).hom.app A).hom.app (FiniteBijection.of q) =
    (λ_ (level A.X q)).hom

omit [HasEqualizers (SymmetricSequence C)] in
/-- 係数加群の単位比較は各段の通常の左単位子の法則を満たす。 -/
lemma pointwiseTensorModuleUnit_levelLaw (A : Mod (SymmetricSequence C) M) (q : ℕ) :
    pointwiseTensorModuleUnitLevelLaw M A q := pointwiseTensorModuleUnitNatIso_level M A q

end SerrePositivity.SymmetricSequence
