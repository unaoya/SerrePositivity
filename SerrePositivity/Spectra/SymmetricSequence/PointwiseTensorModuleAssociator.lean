module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolutionAssociator
public import SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor

/-! # 各段のテンソルの係数加群の結同比較 -/

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

/-- 加群を固定して左の対称列をテンソルする関手。 -/
def moduleTensorParameterFunctor (A : Mod (SymmetricSequence C) M) :
    SymmetricSequence C ⥤ Mod (SymmetricSequence C) M :=
  (𝟭 (SymmetricSequence C)).prod' ((Functor.const (SymmetricSequence C)).obj A) ⋙
    MonoidalBalancedTensor.tensorLeftBifunctor M

/-- 自由因子の結同比較を移した各段のテンソルの加群同型。 -/
def pointwiseTensorModuleAssociator (X Y : C) (A : Mod (SymmetricSequence C) M) :
    pointwiseTensorModule M (X ⊗ Y) A ≅
      pointwiseTensorModule M X (pointwiseTensorModule M Y A) :=
  (pointwiseTensorModuleIso M (X ⊗ Y) A).symm ≪≫
    (moduleTensorParameterFunctor M A).mapIso (freePairConvolutionIso 0 0 X Y).symm ≪≫
      MonoidalBalancedTensor.freeLeftPairAssociator M ((freeAt 0).obj X)
        ((freeAt 0).obj Y) A ≪≫
          (freeZeroConvolutionModuleFunctor M X).mapIso (pointwiseTensorModuleIso M Y A) ≪≫
            pointwiseTensorModuleIso M X (pointwiseTensorModule M Y A)

omit [HasEqualizers (SymmetricSequence C)] in
/-- 移した結同比較の基礎射は自由零生成のconvolutionの結同比較。 -/
lemma pointwiseTensorModuleAssociator_hom (X Y : C) (A : Mod (SymmetricSequence C) M) :
    (pointwiseTensorModuleAssociator M X Y A).hom.hom =
      (freeZeroConvolutionAssociatorIso X Y A.X).hom := by
  unfold pointwiseTensorModuleAssociator
  simp only [Iso.trans_hom, Mod.comp_hom']
  change (freeZeroConvolutionNatIso (X ⊗ Y)).inv.app A.X ≫
    (MonoidalBalancedTensor.tensorLeftMap M (freePairConvolutionIso 0 0 X Y).inv
      (𝟙 A)).hom ≫
      (MonoidalBalancedTensor.freeLeftPairAssociator M ((freeAt 0).obj X)
        ((freeAt 0).obj Y) A).hom.hom ≫
        (MonoidalBalancedTensor.tensorLeftMap M (𝟙 ((freeAt 0).obj X))
          (pointwiseTensorModuleIso M Y A).hom).hom ≫
          (freeZeroConvolutionNatIso X).hom.app (pointwiseTensorModule M Y A).X = _
  rw [MonoidalBalancedTensor.tensorLeftMap_hom, Mod.id_hom', tensorHom_id,
    MonoidalBalancedTensor.freeLeftPairAssociator_hom,
    MonoidalBalancedTensor.tensorLeftMap_hom, id_tensorHom]
  rfl

omit [HasEqualizers (SymmetricSequence C)] in
/-- 加群の結同比較の各段は基礎圏の通常の結合子。 -/
lemma pointwiseTensorModuleAssociator_level (X Y : C) (A : Mod (SymmetricSequence C) M)
    (q : ℕ) :
    (pointwiseTensorModuleAssociator M X Y A).hom.hom.app (FiniteBijection.of q) =
      (α_ X Y (level A.X q)).hom := by
  rw [pointwiseTensorModuleAssociator_hom]
  exact freeZeroConvolutionAssociatorIso_level X Y A.X q

omit [HasEqualizers (SymmetricSequence C)] in
/-- 加群の逆結同比較の各段も通常の逆結合子。 -/
lemma pointwiseTensorModuleAssociator_inv_level (X Y : C)
    (A : Mod (SymmetricSequence C) M) (q : ℕ) :
    (pointwiseTensorModuleAssociator M X Y A).inv.hom.app (FiniteBijection.of q) =
      (α_ X Y (level A.X q)).inv := by
  apply (cancel_mono (α_ X Y (level A.X q)).hom).mp
  calc
    _ = (pointwiseTensorModuleAssociator M X Y A).inv.hom.app (FiniteBijection.of q) ≫
        (pointwiseTensorModuleAssociator M X Y A).hom.hom.app (FiniteBijection.of q) := by
      rw [pointwiseTensorModuleAssociator_level]
    _ = ((pointwiseTensorModuleAssociator M X Y A).inv ≫
      (pointwiseTensorModuleAssociator M X Y A).hom).hom.app (FiniteBijection.of q) := rfl
    _ = 𝟙 _ := by rw [Iso.inv_hom_id]; rfl
    _ = _ := (α_ X Y (level A.X q)).inv_hom_id.symm

omit [HasEqualizers (SymmetricSequence C)] in
/-- 自由加群の積の比較から移送した結同比較は構成済みの加群の結同比較に一致する。 -/
lemma pointwiseTensorModuleAssociator_free_hom (X Y : C)
    (A : Mod (SymmetricSequence C) M) :
    (freeZeroTensorPointwiseModuleIso M (X ⊗ Y) A).inv ≫
      (MonoidalBalancedTensor.freePairIso M ((freeAt 0).obj X) ((freeAt 0).obj Y) ≪≫
        (MonoidalFreeModule.freeFunctor M).mapIso (freePairConvolutionIso 0 0 X Y)).inv ▷ A ≫
      (α_ (MonoidalFreeModule.freeObj M ((freeAt 0).obj X))
        (MonoidalFreeModule.freeObj M ((freeAt 0).obj Y)) A).hom ≫
      MonoidalFreeModule.freeObj M ((freeAt 0).obj X) ◁
        (freeZeroTensorPointwiseModuleIso M Y A).hom ≫
      (freeZeroTensorPointwiseModuleIso M X (pointwiseTensorModule M Y A)).hom =
        (pointwiseTensorModuleAssociator M X Y A).hom := by
  unfold freeZeroTensorPointwiseModuleIso
  simp only [Iso.trans_inv, Iso.trans_hom, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc]
  have ht := MonoidalBalancedTensor.freeLeftPairAssociator_transport M
    (freePairConvolutionIso 0 0 X Y).inv A (pointwiseTensorModule M Y A)
      (pointwiseTensorModuleIso M Y A).hom
  change (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj (X ⊗ Y)) A).inv ≫
    (MonoidalFreeModule.freeFunctor M).map (freePairConvolutionIso 0 0 X Y).inv ▷ A ≫
    (MonoidalBalancedTensor.freePairIso M ((freeAt 0).obj X) ((freeAt 0).obj Y)).inv ▷ A ≫
    (α_ (MonoidalFreeModule.freeObj M ((freeAt 0).obj X))
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj Y)) A).hom ≫
    MonoidalFreeModule.freeObj M ((freeAt 0).obj X) ◁
      ((MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj Y) A).hom ≫
        (pointwiseTensorModuleIso M Y A).hom) ≫
    (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X)
      (pointwiseTensorModule M Y A)).hom = _ at ht
  simp only [whiskerLeft_comp, Category.assoc] at ht
  erw [reassoc_of% ht]
  unfold pointwiseTensorModuleAssociator
  simp only [Iso.trans_hom]
  rfl

end SerrePositivity.SymmetricSequence
