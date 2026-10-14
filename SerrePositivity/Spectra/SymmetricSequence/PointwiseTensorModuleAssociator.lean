module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolutionAssociator
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeAssociator

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

end SerrePositivity.SymmetricSequence
