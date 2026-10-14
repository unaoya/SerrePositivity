module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleTransport
public import SerrePositivity.CategoryTheory.FunctorTransport
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleEvaluation

/-! # 各段の通常のテンソル積を持つ係数加群 -/

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

/-- 自由零生成対称列との左convolutionの係数加群の関手。 -/
def freeZeroConvolutionModuleFunctor (X : C) : Mod (SymmetricSequence C) M ⥤
    Mod (SymmetricSequence C) M :=
  ((Functor.const (Mod (SymmetricSequence C) M)).obj ((freeAt 0).obj X)).prod'
    (𝟭 _) ⋙ MonoidalBalancedTensor.tensorLeftBifunctor M

/-- 左convolutionの作用を移し、各段が通常のテンソル積となる係数加群を構成する。 -/
def pointwiseTensorModule (X : C) (A : Mod (SymmetricSequence C) M) :=
  MonoidalModuleTransport.obj M
    (MonoidalBalancedTensor.tensorLeftObj M ((freeAt 0).obj X) A)
      ((freeZeroConvolutionNatIso X).app A.X)

/-- 左convolutionの係数加群と各段の通常のテンソル積の係数加群の全体の比較。 -/
def pointwiseTensorModuleIso (X : C) (A : Mod (SymmetricSequence C) M) :
    MonoidalBalancedTensor.tensorLeftObj M ((freeAt 0).obj X) A ≅
      pointwiseTensorModule M X A :=
  MonoidalModuleTransport.iso M
    (MonoidalBalancedTensor.tensorLeftObj M ((freeAt 0).obj X) A)
      ((freeZeroConvolutionNatIso X).app A.X)

/-- 各段の通常のテンソル積の係数加群はパラメータ加群に関する関手。 -/
def pointwiseTensorModuleFunctor (X : C) : Mod (SymmetricSequence C) M ⥤
    Mod (SymmetricSequence C) M :=
  FunctorTransport.transport (freeZeroConvolutionModuleFunctor M X)
    (pointwiseTensorModule M X) (pointwiseTensorModuleIso M X)

/-- 左convolutionとの全体の比較はパラメータ加群に関する自然同型。 -/
def pointwiseTensorModuleNatIso (X : C) :
    freeZeroConvolutionModuleFunctor M X ≅ pointwiseTensorModuleFunctor M X :=
  FunctorTransport.iso (freeZeroConvolutionModuleFunctor M X)
    (pointwiseTensorModule M X) (pointwiseTensorModuleIso M X)

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
/-- 各段の対象は基礎圏の通常のテンソル積。 -/
lemma pointwiseTensorModule_level (X : C) (A : Mod (SymmetricSequence C) M) (q : ℕ) :
    level (pointwiseTensorModule M X A).X q = X ⊗ level A.X q := rfl

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
/-- 移送した関手の基礎射は通常のテンソル積の各段の射。 -/
lemma pointwiseTensorModuleFunctor_map_hom (X : C) {A B : Mod (SymmetricSequence C) M}
    (g : A ⟶ B) :
    ((pointwiseTensorModuleFunctor M X).map g).hom = (pointwiseTensorFunctor X).map g.hom := by
  change (freeZeroConvolutionNatIso X).inv.app A.X ≫
      (MonoidalBalancedTensor.tensorLeftMap M (𝟙 ((freeAt 0).obj X)) g).hom ≫
        (freeZeroConvolutionNatIso X).hom.app B.X = _
  rw [MonoidalBalancedTensor.tensorLeftMap_hom, id_tensorHom]
  have hn := (freeZeroConvolutionNatIso X).hom.naturality g.hom
  change ((freeAt 0).obj X ◁ g.hom) ≫ (freeZeroConvolutionNatIso X).hom.app B.X =
    (freeZeroConvolutionNatIso X).hom.app A.X ≫ (pointwiseTensorFunctor X).map g.hom at hn
  erw [hn, Iso.inv_hom_id_app_assoc]

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
/-- 各段の関手の射は第二因子の射との通常のテンソル積。 -/
lemma pointwiseTensorModuleFunctor_map_app (X : C) {A B : Mod (SymmetricSequence C) M}
    (g : A ⟶ B) (q : ℕ) :
    ((pointwiseTensorModuleFunctor M X).map g).hom.app (FiniteBijection.of q) =
      X ◁ g.hom.app (FiniteBijection.of q) := by
  rw [pointwiseTensorModuleFunctor_map_hom]
  rfl

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
/-- 指定した基礎射の各段が通常のテンソルの射になるという法則。 -/
def pointwiseTensorMapLevelLaw (X : C) {A B : Mod (SymmetricSequence C) M}
    (g : A ⟶ B) (h : (pointwiseTensorModule M X A).X ⟶
      (pointwiseTensorModule M X B).X) (q : ℕ) : Prop :=
  h.app (FiniteBijection.of q) = X ◁ g.hom.app (FiniteBijection.of q)

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [IsCommMonObj M] in
/-- 各段のテンソル関手の基礎射は通常のテンソルの射の法則を満たす。 -/
lemma pointwiseTensorModuleFunctor_map_levelLaw (X : C)
    {A B : Mod (SymmetricSequence C) M} (g : A ⟶ B) (q : ℕ) :
    pointwiseTensorMapLevelLaw M X g ((pointwiseTensorModuleFunctor M X).map g).hom q :=
  pointwiseTensorModuleFunctor_map_app M X g q

/-- 自由零生成加群との釣り合いテンソル積と各段の通常のテンソル積の全体の比較。 -/
def freeZeroTensorPointwiseModuleIso (X : C) (A : Mod (SymmetricSequence C) M) :
    MonoidalBalancedTensor.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) A ≅ pointwiseTensorModule M X A :=
  MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X) A ≪≫ pointwiseTensorModuleIso M X A

omit [HasEqualizers (SymmetricSequence C)] in
/-- 自由零生成加群との全体の比較はパラメータ加群の射に関して自然。 -/
@[reassoc]
lemma freeZeroTensorPointwiseModuleIso_naturality (X : C)
    {A B : Mod (SymmetricSequence C) M} (g : A ⟶ B) :
    (tensorLeft (MonoidalFreeModule.freeObj M ((freeAt 0).obj X))).map g ≫
        (freeZeroTensorPointwiseModuleIso M X B).hom =
      (freeZeroTensorPointwiseModuleIso M X A).hom ≫ (pointwiseTensorModuleFunctor M X).map g := by
  have h := MonoidalBalancedTensor.freeLeft_naturality M (𝟙 ((freeAt 0).obj X)) g
  have hi : MonoidalFreeModule.freeMap M (𝟙 ((freeAt 0).obj X)) =
      𝟙 (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) :=
    (MonoidalFreeModule.freeFunctor M).map_id _
  rw [hi] at h
  change (tensorLeft (MonoidalFreeModule.freeObj M ((freeAt 0).obj X))).map g ≫
      (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X) B).hom =
    (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X) A).hom ≫
      (freeZeroConvolutionModuleFunctor M X).map g at h
  have hn := (pointwiseTensorModuleNatIso M X).hom.naturality g
  change (freeZeroConvolutionModuleFunctor M X).map g ≫
      (pointwiseTensorModuleIso M X B).hom =
    (pointwiseTensorModuleIso M X A).hom ≫ (pointwiseTensorModuleFunctor M X).map g at hn
  change (tensorLeft (MonoidalFreeModule.freeObj M ((freeAt 0).obj X))).map g ≫
      ((MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X) B).hom ≫
        (pointwiseTensorModuleIso M X B).hom) =
    ((MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X) A).hom ≫
      (pointwiseTensorModuleIso M X A).hom) ≫ (pointwiseTensorModuleFunctor M X).map g
  erw [← Category.assoc, h, Category.assoc, hn]
  exact (Category.assoc _ _ _).symm

/-- 自由零生成加群との比較を全体の自然同型へまとめる。 -/
def freeZeroTensorPointwiseModuleNatIso (X : C) :
    tensorLeft (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) ≅
      pointwiseTensorModuleFunctor M X :=
  NatIso.ofComponents (freeZeroTensorPointwiseModuleIso M X)
    (freeZeroTensorPointwiseModuleIso_naturality M X)

omit [HasEqualizers (SymmetricSequence C)] in
/-- 全体の比較を各段に評価すると、既存の各段のテンソル比較になる。 -/
lemma freeZeroTensorPointwiseModuleIso_level (X : C) (A : Mod (SymmetricSequence C) M)
    (q : ℕ) :
    ((Mod.forget (D := SymmetricSequence C) M) ⋙ evaluation q).mapIso
        (freeZeroTensorPointwiseModuleIso M X A) = freeZeroTensorModuleLevelIso M X A q := by
  apply Iso.ext
  rfl

end SerrePositivity.SymmetricSequence
