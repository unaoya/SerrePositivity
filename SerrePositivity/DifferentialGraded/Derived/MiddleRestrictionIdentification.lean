module
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction

/-! # 直接の中間制限と既存の積dg圏表示によるbimodule制限の同定

## 概要
直接の中間制限と既存の積dg圏表示によるbimodule制限の同定。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory BimoduleTensorModule
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

/-- 直接の左制限は既存の積dg圏表示による制限と自然同型。 -/
def middleLeftRestrictionIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B C D F ≅
      bimoduleRestriction A B D B C (DGFunctor.id B) F :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
      (rightModuleCounitIso A B D).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (middleLeftPresentationIso A B C D F)
      (rightModuleBimoduleEquivalence A B D).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (rightModuleInverseIso A B C)
      (moduleRestriction A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        ((DGFunctor.id Bᵒᵖ).tensor F).op.op ⋙ (rightModuleBimoduleEquivalence A B D).functor)

variable (E : Type t) [DGCategory A E] [Small.{u} E]

/-- 直接の右制限は既存の積dg圏表示による制限と自然同型。 -/
def middleRightRestrictionIso :
    BimoduleCategory.middleRightRestrictionFunctor A C D E F ≅
      bimoduleRestriction A D E C E F (DGFunctor.id E) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A C D E F)
      (rightModuleCounitIso A D E).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (middleRightPresentationIso A C D F E)
      (rightModuleBimoduleEquivalence A D E).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (rightModuleInverseIso A C E)
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Cᵒᵖ E)ᵒᵖ
        (F.op.tensor (DGFunctor.id E)).op.op ⋙ (rightModuleBimoduleEquivalence A D E).functor)

/-- 左制限の局所化は既存の導来制限と自然に可換する。 -/
def middleLeftRestrictionDerivedIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ bimoduleToDerived A B D ≅
      bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A B D B C (DGFunctor.id B) F :=
  Functor.isoWhiskerRight (middleLeftRestrictionIso A B C D F) (bimoduleToDerived A B D) ≪≫
    (eqToIso (derivedBimoduleRestriction_fac A B D B C (DGFunctor.id B) F)).symm

/-- 右制限の局所化も既存の導来制限と自然に可換する。 -/
def middleRightRestrictionDerivedIso :
    BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A C E ⋙
        derivedBimoduleRestriction A D E C E F (DGFunctor.id E) :=
  Functor.isoWhiskerRight (middleRightRestrictionIso A C D F E) (bimoduleToDerived A D E) ≪≫
    (eqToIso (derivedBimoduleRestriction_fac A D E C E F (DGFunctor.id E))).symm

end SerrePositivity.DifferentialGraded
