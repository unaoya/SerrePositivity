module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.FunctorCoherence
public import SerrePositivity.DifferentialGraded.Resolution.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 準同値に沿う中間圏変更の全導来自然同型の検査

## 概要
準同値に沿う中間圏変更の全導来自然同型の検査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hF : QuasiEquivalence F) (hE : localHomKFlat A E)

-- C・Dの局所Hom K-flat性も制限後の加群自体のK-flat性も追加しない。
example : middleRestrictionDerivedSource A B C D E F hE ≅
    derivedBimoduleComposeFunctor A B C E hE :=
  derivedMiddleRestrictionIso A B C D E F hF hE

-- 両変数の任意の導来対象について、既存の制限・導来合成の間の同型となる。
example (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((derivedBimoduleRestriction A D E C E F (DGFunctor.id E)).obj Q)).obj
      ((derivedBimoduleRestriction A B D B C (DGFunctor.id B) F).obj P) ≅
    ((derivedBimoduleComposeFunctor A B C E hE).obj Q).obj P :=
  ((derivedMiddleRestrictionIso A B C D E F hF hE).app Q).app P

example (P : BimoduleCategory A B C) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    IsIso (derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq) :=
  derivedMiddleRestrictionComparison_isIso A B C D E F hF hE P Q R q hq

example {Q Q' : DerivedBimoduleCategory A C E} (g : Q ⟶ Q') :
    (middleRestrictionDerivedSource A B C D E F hE).map g ≫
        (derivedMiddleRestrictionIso A B C D E F hF hE).hom.app Q' =
      (derivedMiddleRestrictionIso A B C D E F hF hE).hom.app Q ≫
        (derivedBimoduleComposeFunctor A B C E hE).map g :=
  (derivedMiddleRestrictionIso A B C D E F hF hE).hom.naturality g

example (Q : DerivedBimoduleCategory A C E) {P P' : DerivedBimoduleCategory A B C}
    (f : P ⟶ P') :
    ((middleRestrictionDerivedSource A B C D E F hE).obj Q).map f ≫
        ((derivedMiddleRestrictionIso A B C D E F hF hE).hom.app Q).app P' =
      ((derivedMiddleRestrictionIso A B C D E F hF hE).hom.app Q).app P ≫
        ((derivedBimoduleComposeFunctor A B C E hE).obj Q).map f :=
  ((derivedMiddleRestrictionIso A B C D E F hF hE).hom.app Q).naturality f

-- 元のCのHomにflat性を課さず、指定dg圏解像度の増大へ適用できる。
example (S : KFlatDGResolution.{u, w, z} A C) :
    middleRestrictionDerivedSource A B C S.source E S.augmentation hE ≅
      derivedBimoduleComposeFunctor A B C E hE :=
  derivedMiddleRestrictionIso A B C S.source E S.augmentation S.quasiEquivalence hE

example (X : Type v) (Y : Type w) (Z : Type z) (T : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) T]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} T]
    (G : DGFunctor (ZMod 2) Z Y) (hG : QuasiEquivalence G) (hT : localHomKFlat (ZMod 2) T) :
    middleRestrictionDerivedSource (ZMod 2) X Y Z T G hT ≅
      derivedBimoduleComposeFunctor (ZMod 2) X Y T hT :=
  derivedMiddleRestrictionIso (ZMod 2) X Y Z T G hG hT

namespace SerrePositivity.DifferentialGraded
#print axioms dgModuleExtension_relativeKFlat_quasiIso
#print axioms functorExtensionUnit_canonical_quasiIso
#print axioms functorExtensionUnit_relativeKFlat_quasiIso
#print axioms moduleRestriction_reflects_quasiIso
#print axioms functorExtensionTranspose
#print axioms functorExtensionTranspose_eq
#print axioms functorExtensionTranspose_unit_fac
#print axioms functorExtensionTranspose_quasiIso
#print axioms BalancedTensor.graphTensorYoneda_naturality
#print axioms BalancedTensor.graphTensorYonedaIso
#print axioms BalancedTensor.graphTensorYonedaIso_hom_eval
#print axioms BalancedTensor.functorExtensionTensorIso
#print axioms BalancedTensor.rightι_functorExtensionTensorIso_hom
#print axioms BalancedTensor.functorExtension_relativeKFlat
#print axioms BalancedTensor.resolvedRestrictionComparison
#print axioms BalancedTensor.ι_resolvedRestrictionComparison
#print axioms BalancedTensor.ι_functorExtensionTranspose_eval
#print axioms BalancedTensor.tensorAction_balance_map
#print axioms BalancedTensor.functorExtensionTensorIso_resolvedComparison
#print axioms BalancedTensor.resolvedRestrictionComparison_quasiIso
#print axioms BimoduleTensor.middleRestrictionResolvedValueIso
#print axioms BimoduleTensor.middleRestrictionResolvedMap_value
#print axioms BimoduleTensor.middleRestrictionResolvedMap_quasiIso
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_isIso
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonLocalized_isIso
#print axioms BimoduleTensor.middleDerivedKFlatComparison_isIso
#print axioms BimoduleTensor.middleRightKFlatLocalizedComparison_isIso
#print axioms BimoduleTensor.middleFullDerivedComparison_isIso
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_isIso
#print axioms BimoduleTensor.derivedMiddleRestrictionIso
#print axioms BimoduleTensor.derivedMiddleRestrictionIso_hom
end SerrePositivity.DifferentialGraded
