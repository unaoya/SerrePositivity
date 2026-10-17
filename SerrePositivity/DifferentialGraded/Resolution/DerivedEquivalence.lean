module
public import SerrePositivity.DifferentialGraded.Resolution.CanonicalZigzag
public import SerrePositivity.DifferentialGraded.Derived.FunctorDerivedEquivalence

/-! # dg圏解像度の増大・比較に沿う主導来加群圏の同値

## 概要
dg圏解像度の増大・比較に沿う主導来加群圏の同値。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.KFlatDGResolution
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  (P : KFlatDGResolution.{u, v, w} A D)

/-- 元のdg圏のHomにflatnessを要求せず、増大に沿って実際の導来加群圏を比較する。 -/
def moduleDerivedEquivalence : DerivedModuleCategory A P.source ≌ DerivedModuleCategory A D :=
  dgFunctorDerivedEquivalence A P.source D P.augmentation P.quasiEquivalence

omit [Small.{u} D] in
/-- 標準zigzagの左脚に沿う実際の導来同値。 -/
def comparisonLeftModuleDerivedEquivalence :
    DerivedModuleCategory A P.ComparisonSource ≌ DerivedModuleCategory A P.source :=
  dgFunctorDerivedEquivalence A P.ComparisonSource P.source P.comparisonLeft
    P.comparisonLeft_quasiEquivalence

/-- 標準zigzagの右脚に沿う実際の導来同値。 -/
def comparisonRightModuleDerivedEquivalence :
    DerivedModuleCategory A P.ComparisonSource ≌
      DerivedModuleCategory A (canonical A D).source :=
  dgFunctorDerivedEquivalence A P.ComparisonSource (canonical A D).source P.comparisonRight
    P.comparisonRight_quasiEquivalence

/-- 二つの指定解像度の主導来加群圏を、元のdg圏を経由して比較する。 -/
def changeModuleDerivedEquivalence (Q : KFlatDGResolution.{u, v, z} A D) :
    DerivedModuleCategory A P.source ≌ DerivedModuleCategory A Q.source :=
  P.moduleDerivedEquivalence.trans Q.moduleDerivedEquivalence.symm

lemma changeModuleDerivedEquivalence_functor (Q : KFlatDGResolution.{u, v, z} A D) :
    (P.changeModuleDerivedEquivalence Q).functor =
      dgDerivedExtension A P.source D P.augmentation ⋙
        dgDerivedRestriction A Q.source D Q.augmentation := rfl

lemma changeModuleDerivedEquivalence_inverse (Q : KFlatDGResolution.{u, v, z} A D) :
    (P.changeModuleDerivedEquivalence Q).inverse =
      dgDerivedExtension A Q.source D Q.augmentation ⋙
        dgDerivedRestriction A P.source D P.augmentation := rfl

end SerrePositivity.DifferentialGraded.KFlatDGResolution
