module
public import SerrePositivity.DifferentialGraded.Resolution.DerivedEquivalence
public import Mathlib.Data.ZMod.Basic

/-! # dg準同値による導来同値と指定解像度比較の監査

## 概要
dg準同値による導来同値と指定解像度比較の監査。

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
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

-- 本質的全射性だけで保守性を得る。Hom準同型性とは区別する。
example (hF : F.onHomotopy.EssSurj) {X Y : DerivedModuleCategory A E} (f : X ⟶ Y)
    [IsIso ((dgDerivedRestriction A D E F).map f)] : IsIso f :=
  dgDerivedRestriction_reflectsIso A D E F hF f

example (hF : QuasiEquivalence F) : DerivedModuleCategory A D ≌ DerivedModuleCategory A E :=
  dgFunctorDerivedEquivalence A D E F hF

example (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).inverse = dgDerivedRestriction A D E F := rfl

example (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom = dgDerivedExtensionUnit A D E F := rfl

example (P : KFlatDGResolution.{u, v, z} A D) :
    DerivedModuleCategory A P.source ≌ DerivedModuleCategory A D := P.moduleDerivedEquivalence

-- 元のdg圏のHomのflatness・有界性を仮定せず、独立のsource宇宙の解像度を比較する。
example (P : KFlatDGResolution.{u, v, w} A D) (Q : KFlatDGResolution.{u, v, z} A D) :
    (P.changeModuleDerivedEquivalence Q).functor =
      dgDerivedExtension A P.source D P.augmentation ⋙
        dgDerivedRestriction A Q.source D Q.augmentation := rfl

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) (hF : QuasiEquivalence F) :
    DerivedModuleCategory (ZMod 2) X ≌ DerivedModuleCategory (ZMod 2) Y :=
  dgFunctorDerivedEquivalence (ZMod 2) X Y F hF

namespace SerrePositivity.DifferentialGraded
#print axioms representableHomotopyToDerived
#print axioms representableHomotopyToDerivedComputation
#print axioms dgDerivedExtension_representable_essImage
#print axioms dgDerivedRestriction_reflectsZero
#print axioms dgDerivedRestriction_reflectsIso
#print axioms dgDerivedRestrictionReflectsIsomorphisms
#print axioms dgDerivedExtensionCounit_isIso_all
#print axioms dgFunctorDerivedEquivalence
#print axioms dgFunctorDerivedEquivalence_functor
#print axioms dgFunctorDerivedEquivalence_inverse
#print axioms dgFunctorDerivedEquivalence_unit
#print axioms dgFunctorDerivedEquivalence_counit
#print axioms KFlatDGResolution.moduleDerivedEquivalence
#print axioms KFlatDGResolution.comparisonLeftModuleDerivedEquivalence
#print axioms KFlatDGResolution.comparisonRightModuleDerivedEquivalence
#print axioms KFlatDGResolution.changeModuleDerivedEquivalence
#print axioms KFlatDGResolution.changeModuleDerivedEquivalence_functor
#print axioms KFlatDGResolution.changeModuleDerivedEquivalence_inverse
end SerrePositivity.DifferentialGraded
