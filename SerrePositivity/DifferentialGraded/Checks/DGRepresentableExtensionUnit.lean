module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentableUnit
public import Mathlib.Data.ZMod.Basic

/-! # graph延長–制限単位の代表加群計算と可逆性

## 概要
graph延長–制限単位の代表加群計算と可逆性。

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
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

example (d : D) : functorExtensionUnit A D E F (representable A d) ≫
    (moduleRestriction A D E F.op).map (dgModuleExtensionRepresentableIso A D E F d).hom =
      representableRestrictionMap A D E F d := functorExtensionUnit_representable A D E F d

-- Hom準同型性だけを仮定し、本質的全射性・Hom flatness・有界性を要求しない。
example (hF : HomQuasiIso F) (d : D) :
    IsIso ((dgDerivedExtensionUnit A D E F).app
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)))) :=
  dgDerivedExtensionUnit_representable_isIso A D E F hF d

example (M : ModuleCategory A D) :
    (dgModuleEnrichedRestrictionAdjunction A D E F).unit.app M =
      functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) :=
  dgModuleEnrichedRestrictionAdjunction_unit A D E F M

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) (hF : HomQuasiIso F) (x : X) :
    IsIso ((dgDerivedExtensionUnit (ZMod 2) X Y F).app
      ((moduleToDerived (ZMod 2) X).obj
        (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) x)))) :=
  dgDerivedExtensionUnit_representable_isIso (ZMod 2) X Y F hF x

namespace SerrePositivity.DifferentialGraded
#print axioms functorExtensionUnit_representable
#print axioms functorExtensionUnit_representable_quasiIso
#print axioms dgModuleExtensionRestrictionAdjunction_unit
#print axioms dgModuleEnrichedRestrictionAdjunction_unit
#print axioms dgDerivedExtensionRestrictionAdjunction_homEquiv
#print axioms dgDerivedExtensionUnit_computation
#print axioms functorExtensionUnit_resolution_quasiIso
#print axioms dgDerivedExtensionUnit_representable_isIso
#print axioms dgModuleEnrichedRestrictionAdjunction
end SerrePositivity.DifferentialGraded
