module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import Mathlib.Data.ZMod.Basic

/-! # dg制限・主K随伴・延長の射影性保存と導来Hom同値

## 概要
dg制限・主K随伴・延長の射影性保存と導来Hom同値。

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
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

example : (dgModuleRestriction A D E F.op).onClosed = moduleRestriction A D E F.op :=
  dgModuleRestriction_onClosed_eq A D E F.op

example : (dgModuleExtension A D E F).onHomotopy ⊣
    (dgModuleRestriction A D E F.op).onHomotopy := dgModuleHomotopyAdjunction A D E F

-- 元のHomにflatnessや有界性を要求しない。
example {P : ModuleCategory A D} (hP : moduleHomotopicallyProjective A D P) :
    moduleHomotopicallyProjective A E ((dgModuleExtension A D E F).onClosed.obj P) :=
  dgModuleExtension_homotopicallyProjective A D E F hP

example (X : DerivedModuleCategory A D) (Y : DerivedModuleCategory A E) :
    ((dgDerivedExtension A D E F).obj X ⟶ Y) ≃
      (X ⟶ (dgDerivedRestriction A D E F).obj Y) :=
  dgDerivedExtensionHomEquiv A D E F X Y

-- dg一般補題は、対象型がu-smallでなくても使える。
example (X : Type v) (Y : Type w) [DGCategory A X] [DGCategory A Y]
    (L : DGFunctor A X Y) (R : DGFunctor A Y X) (adj : L.onClosed ⊣ R.onClosed) :
    L.onHomotopy ⊣ R.onHomotopy := DGFunctor.homotopyAdjunction L R adj

example (X : Type v) (Y : Type w) [DGCategory A X] [DGCategory A Y]
    (L : DGFunctor A X Y) (R : DGFunctor A Y X) (adj : L.onClosed ⊣ R.onClosed)
    (x : ClosedCategory A X) :
    (DGFunctor.homotopyAdjunctionUnit L R adj).app ((toHomotopy A X).obj x) =
      (toHomotopy A X).map (adj.unit.app x) := rfl

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y)
    {P : ModuleCategory (ZMod 2) X} (hP : moduleHomotopicallyProjective (ZMod 2) X P) :
    moduleHomotopicallyProjective (ZMod 2) Y
      ((dgModuleExtension (ZMod 2) X Y F).onClosed.obj P) :=
  dgModuleExtension_homotopicallyProjective (ZMod 2) X Y F hP

#print axioms SerrePositivity.DifferentialGraded.moduleRestrictionParam
#print axioms SerrePositivity.DifferentialGraded.moduleRestrictionHom
#print axioms SerrePositivity.DifferentialGraded.moduleRestrictionHom_identity
#print axioms SerrePositivity.DifferentialGraded.moduleRestrictionHom_comp
#print axioms SerrePositivity.DifferentialGraded.dgModuleRestriction
#print axioms SerrePositivity.DifferentialGraded.dgModuleRestriction_map_eval
#print axioms SerrePositivity.DifferentialGraded.dgModuleRestriction_map
#print axioms SerrePositivity.DifferentialGraded.dgModuleRestriction_onClosed_eq
#print axioms SerrePositivity.DifferentialGraded.DGFunctor.homotopyAdjunctionUnit
#print axioms SerrePositivity.DifferentialGraded.DGFunctor.homotopyAdjunctionCounit
#print axioms SerrePositivity.DifferentialGraded.DGFunctor.homotopyAdjunction_left_triangle
#print axioms SerrePositivity.DifferentialGraded.DGFunctor.homotopyAdjunction_right_triangle
#print axioms SerrePositivity.DifferentialGraded.DGFunctor.homotopyAdjunction
#print axioms SerrePositivity.DifferentialGraded.dgModuleEnrichedRestrictionAdjunction
#print axioms SerrePositivity.DifferentialGraded.dgModuleHomotopyAdjunction
#print axioms SerrePositivity.DifferentialGraded.dgModuleHomotopyRestriction_quasiIso
#print axioms SerrePositivity.DifferentialGraded.dgModuleExtension_homotopicallyProjective
#print axioms SerrePositivity.DifferentialGraded.dgDerivedRestrictionComputation
#print axioms SerrePositivity.DifferentialGraded.dgProjectiveDerivedExtensionHomEquiv
#print axioms SerrePositivity.DifferentialGraded.dgDerivedExtensionHomEquivOnModules
#print axioms SerrePositivity.DifferentialGraded.dgDerivedExtensionHomEquiv
