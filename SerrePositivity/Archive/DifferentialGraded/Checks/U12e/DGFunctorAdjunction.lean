module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import Mathlib.Data.ZMod.Basic

/-! # graph延長–制限随伴の独立宇宙・全次数・三角恒等式の検査

## 概要
graph延長–制限随伴の独立宇宙・全次数・三角恒等式の検査。

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

example : (dgModuleExtension A D E F).onClosed ⊣ moduleRestriction A D E F.op :=
  dgModuleExtensionRestrictionAdjunction A D E F

example (N : RightModule A D) (x y : Dᵒᵖ) {p r n : ℤ}
    (f : GradedHom A x y p) (m : (N.obj x).X r) (hn : r + p = n) :
    (functorExtensionInsertionComponent A D E F N y.unop).f n
      (moduleAction A N f m hn) =
    moduleAction A (restrictModule A D E F.op ((dgModuleExtension A D E F).obj N)) f
      ((functorExtensionInsertionComponent A D E F N x.unop).f r m) hn :=
  functorExtensionInsertion_action A D E F N x y f m hn

example (M : ModuleCategory A D) :
    (dgModuleExtension A D E F).onClosed.map ((dgModuleUnit A D E F).app M) ≫
      (dgModuleCounit A D E F).app ((dgModuleExtension A D E F).onClosed.obj M) = 𝟙 _ :=
  dgModule_left_triangle A D E F M

example (M : ModuleCategory A E) :
    (dgModuleUnit A D E F).app ((moduleRestriction A D E F.op).obj M) ≫
      (moduleRestriction A D E F.op).map ((dgModuleCounit A D E F).app M) = 𝟙 _ :=
  dgModule_right_triangle A D E F M

-- source対象型のsmallnessを使わないgraph左作用の単位計算。
example (X : Type v) [DGCategory A X] (F : DGFunctor A X E) (x y : X) {p : ℤ}
    (f : GradedHom A x y p) :
    leftAction A ((functorGraph A X E F).leftAt (F.obj x)) f
      (unitElement A (F.obj x)).val (zero_add p) = (F.map x y).f p f :=
  functorGraph_leftAction_unit A X E F x y f

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) :
    (dgModuleExtension (ZMod 2) X Y F).onClosed ⊣ moduleRestriction (ZMod 2) X Y F.op :=
  dgModuleExtensionRestrictionAdjunction (ZMod 2) X Y F

#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.leftAction_heq
#print axioms SerrePositivity.DifferentialGraded.BalancedTensor.element_balanced_zero
#print axioms SerrePositivity.DifferentialGraded.functorGraph_leftAction_unit
#print axioms SerrePositivity.DifferentialGraded.functorExtensionInsertion_action
#print axioms SerrePositivity.DifferentialGraded.functorExtensionUnit
#print axioms SerrePositivity.DifferentialGraded.functorExtensionUnit_eval
#print axioms SerrePositivity.DifferentialGraded.functorExtensionInsertion_map
#print axioms SerrePositivity.DifferentialGraded.dgModuleUnit
#print axioms SerrePositivity.DifferentialGraded.dgModule_right_triangle
#print axioms SerrePositivity.DifferentialGraded.dgModule_left_triangle
#print axioms SerrePositivity.DifferentialGraded.dgModuleExtensionRestrictionAdjunction
