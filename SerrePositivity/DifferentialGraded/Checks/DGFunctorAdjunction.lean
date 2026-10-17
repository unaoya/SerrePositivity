module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import Mathlib.Data.ZMod.Basic

/-! # graph延長–制限随伴の独立宇宙・全次数・三角恒等式の検査 -/
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
