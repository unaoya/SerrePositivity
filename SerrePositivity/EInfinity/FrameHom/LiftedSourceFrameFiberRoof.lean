module
public import SerrePositivity.EInfinity.FrameHom.LiftedSourceFrameElements
public import SerrePositivity.EInfinity.FrameHom.FrameArrowElements
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftElements

/-!
概要：元の持ち上げたHomのfiber要素圏を、同じ固定標的のroofの反対圏へ戻す。
方針：Homの宇宙持ち上げ・単体のULift・既存のelements/costructured同値を合成する。
規約：通常の要素圏と反対の要素圏の向きを保持し、元の次数とラベルを回収する。
使われ方：同じnative fiber射と元の固定始域roofとの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Opposite SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

/-- 同じ元のHom単体のfiberの要素圏を、元の固定標的のroofの反対圏へ移す。 -/
def liftedSourceFrameFiberRoofEquivalence (P : liftedSourceFrameIndex (C := C)) :
    (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P ≌
      (CostructuredArrow (Q.obj (AsSmall.down.obj P).1.unop)
        (R.obj (AsSmall.down.obj P).2))ᵒᵖ :=
  (ULiftHom.equiv (C := ((liftedSourceFrameCoefficients Q R).obj P).Elements)).symm.trans
    ((SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.elementsEquivalence
      ((cosimplicialHom (Q.obj (AsSmall.down.obj P).1.unop)).obj
        (R.obj (AsSmall.down.obj P).2))).symm.trans
      (FrameArrows.elementsCostructuredEquivalence
        (Q.obj (AsSmall.down.obj P).1.unop) (R.obj (AsSmall.down.obj P).2)).rightOp)

/-- 同じroofの次数は、元のHom単体の次数そのもの。 -/
theorem liftedSourceFrameFiberRoofEquivalence_degree (P : liftedSourceFrameIndex (C := C))
    (s : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.obj s).unop).left =
      s.obj.unop := rfl

/-- 同じroofの射のラベルは、元の持ち上げたHom単体のdownそのもの。 -/
theorem liftedSourceFrameFiberRoofEquivalence_value (P : liftedSourceFrameIndex (C := C))
    (s : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.obj s).unop).hom =
      s.val.down := rfl

/-- 同じroofの単体作用素も、元の要素圏の作用素を反対向きにしたもの。 -/
theorem liftedSourceFrameFiberRoofEquivalence_operator (P : liftedSourceFrameIndex (C := C))
    {s t : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P}
    (f : s ⟶ t) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.map f).unop).left =
      f.down.hom.unop := rfl
end SerrePositivity.EInfinity.FrameHom
