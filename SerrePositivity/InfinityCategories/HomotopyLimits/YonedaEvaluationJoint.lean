module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseDiagram
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction

/-!
概要：全 C・全前層にまたがる元の Yoneda Hom と元の評価を、同じ底上の図式に固定する。
方針：元の全 twisted arrow 射影への底写像と、内部 Hom の元の評価を使用する。
規約：全二変数の元の写像を保持。比較射とその同値性はまだ主張しない。
使われ方：全 Yoneda 評価の比較の、一つの大域的な始域・終域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の C の反変な変数と、元の全前層係数を同時に記録する底。 -/
def YonedaEvaluationJointBase (C : SSet.{u}) : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj C.op ⊗ PresheafInfinity C

/-- 元の共同 Hom 射影に入る、全 Yoneda と全前層の同じ両変数の写像。 -/
def yonedaHomJointBaseMap (C : SSet.{u}) [Quasicategory C] :
    YonedaEvaluationJointBase C ⟶ (PresheafInfinity C).op ⊗ PresheafInfinity C :=
  ((uliftOppositeIso.{u, u + 1} C).hom ≫ SSet.opFunctor.map (yonedaInfinityMap C)) ⊗ₘ
    𝟙 (PresheafInfinity C)

/-- 元の Yoneda から元の全前層への共同 Hom の全図式。 -/
def yonedaHomJointDiagram (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (YonedaEvaluationJointBase C) ⟶
      SpaceInfinity.{u + 1} :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaHomJointBaseMap C) ≫
    twistedArrowHomInfinity (PresheafInfinity C)

/-- 元の全前層族の、元の C における全共同評価。 -/
def yonedaEvaluationJointNative (C : SSet.{u}) :
    YonedaEvaluationJointBase C ⟶ SpaceInfinity.{u} :=
  (ihom.ev ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).app SpaceInfinity.{u}

/-- 元の同じ全共同評価を、指定された同じ空間宇宙変更で読む全図式。 -/
def yonedaEvaluationJointDiagram (C : SSet.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (YonedaEvaluationJointBase C) ⟶
      SpaceInfinity.{u + 1} :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaEvaluationJointNative C) ≫
    F2.Compact.spaceUniverseDiagram.{u}

end SerrePositivity.InfinityCategories.HomotopyLimits
