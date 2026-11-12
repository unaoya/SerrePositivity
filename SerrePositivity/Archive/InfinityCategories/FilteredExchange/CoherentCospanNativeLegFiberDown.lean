module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeLegFiberIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningFunctorIso

/-!
概要：native 全錐の二脚と元の実際の fiber 射の指定同型を、元の小さい宇宙へ降ろす。
方針：全忠実な宇宙持ち上げで評価射を降ろし、元の指定同型を同じ関手空間で下降する。
規約：元の fiber と作用射を保持。使われ方：元の模型 fiber 比較の二脚との同時照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local instance : KanComplex (vertexFiber pX b) := vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber pY b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 元の小さい宇宙での native 全錐の左脚。 -/
def coherentCospanNativeLeftLegFiberDown : vertexFiber pF b ⟶ vertexFiber pX b :=
  uliftMorphismDown (coherentCospanNativeLeftLegFiberMap F X Y Z C b)

/-- 元の小さい宇宙での同じ全錐の右脚。 -/
def coherentCospanNativeRightLegFiberDown : vertexFiber pF b ⟶ vertexFiber pY b :=
  uliftMorphismDown (coherentCospanNativeRightLegFiberMap F X Y Z C b)

/-- 左脚を再度持ち上げると、元の評価した射そのものを回収する。 -/
lemma coherentCospanNativeLeftLegFiberDown_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (coherentCospanNativeLeftLegFiberDown F X Y Z C b) =
      coherentCospanNativeLeftLegFiberMap F X Y Z C b := uliftMorphismDown_lift _

/-- 右脚も元の評価した射を厳密に回収する。 -/
lemma coherentCospanNativeRightLegFiberDown_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (coherentCospanNativeRightLegFiberDown F X Y Z C b) =
      coherentCospanNativeRightLegFiberMap F X Y Z C b := uliftMorphismDown_lift _

/-- 元の実際の左 fiber 射との指定同型を、元の小さい宇宙へ下降する。 -/
def coherentCospanNativeLeftLegFiberDownIso :
    FunctorIso (coherentCospanNativeLeftLegFiberDown F X Y Z C b)
      (vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
        (coherentTransformationTotalMap_projection F X C.toLeft) b) :=
  functorIsoDown (functorIsoOfEq (coherentCospanNativeLeftLegFiberIso F X Y Z C b)
    (coherentCospanNativeLeftLegFiberDown_lift F X Y Z C b).symm rfl)

/-- 右も同じ指定比較を保持して、実際の元の fiber 射との同型へ下降する。 -/
def coherentCospanNativeRightLegFiberDownIso :
    FunctorIso (coherentCospanNativeRightLegFiberDown F X Y Z C b)
      (vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
        (coherentTransformationTotalMap_projection F Y C.toRight) b) :=
  functorIsoDown (functorIsoOfEq (coherentCospanNativeRightLegFiberIso F X Y Z C b)
    (coherentCospanNativeRightLegFiberDown_lift F X Y Z C b).symm rfl)

end SerrePositivity.InfinityCategories.F2
