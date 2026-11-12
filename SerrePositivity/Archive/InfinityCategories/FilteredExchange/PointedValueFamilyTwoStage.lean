module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyEvaluationActionFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueFamilyTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanRightCompositionMoving

/-!
概要：動く始点と二射の元の値比較を、同じ合成輸送の終点まで貼り合わせる。
方針：第一比較の評価像、第二比較、元の合成四角形の比較を合成する。
規約：三つの指定比較と全係数を保持し、合成則の証明とは区別する。
使われ方：Ncomp に必要な指定値の合成則の両辺を同じ型で比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K M L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K M))
  (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom M L))
local notation "V₀" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K))
local notation "V₂" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "t" => diagonalFiberTransport pointedSpaceProjection x
  (y ≫ coherentKanRightHomInterval K M)
local notation "c" => lift y z ≫ coherentHomComposition K M L

/-- 同じ第一比較を第二射で評価し、元の第二比較と合成四角形を続ける。 -/
def pointedValueFamilyTwoStageIso :
    FunctorIso (pointedRightFamilyEvaluation (x ≫ V₀) c)
      (diagonalFiberTransport pointedSpaceProjection x
        (c ≫ coherentKanRightHomInterval K L) ≫ V₂) :=
  functorIsoOfEq
    (pointedRightFamilyEvaluationValueIso (pointedValueFamilyTransportIso x y) z ≪≫
      pointedValueFamilyTransportIso t z ≪≫
      (coherentKanRightCompositionTransport_movingIso x y z).postcomp V₂)
    (pointedRightFamilyEvaluation_comp (x ≫ V₀) y z) rfl

/-- 合成射の元の指定比較を、同じ始点・同じ終点の型で保持する。 -/
def pointedValueFamilyCompositeIso :
    FunctorIso (pointedRightFamilyEvaluation (x ≫ V₀) c)
      (diagonalFiberTransport pointedSpaceProjection x
        (c ≫ coherentKanRightHomInterval K L) ≫ V₂) :=
  pointedValueFamilyTransportIso x c

end SerrePositivity.InfinityCategories.F2
