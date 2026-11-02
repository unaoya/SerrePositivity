module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanCompositionDiagonalMovingValue
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyTransportPresentation

/-!
概要：元の右 Hom の全点評価比較を、同じ元の動く始点 Kan 合成比較へ値まで戻す。
方針：元の定始点比較への表示と、同じ定始点での movingIso の一致を合成する。
規約：元の指定比較と全係数を保持。使われ方：右 Hom 評価の二段合成の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の右 Hom の全点評価比較の逆は、同じ一点始点の元の movingIso の指定値である。 -/
lemma pointedRightFamilyTransportIso_symm_heq_moving {K L : KanObject.{u}}
    {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) :
    HEq (pointedRightFamilyTransportIso x y).symm
      (coherentKanRightCompositionTransport_movingIso (SSet.const pointedSpaceIdentityPoint)
        (x ≫ (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv) y) :=
  (pointedRightFamilyTransportIso_symm_heq_diagonal x y).trans
    (coherentKanRightCompositionDiagonalIso_heq_moving pointKanObject K L
      pointedSpaceIdentityPoint
      (x ≫ (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv) y)

end SerrePositivity.InfinityCategories.F2
