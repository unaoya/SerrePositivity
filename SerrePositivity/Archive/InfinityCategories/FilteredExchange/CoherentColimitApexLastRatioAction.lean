module

public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastValueSquare
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawPointDiagonalRatio
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismPointDiagonalRatio
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismUniversalActionPrecomp
/-!
概要：元の Apex の最後辺の raw 比を、同じ最後射の作用比較の値へ戻す。
方針：同じ実 raw prism の比を一般の区間表示へ移し、元の辺での比較へ代入する。
規約：全初期係数・実辺・元の値因子と指定比較を保持する。
使われ方：Ncomp の最後辺の比と native 中間像の貼り合わせ。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "s" => coherentColimitApexTriangle B T
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "f'" => q ≫ coherentColimitRawFiberTransport B a
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "ug" => CategoryTheory.Functor.map SSet.uliftFunctor g
local notation "C" => f' ≫
  eqToHom (congrArg (vertexFiber p) (coherentColimitApex_raw_one_vertex B T))
/-- 概要：元の raw 比は同じ最後射の元の作用比較の指定値。
方針：同じ実辺と全初期係数で一般比較を制限する。
規約：指定値を保持。使われ方：Ncomp の native 中間像との照合。 -/
lemma coherentColimitApexLastSquareRawValueRatio_heq_action :
    HEq (coherentColimitApexLastSquareRawValueRatio B T)
      ((pointedValueMorphismUniversalActionIso g).precomp C) := by
  exact pointedMorphismPointDiagonalRatio_heq_action_of_heq g (coherentColimitRawSpaceEdge B b)
    (coherentColimitApex_raw_one_vertex B T) (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_last B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 0 s)).symm) f' _
    (coherentColimitRawPointDiagonal_ratio_heq_pointed B b f'
      V₁ V₂ ug (coherentColimitApexRawLastValueIso B T))

/-- 概要：同じ raw 比は元の全 Hom 上の同じ作用比較の値。
方針：同じ係数射による前作用へ移す。規約：指定値を保持。
使われ方：最後射の評価比較との貼り合わせ。 -/
lemma coherentColimitApexLastSquareRawValueRatio_heq_evaluation :
    HEq (coherentColimitApexLastSquareRawValueRatio B T)
      (VertexIso.map (pointedValueHomActionAt g)
        ((pre C).app ((SSet.uliftFunctor.{u + 1, u}).obj (KanObject.obj K₂)))) :=
  (coherentColimitApexLastSquareRawValueRatio_heq_action B T).trans
    (pointedValueMorphismUniversalActionIso_precomp_heq_evaluation g C)
end
end SerrePositivity.InfinityCategories.F2
