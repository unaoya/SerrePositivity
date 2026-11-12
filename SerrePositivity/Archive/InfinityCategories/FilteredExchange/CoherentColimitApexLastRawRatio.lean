module

public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastValueSquare
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawPointDiagonalRatio
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismPointDiagonalRatio
/-!
概要：元の Apex の最後辺の raw 比を fiber 全体の同じ比の制限として保持する。
方針：同じ実 raw prism の比を一般の区間表示へ移し、元の辺での比較へ代入する。
規約：全初期係数・実辺・元の値因子と指定比較を保持する。
使われ方：Ncomp の最後辺の比と native 中間像の交換。
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
/-- 概要：元の最後辺の raw 辺値の逆と同じ一点普遍比較の比。
方針：同じ実辺の元の二因子を fiber 全体で保持する。
規約：指定値を再選択しない。使われ方：中間比較に沿う交換。 -/
def coherentColimitApexLastRawValueRatio :=
  pointedMorphismEdgeValueRatio g (coherentColimitRawSpaceEdge B b)
    (coherentColimitApex_raw_one_vertex B T) (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_last B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 0 s)).symm)
/-- 概要：元の指定対角値の比は fiber 全体の同じ raw 比の制限。
方針：同じ実 prism と全初期値で一般比較を制限する。
規約：元の二因子を保持。使われ方：中間比較との貼り合わせ。 -/
lemma coherentColimitApexLastSquareRawValueRatio_heq_raw_ratio :
    HEq (coherentColimitApexLastSquareRawValueRatio B T)
      ((coherentColimitApexLastRawValueRatio B T).precomp f') := by
  exact pointedMorphismPointDiagonalRatio_heq_raw_ratio_of_heq g (coherentColimitRawSpaceEdge B b)
    (coherentColimitApex_raw_one_vertex B T) (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_last B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 0 s)).symm) f' _
    (coherentColimitRawPointDiagonal_ratio_heq_pointed B b f'
      V₁ V₂ ug (coherentColimitApexRawLastValueIso B T))
end
end SerrePositivity.InfinityCategories.F2
