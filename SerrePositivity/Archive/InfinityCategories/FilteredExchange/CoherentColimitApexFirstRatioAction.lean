module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexFirstValueSquare
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawPointDiagonalRatio
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismPointDiagonalRatio
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismUniversalActionPrecomp
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawLongCanonical
/-!
概要：元の第一辺の raw 比を、同じ第一射の作用比較と標準全係数での評価値へ戻す。
方針：同じ実 raw prism の比を一般区間表示へ移し、元の初期係数を標準 fiber で読む。
規約：元の実辺・全初期係数・指定二因子と比較の値を保持する。
使われ方：第一射の元の評価比較の回収。
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
local notation "K₀" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "uf" => CategoryTheory.Functor.map SSet.uliftFunctor f
local notation "Craw" => q ≫
  eqToHom (congrArg (vertexFiber p) (coherentColimitApex_raw_zero_vertex B T))
local notation "C" => pointedCoherentFiberComparison K₀ ≫
  eqToHom (congrArg (vertexFiber p) (Eq.symm (spaceInfinityVertex_eq_coherent K₀)))
/-- 概要：元の第一辺の raw 比は同じ第一射の作用比較の値。
方針：同じ実辺と全初期係数で一般比較を制限する。
規約：指定値を保持。使われ方：第一辺評価の二因子。 -/
lemma coherentColimitApexFirstSquareRawValueRatio_heq_action :
    HEq (coherentColimitApexFirstSquareRawValueRatio B T)
      ((pointedValueMorphismUniversalActionIso f).precomp Craw) := by
  exact pointedMorphismPointDiagonalRatio_heq_action_of_heq f (coherentColimitRawSpaceEdge B a)
    (coherentColimitApex_raw_zero_vertex B T) (coherentColimitApex_raw_one_vertex B T)
    ((coherentColimitRawSpaceEdge_first B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 2 s)).symm) q _
    (coherentColimitRawPointDiagonal_ratio_heq_pointed B a q
      V₀ V₁ uf (coherentColimitApexRawFirstValueIso B T))
/-- 概要：同じ raw 比を標準初期係数での元の作用比較に同定する。
方針：実初期係数と標準 fiber の同じ射を照合する。
規約：元の指定値を保持。使われ方：全 Hom の元の成分への接続。 -/
lemma coherentColimitApexFirstSquareRawValueRatio_heq_standard :
    HEq (coherentColimitApexFirstSquareRawValueRatio B T)
      ((pointedValueMorphismUniversalActionIso f).precomp C) :=
  (coherentColimitApexFirstSquareRawValueRatio_heq_action B T).trans
    (functorIso_precomp_heq_of_map_eq (pointedValueMorphismUniversalActionIso f)
      (coherentColimitApexCoefficientMap_standard B T))
/-- 概要：同じ raw 比は全 Hom 上の元の作用比較の同じ評価値。
方針：同じ標準係数による前作用で読む。
規約：全係数と指定値を保持。使われ方：第一射の評価比較。 -/
lemma coherentColimitApexFirstSquareRawValueRatio_heq_evaluation :
    HEq (coherentColimitApexFirstSquareRawValueRatio B T)
      (VertexIso.map (pointedValueHomActionAt f)
        ((pre C).app ((SSet.uliftFunctor.{u + 1, u}).obj (KanObject.obj K₁)))) :=
  (coherentColimitApexFirstSquareRawValueRatio_heq_standard B T).trans
    (pointedValueMorphismUniversalActionIso_precomp_heq_evaluation f C)
end
end SerrePositivity.InfinityCategories.F2
