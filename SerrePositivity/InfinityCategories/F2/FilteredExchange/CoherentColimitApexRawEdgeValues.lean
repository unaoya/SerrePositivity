module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexRawVertices
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedSpaceMorphismEdgeValueIso

/-!
概要：元の余極限二単体の三実輸送を、同じ三つの Kan 値と同じ三辺の射へ比較する。
方針：実三頂点と三面の厳密な式で、全 Hom 比較の同じ三成分を表示する。
規約：元の二単体・三辺・指定成分を保持。使われ方：元の指定三角形同型との一括比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)

/-- 元の第一辺の実輸送を、同じ二単体の最初と中間の値の間で比較する指定成分。 -/
def coherentColimitApexRawFirstValueIso :
    FunctorIso (coherentColimitRawFiberTransport B a ≫ V₁)
      (V₀ ≫ (SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom (SpaceInfinity.δ 2 s))) :=
  pointedSpaceMorphismEdgeValueIso (coherentEdgeHom (SpaceInfinity.δ 2 s))
    (coherentColimitRawSpaceEdge B a) (coherentColimitApex_raw_zero_vertex B T)
    (coherentColimitApex_raw_one_vertex B T)
    ((coherentColimitRawSpaceEdge_first B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 2 s)).symm)

/-- 元の最後辺の実輸送を、同じ二単体の中間と最後の値の間で比較する指定成分。 -/
def coherentColimitApexRawLastValueIso :
    FunctorIso (coherentColimitRawFiberTransport B b ≫ V₂)
      (V₁ ≫ (SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom (SpaceInfinity.δ 0 s))) :=
  pointedSpaceMorphismEdgeValueIso (coherentEdgeHom (SpaceInfinity.δ 0 s))
    (coherentColimitRawSpaceEdge B b) (coherentColimitApex_raw_one_vertex B T)
    (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_last B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 0 s)).symm)

/-- 元の長辺の実輸送を、同じ二単体の最初と最後の値の間で比較する指定成分。 -/
def coherentColimitApexRawLongValueIso :
    FunctorIso (coherentColimitRawFiberTransport B d ≫ V₂)
      (V₀ ≫ (SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom (SpaceInfinity.δ 1 s))) :=
  pointedSpaceMorphismEdgeValueIso (coherentEdgeHom (SpaceInfinity.δ 1 s))
    (coherentColimitRawSpaceEdge B d) (coherentColimitApex_raw_zero_vertex B T)
    (coherentColimitApex_raw_two_vertex B T)
    ((coherentColimitRawSpaceEdge_long B a T).trans
      (pointedRightMorphismEdge_recover (SpaceInfinity.δ 1 s)).symm)

end SerrePositivity.InfinityCategories.F2
