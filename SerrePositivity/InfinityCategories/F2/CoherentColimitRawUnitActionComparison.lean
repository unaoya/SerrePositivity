module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitValueActionTo
public import SerrePositivity.InfinityCategories.F2.FunctorSquareConstantPostFiberMap
public import SerrePositivity.InfinityCategories.F2.PointedFiberValueTo
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawUnitActions

/-!
概要：最初辺の元の二面比較を、値射影前の元の実全空間作用として保持する。
方針：同じ下面の逆と上面を合成し、定値最後辺の実後合成への値の一致を使う。
規約：共有対角・元の全二面を保持。使われ方：一点輸送比較との自然性の交換式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "rc" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "z₁" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)

omit b in
/-- 元の raw 全空間上の二面比較。下面の逆と上面の元の指定値を保つ。 -/
def coherentColimitRawUnitActionComparison :
    FunctorIso (coherentColimitRawLowerCompositeAction B a)
      (coherentColimitRawUpperCompositeAction B a) :=
  (functorTriangleTotalActionIso (coherentColimitUnitLowerTriangle B a)).symm ≪≫
    functorTriangleTotalActionIso (coherentColimitUnitUpperTriangle B a)

/-- 五因子式の最初辺の後合成因子は、同じ raw 全空間比較の実後合成の値。 -/
lemma coherentColimitFirstEdgePost_valueTo_heq_raw :
    HEq (VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
      (functorHomotopyRelativePost rc p)) Q)
      (FunctorIso.postcomp (coherentColimitRawUnitActionComparison B a)
        ((leftUnstraighteningMappingVertexMap (SSet.const z₁) (SSet.const z₃)
          (coherentVertexOfHomotopy rc)).val ≫ constantUnstraighteningFiberProjection
            (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₃ ≫ V)) := by
  rw [constantTargetValueProjectionTo_eq_fiberValueTo]
  exact functorSquareComparison_map_constantPost_fiberMap
    (coherentColimitUnitUpperTriangle B a) (coherentColimitUnitLowerTriangle B a) rc V

end SerrePositivity.InfinityCategories.F2
