module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitFirstPostLowerExchange
public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalModelLowerCancellation
public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalModelUnitExchange

/-!
概要：五因子式の残り二因子を、同じ実中間頂点の最初比較と native 最後比較へ分ける。
方針：元の合成同型の三実頂点を同時に揃える。
規約：元の二因子を保持。使われ方：上側単位を a6 の元の模型比較へ消去する。
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
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))

/-- 元の残り二因子を実中間頂点で揃えた値は、同じ最初比較と最後辺の native 比較の合成。 -/
lemma coherentColimitRightTail_valueTo_eq_native :
    vertexIsoOfEq (coherentColimitUnitRightTailValueTo B (a := a) (b := b))
      (coherentColimitFirstPost_valueTo_source_vertex B a b)
      (coherentColimitValueProjection_composite_vertex B a b) =
    coherentColimitFirstPostNativeValueToComparison B a b ≪≫
      (coherentColimitNativeTriangleActionComparison B b).precomp f := by
  have h := vertexIsoOfEq_trans
    (VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
      (functorHomotopyRelativePost rc p)) Q)
    (coherentColimitUnitValueActionTo B b p
      ((functorHomotopyRelativePost a p).app (Opposite.op ⦋0⦌) x₀))
    (coherentColimitFirstPost_valueTo_source_vertex B a b)
    (coherentColimitLastValueTo_source_vertex B a b)
    (coherentColimitValueProjection_composite_vertex B a b)
  rw [coherentColimitLastValueTo_eq_native] at h
  exact h

end SerrePositivity.InfinityCategories.F2
