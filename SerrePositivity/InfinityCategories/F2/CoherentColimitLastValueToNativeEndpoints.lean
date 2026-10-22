module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitFirstPostValueToEndpoints
public import SerrePositivity.InfinityCategories.F2.CoherentColimitPointValueToUpperMaps
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitValueActionToNativeFirstEdge

/-!
概要：五因子式の最後辺因子の実両端を、同じ native 中央比較の実前合成へ揃える。
方針：元の三作用の実頂点と一点比較の元の始点等式を合成する。
規約：指定値・二辺を保持。使われ方：元の残り二因子と上側単位の消去。
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
local notation "uG" => coconeTransformationHomotopy (coherentDiagramTotalCocone G)
local notation "cb" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))

/-- 元の最後辺因子の始点は、同じ最後辺の下側実合成射を最初辺で前合成した頂点。 -/
lemma coherentColimitLastValueTo_source_vertex :
    NatTrans.app Q (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost cb p).app (Opposite.op ⦋0⦌)
        ((functorHomotopyRelativePost uG p).app (Opposite.op ⦋0⦌)
          ((functorHomotopyRelativePost a p).app (Opposite.op ⦋0⦌) x₀))) =
      functorVertex (f ≫ coherentColimitLowerCompositeAction B b) :=
  (coherentColimitFirstPost_valueTo_target_vertex B a b).trans
    (congrArg functorVertex (coherentColimitPointValueTo_upper_source_map B a b))

/-- 元の最後辺因子を実両端で揃えると、同じ native 中央比較の実前合成に等しい。 -/
lemma coherentColimitLastValueTo_eq_native :
    vertexIsoOfEq (coherentColimitUnitValueActionTo B b p
      ((functorHomotopyRelativePost a p).app (Opposite.op ⦋0⦌) x₀))
      (coherentColimitLastValueTo_source_vertex B a b)
      (coherentColimitValueProjection_composite_vertex B a b) =
      (coherentColimitNativeTriangleActionComparison B b).precomp f := by
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (coherentColimitUnitValueActionTo_firstEdge_heq_native B a b))

end SerrePositivity.InfinityCategories.F2
