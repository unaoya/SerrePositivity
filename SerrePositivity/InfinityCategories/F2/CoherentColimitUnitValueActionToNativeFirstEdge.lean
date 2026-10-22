module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitValueActionToFirstEdge
public import SerrePositivity.InfinityCategories.F2.CoherentColimitValueProjectionEndpoints

/-!
概要：五因子式の最後の比較を、同じ最後辺の native 中央比較の実前合成へ同定する。
方針：元の全前合成の比較と、実二端点を明示した元の中央比較への射影を合成する。
規約：二辺と指定比較を保持。使われ方：上側単位因子との整合と消去。
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
local notation "pF" => leftUnstraighteningProjection F
local notation "pG" => leftUnstraighteningProjection G
local notation "xF" => relativeFunctorVertex pF pF (𝟙 (leftUnstraightening F))
  (Category.id_comp pF)
local notation "xG" => relativeFunctorVertex pG pG (𝟙 (leftUnstraightening G))
  (Category.id_comp pG)
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "V" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (KanObject.obj (spaceInfinityObject (coherentDiagramTotalVertex J)))

/-- 元の最後の比較の固定値への像は、同じ native 中央比較の元の最初辺による前合成。 -/
lemma coherentColimitUnitValueActionTo_firstEdge_heq_native :
    HEq (coherentColimitUnitValueActionTo B b pF
      ((functorHomotopyRelativePost a pF).app (Opposite.op ⦋0⦌) xF))
      ((coherentColimitNativeTriangleActionComparison B b).precomp f) := by
  refine (coherentColimitUnitValueActionTo_precomp_firstEdge B a b).symm.trans ?_
  refine (vertexIso_map_heq_of_heq (coherentColimitUnitValueActionTo B b pG xG)
    (coherentColimitNativeTriangleActionComparison B b)
    (coherentColimitValueProjection_lower_vertex B b)
    (coherentColimitValueProjection_upper_vertex B b)
    (coherentColimitUnitValueActionTo_total_heq_native B b) ((pre f).app V)).trans ?_
  exact heq_of_eq (functorIso_precomp_eq_mapIso
    (coherentColimitNativeTriangleActionComparison B b) f).symm

end SerrePositivity.InfinityCategories.F2
