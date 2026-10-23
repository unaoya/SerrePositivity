module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalMapNativeHomComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalMapNativeActionNaturality

/-!
概要：元の二 native 表現間へ元の模型側比較を一意に反映し、指定正方形 hu を証明する。
方針：同じ元の全 Hom 比較の充満忠実性に、元の両端比較で挟んだ指定同型を渡す。
規約：二つの元の表現と模型側比較を保持。使われ方：三角形の native 作用比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a b : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
local notation "z" => coherentDiagramTotalVertex G
local notation "x" => Sigma.fst (coherentTotalMapNativeRepresentation F G a)
local notation "y" => Sigma.fst (coherentTotalMapNativeRepresentation F G b)
local notation "S" => Iso.inv (smallUnstraighteningHomIso F (KanObject.obj (spaceInfinityObject z)))
local notation "u₀" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G a) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))
local notation "u₁" => vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G b) S)
  rfl (smallUnstraighteningHomIso_inv_vertex F
    (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G b))

/-- 元の指定模型比較から、同じ二 native 表現を結ぶ比較を一意に反映する。 -/
def coherentTotalMapNativeRepresentationComparison
    (m : VertexIso
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a)))
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G b)))) : VertexIso x y :=
  fullyFaithfulComparisonPreimage (coherentTotalMapNativeHomComparison_isFullyFaithful F G) u₀ u₁ m

/-- 反映した元の比較は、元の二表現と指定模型比較の正方形 hu を厳密に満たす。 -/
lemma coherentTotalMapNativeRepresentationComparison_square
    (m : VertexIso
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a)))
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G b)))) :
    u₀ ≪≫ m = VertexIso.map (coherentTotalMapNativeRepresentationComparison F G a b m)
      (coherentTotalMapNativeHomComparison F G) ≪≫ u₁ := by
  exact fullyFaithfulComparisonPreimage_square
    (coherentTotalMapNativeHomComparison_isFullyFaithful F G) u₀ u₁ m

end SerrePositivity.InfinityCategories.F2
