module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalMapNative
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentCoconeTransportAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：元の native 作用比較の指定全 Hom 成分と指定余錐比較を明示して束ねる。
方針：同じ二成分を合成し、具体的頂点射の表示変更だけを保持する。
規約：native な射・比較・成分を再選択しない。使われ方：上側 native 因子の自然性。
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
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)

/-- 元の native 作用比較を作る同じ二つの指定成分の合成。 -/
def coherentTotalMapNativeActionComponentsIso :
    VertexIso ((coherentCoconeTransportAction F (coherentDiagramTotalCocone F)
      (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
        (coherentTotalMapNativeRepresentation F G a).1)
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))) :=
  ((coherentCoconeTransportActionIso F (coherentDiagramTotalCocone F)
    (coherentDiagramTotalVertex G)).app (coherentTotalMapNativeRepresentation F G a).1).symm ≪≫
    vertexIsoOfEq (VertexIso.map (coherentTotalMapNativeComparisonIso F G a)
      (smallUnstraighteningHomIso F
        (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).inv) rfl
      (smallUnstraighteningHomIso_inv_vertex F
        (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a))

/-- 同じ実単位と具体的頂点射の合成の、元の二つの持ち上げ表示は厳密に一致する。 -/
lemma coherentTotalMapNativeActionComponents_target :
    (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a) =
      coherentLargeTotalUnit F ≫
        (SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a) := by
  rw [Functor.map_comp, coherentLargeTotalUnit, Category.assoc]

end SerrePositivity.InfinityCategories.F2
