module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueTriangleIntervalImage
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の右精密化の値を、係数の前合成後も元の指定三角形輸送へ戻す。
方針：両面の式で両端を照合し、同じ実辺の類の一致に前合成を適用する。
規約：元の fiber と任意の全係数を保持。使われ方：同じ反転 Hom 係数での比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "L" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "H" => SimplicialCategory.sHom K L

/-- 同じ右区間の値の実始点は元の長辺での同じ値の頂点。 -/
lemma pointedRightRefinementValue_source_eq_triangle :
    (pointedIntervalValueAction K L).app (Opposite.op ⦋0⦌)
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up ((H).δ 1 (coherentTriangleHomotopy s)))) =
    (pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
      (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s)))) := by
  change (pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
    (ULift.up ((H).δ 1 (coherentTriangleHomotopy s))) = _
  rw [coherentTriangleHomotopy_source, kanHom_vertex]
  rfl

/-- 同じ右区間の値の実終点は元の二辺合成での同じ値の頂点。 -/
lemma pointedRightRefinementValue_target_eq_triangle :
    (pointedIntervalValueAction K L).app (Opposite.op ⦋0⦌)
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up ((H).δ 0 (coherentTriangleHomotopy s)))) =
    (pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
      (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s)))) := by
  change (pointedValueHomTransport K L).app (Opposite.op ⦋0⦌)
    (ULift.up ((H).δ 0 (coherentTriangleHomotopy s))) = _
  rw [coherentTriangleHomotopy_target, kanHom_vertex]
  rfl

/-- 同じ全係数の前合成後も、元の右精密化の値は指定三角形輸送の像そのもの。 -/
lemma pointedRightRefinement_value_pre_heq_triangle {P : SSet.{u + 1}}
    (q : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
    HEq (VertexIso.map
      (VertexIso.map (coherentKanRightRefinementIso K L (coherentTriangleHomotopy s))
        (pointedIntervalValueAction K L))
      ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj (L).obj)))
      (VertexIso.map (pointedValueTriangleTransportIso s)
        ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj (L).obj))) :=
  vertexIso_map_heq_of_heq _ _
    (pointedRightRefinementValue_source_eq_triangle s)
    (pointedRightRefinementValue_target_eq_triangle s)
    (pointedValueTriangleIntervalImage_iso s)
    ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj (L).obj))

end SerrePositivity.InfinityCategories.F2
