module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueTriangleSquare
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorVertexEquivPostVertex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedRightMorphismTransport

/-!
概要：元の Kan 射の全 Hom 値比較を、同じ辺の普遍輸送の実射で表示する。
方針：元の右 Hom の零単体を元の辺へ厳密に戻し、内部 Hom の頂点往復を使う。
規約：元の Hom 成分と同じ辺を保持。使われ方：普遍三角形比較と指定三角形同型の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "A" => vertexFiber pointedSpaceProjection (spaceInfinityVertex K)
local notation "W" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "v" => intervalMappingVertexOfEdge (pointedRightMorphismEdge f)
local notation "P" => parametrizedFiberTransport pointedSpaceProjection
  (spaceInfinityVertex K) (spaceInfinityVertex L)

/-- 元の Kan 射での全 Hom 輸送の頂点は、同じ辺での普遍輸送の実射と値の合成。 -/
lemma pointedValueHomTransport_morphism_vertex :
    (pointedValueHomTransport K L).app (Opposite.op ⦋0⦌) (ULift.up (functorVertex f)) =
      functorVertex (((functorVertexEquiv _ _).symm
        ((P).app (Opposite.op ⦋0⦌) v)) ≫ W) := by
  change ((ihom A).map W).app (Opposite.op ⦋0⦌)
    ((P).app (Opposite.op ⦋0⦌)
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (functorVertex f)))) = _
  rw [coherentKanRightHomInterval_morphism]
  exact functorVertexEquiv_symm_post_vertex ((P).app (Opposite.op ⦋0⦌) v) W

/-- 同じ元の Hom 成分を、同じ辺の普遍輸送と元の Kan 射の間の指定比較として保持。 -/
def pointedValueMorphismUniversalActionIso :
    FunctorIso ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map f)
      (((functorVertexEquiv _ _).symm ((P).app (Opposite.op ⦋0⦌) v)) ≫ W) :=
  vertexIsoOfEq (pointedValueHomActionAt f) rfl (pointedValueHomTransport_morphism_vertex f)

end SerrePositivity.InfinityCategories.F2
