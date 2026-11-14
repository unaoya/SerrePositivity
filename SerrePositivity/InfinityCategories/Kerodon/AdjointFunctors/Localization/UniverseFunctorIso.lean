module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.UniverseEdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseMorphismDown
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseQuasicategory

/-!
概要：実関手同型の宇宙降下。
方針：代表ホモトピーを降ろし、各頂点の実辺の可逆性を同じ辺で反映する。
規約：標的だけ quasicategory。関手や単位を選び直さない。
使われ方：持ち上げた局所化の実延長を元の宇宙の延長へ戻す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- ホモトピーの各点の辺も元の同じ辺へ降下する。 -/
lemma unliftSimplicialHomotopy_vertexEdge {X Y : SSet.{u}}
    {f g : SSet.uliftFunctor.{v, u}.obj X ⟶ SSet.uliftFunctor.{v, u}.obj Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unliftSimplicialHomotopy H) x).toTruncated =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.down (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (ULift.up x)).toTruncated := by
  apply Truncated.Edge.ext
  rfl

/-- 宇宙持ち上げは、同じ二つの実関手の間の全自然同型の存在を反映する。 -/
def functorIso_of_ulift {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{v, u}).map f)
      ((SSet.uliftFunctor.{v, u}).map g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unliftSimplicialHomotopy e.simplicialHomotopy) (by
    intro x
    rw [unliftSimplicialHomotopy_vertexEdge]
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.invertible_down
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible e) (ULift.up x)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
