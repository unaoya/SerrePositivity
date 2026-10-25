module

public import SerrePositivity.InfinityCategories.Core.UniverseEdgeTransport
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseMorphismDown
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseQuasicategory

/-!
概要：実関手同型の宇宙降下。
方針：代表ホモトピーを降ろし、各頂点の実辺の可逆性を同じ辺で反映する。
規約：標的だけ quasicategory。関手や単位を選び直さない。
使われ方：持ち上げた局所化の実延長を元の宇宙の延長へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.LocalizationUniverse

/-- ホモトピーの各点の辺も元の同じ辺へ降下する。 -/
lemma unliftSimplicialHomotopy_vertexEdge {X Y : SSet.{u}}
    {f g : SSet.uliftFunctor.{v, u}.obj X ⟶ SSet.uliftFunctor.{v, u}.obj Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge (unliftSimplicialHomotopy H) x).toTruncated =
      UniverseEdge.down (simplicialHomotopyVertexEdge H (ULift.up x)).toTruncated := by
  apply Truncated.Edge.ext
  rfl

/-- 宇宙持ち上げは、同じ二つの実関手の間の全自然同型の存在を反映する。 -/
def functorIso_of_ulift {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f)
      ((SSet.uliftFunctor.{v, u}).map g)) : FunctorIso f g :=
  functorIsoOfPointwiseInvertibleHomotopy (unliftSimplicialHomotopy e.simplicialHomotopy) (by
    intro x
    rw [unliftSimplicialHomotopy_vertexEdge]
    exact UniverseEdge.invertible_down
      (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) (ULift.up x)))

end SerrePositivity.InfinityCategories.LocalizationUniverse
