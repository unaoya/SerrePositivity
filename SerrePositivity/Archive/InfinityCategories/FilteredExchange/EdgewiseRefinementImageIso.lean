module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：共通解像の二つの実辺の像を、その同じホモトピー類の同型として保持する。
方針：始域の Kan 性で元の辺の可逆性を得て、同じ射で写す。
規約：逆辺を選ばず、元の実辺の類を同型にする。
使われ方：指定左右区間比較の共通終点成分を二自然性正方形から消去する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X : SSet.{u}} {Y : SSet.{max u v}}
  [KanComplex ((SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X))]
  (f : (SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X) ⟶ Y) (e : X _⦋1⦌)

/-- 同じ実右解像の辺の像のホモトピー類を保持する同型。 -/
def edgewiseRefinementRightImageIso :
    VertexIso
      (f.app (Opposite.op ⦋0⦌) (ULift.up (edgewiseRefinementVertex
        (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e))))
      (f.app (Opposite.op ⦋0⦌) (ULift.up (edgewiseRefinementVertex e))) := by
  have h : IsInvertibleEdge
      (X := (SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X))
      (edgewiseRefinementRightEdgeUlift.{u, v} e).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  have : IsInvertibleEdge (X := Y)
      (((edgewiseRefinementRightEdgeUlift.{u, v} e).map f).toTruncated) := h.map f
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (((edgewiseRefinementRightEdgeUlift.{u, v} e).map f).toTruncated))

/-- 同じ実左解像の辺の像も元の類を保持する同型。 -/
def edgewiseRefinementLeftImageIso :
    VertexIso
      (f.app (Opposite.op ⦋0⦌) (ULift.up (edgewiseRefinementVertex
        (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e))))
      (f.app (Opposite.op ⦋0⦌) (ULift.up (edgewiseRefinementVertex e))) := by
  have h : IsInvertibleEdge
      (X := (SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X))
      (edgewiseRefinementLeftEdgeUlift.{u, v} e).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  have : IsInvertibleEdge (X := Y)
      (((edgewiseRefinementLeftEdgeUlift.{u, v} e).map f).toTruncated) := h.map f
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (((edgewiseRefinementLeftEdgeUlift.{u, v} e).map f).toTruncated))

end SerrePositivity.InfinityCategories.F2
