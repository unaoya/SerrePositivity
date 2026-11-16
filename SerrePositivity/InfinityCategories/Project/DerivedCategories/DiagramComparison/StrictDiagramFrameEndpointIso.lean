module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramSourceFrameZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramCofibrantVertices

/-!
概要：同じ source frame と fibrant target の両端点を元の図式の局所化頂点へ戻す。
方針：元の objectwise 擬同型辺を指定局所化で反転する。
規約：元の増大射と置換比較自身の像を使う。
使われ方：RR01 の frame Hom の端点移送。HTT 4.2.4.4 の実評価との照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits _root_.HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance frameEndpointModel : ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 元の擬同型辺の指定局所化像から取る頂点同型。 -/
def strictDiagramLocalizationQuasiIso {X Y : StrictComplexDiagram A d}
    (f : X ⟶ Y) (hf : strictDiagramQuasiIsos A d f) :
    VertexIso ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
      ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Y)) := by
  have hi := (strictDiagramLocalization_inverts A d) ((strictDiagramWeakEdges_mk₁ A d f).2 hf)
  change IsInvertibleEdge
    ((edgeOfSimplex (X := strictComplexDiagramNerve A d) (ComposableArrows.mk₁ f)).map
      ((truncation 2).map (strictDiagramLocalization A d))) at hi
  have hi' : IsInvertibleEdge
      (((nerve.edgeMk f).map (strictDiagramLocalization A d)).toTruncated) := by
    exact (isInvertibleEdge_congr
      (e := ((nerve.edgeMk f).map (strictDiagramLocalization A d)).toTruncated)
      (f := (edgeOfSimplex (X := strictComplexDiagramNerve A d) (ComposableArrows.mk₁ f)).map
        ((truncation 2).map (strictDiagramLocalization A d))) rfl).mpr hi
  haveI := hi'
  exact asIso (Truncated.HomotopyCategory.homMk
    (((nerve.edgeMk f).map (strictDiagramLocalization A d)).toTruncated))

/-- 同じ零次の source frame 対象から、元の図式への増大射の像。 -/
def strictDiagramSourceFrameEndpointIso (X : StrictComplexDiagram A d) :
    VertexIso ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (strictDiagramSourceFrameZero A d X)))
      ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X)) :=
  strictDiagramLocalizationQuasiIso A d
    ((strictDiagramSourceFrame A d X).augmentation.app (SimplexCategory.mk 0)) (by
      rw [← strictDiagramReedyModelCategory_weakEquivalences]
      exact (strictDiagramSourceFrame A d X).augmentation_weakEquivalence _)

/-- 元の fibrant 置換比較の像。端点を戻すときはこの同じ同型の逆を使う。 -/
def strictDiagramFibrantTargetEndpointIso (Y : StrictComplexDiagram A d) :
    VertexIso ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Y))
      ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (strictDiagramFibrantTarget A d Y))) :=
  strictDiagramLocalizationQuasiIso A d (strictDiagramFibrantTargetComparison A d Y)
    (strictDiagramFibrantTargetComparison_quasiIso A d Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
