module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightActualSectionsRestriction
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SpaceTensorHomValueTailNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws

/-!
概要：元の重みの制限の普遍辺を、同じ関手で写して頂点の辺と照合する。
方針：slice の後合成と射影の既存の自然性を使い、端点表示の等式だけを追う。
規約：元の `sectionsConeMap` の辺を選び直さない。
使われ方：G8 の指定極限の値比較と標準後合成の全族比較をつなぐ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 始点の表示の等式による移送は、辺の元の一単体を変えない。 -/
lemma edge_source_transport_simplex {E : SSet.{u}} {x x' y : E _⦋0⦌}
    (h : x = x') (e : E.Edge x y) :
    (Eq.mp (congrArg (fun t ↦ E.Edge t y) h) e).edge = e.edge := by
  cases h
  rfl

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}
  {E : SSet.{u + 1}} [Quasicategory E]
  (φ : X ⟶ Y) (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
  (cX : JoinCone (SetWeight.diagram X F)) (hcX : IsLimitCone cX)
  (cY : JoinCone (SetWeight.diagram Y F)) (hcY : IsLimitCone cY)

/-- 元の切断制限の辺は、同じ指定普遍辺の射影の一単体を保持する。 -/
lemma setWeightSectionsMap_simplex :
    (SetWeight.sectionsMap φ F cX hcX cY hcY).edge =
      ((SetWeight.sectionsConeMap φ F cX hcX cY).map
        (sliceOverProjection (SetWeight.diagram X F))).edge := by
  exact edge_source_transport_simplex (SetWeight.restrictSectionsCone_vertex φ F cY)
    ((SetWeight.sectionsConeMap φ F cX hcX cY).map
      (sliceOverProjection (SetWeight.diagram X F)))

/-- 元の指定普遍辺を同じ関手で写した錐の辺。 -/
def setWeightMappedSectionsConeEdge {D : SSet.{u + 1}} (q : E ⟶ D) :
    (sliceOver (SetWeight.diagram X (F ≫ q))).Edge
      (mapJoinCone q (SetWeight.restrictSectionsCone φ F cY)) (mapJoinCone q cX) :=
  (SetWeight.sectionsConeMap φ F cX hcX cY).map
    (sliceOverPostcomp (SetWeight.diagram X F) q)

/-- 同じ写された錐の辺の射影は、元の切断制限の辺の像と同じ一単体。 -/
lemma setWeightMappedSectionsConeEdge_simplex {D : SSet.{u + 1}} (q : E ⟶ D) :
    ((setWeightMappedSectionsConeEdge φ F cX hcX cY q).map
      (sliceOverProjection (SetWeight.diagram X (F ≫ q)))).edge =
    ((SetWeight.sectionsMap φ F cX hcX cY hcY).map q).edge := by
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
    (SetWeight.sectionsConeMap φ F cX hcX cY).edge)
      (sliceOverPostcomp_projection (SetWeight.diagram X F) q)
  change _ = q.app (Opposite.op ⦋1⦌) (SetWeight.sectionsMap φ F cX hcX cY hcY).edge
  rw [setWeightSectionsMap_simplex]
  exact h

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
