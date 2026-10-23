module

public import SerrePositivity.InfinityCategories.HomotopyLimits.StronglySaturatedHom
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Core.OuterHornConverse

/-!
概要：同じ Hom 類を持つ辺の区間頂点を、元の二単体から同型で結ぶ。
方針：右ホモトピーを pinched 写像空間の辺にし、既存の区間比較で写す。
規約：両端を保持し、区間比較の頂点は元の辺と厳密に同定する。
使われ方：単位のホモトピー代表の変更による comma 始対象性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ射を表す元の二辺は、区間写像空間内で同型な頂点を与える。 -/
def intervalVertexIsoOfHomMkEq {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e f : X.Edge x y)
    (h : Truncated.HomotopyCategory.homMk e.toTruncated =
      Truncated.HomotopyCategory.homMk f.toTruncated) :
    VertexIso (intervalMappingVertexOfEdge e) (intervalMappingVertexOfEdge f) := by
  let t : Truncated.Edge.CompStruct (Truncated.Edge.id (X := (truncation 2).obj X) x)
      f.toTruncated e.toTruncated := compStructOfHomotopyCategoryFac (by
    rw [Truncated.HomotopyCategory.homMk_id, Category.id_comp]
    exact h.symm)
  let a := pinchedHomEdgeOfRightHomotopy t
  have : IsIso (Truncated.HomotopyCategory.homMk a.toTruncated) :=
    isInvertibleEdge_of_hasFinalHornFillers a.toTruncated
      (hasFinalHornFillers_of_kanComplex a.toTruncated)
  let i := VertexIso.map (asIso (Truncated.HomotopyCategory.homMk a.toTruncated))
    (pinchedHomToIntervalMappingSpace x y)
  have he : (pinchedHomToIntervalMappingSpace x y).app (Opposite.op ⦋0⦌)
      ((pinchedHomVertexEquiv x y).symm e.toTruncated) = intervalMappingVertexOfEdge e := by
    rw [pinchedHomToIntervalMappingSpace_vertex, Equiv.apply_symm_apply]
    rfl
  have hf : (pinchedHomToIntervalMappingSpace x y).app (Opposite.op ⦋0⦌)
      ((pinchedHomVertexEquiv x y).symm f.toTruncated) = intervalMappingVertexOfEdge f := by
    rw [pinchedHomToIntervalMappingSpace_vertex, Equiv.apply_symm_apply]
    rfl
  exact eqToIso (congrArg HomotopyCategory.mk he.symm) ≪≫ i ≪≫
    eqToIso (congrArg HomotopyCategory.mk hf)

/-- 区間頂点から回収した辺の Hom 類が同じなら、元の区間頂点は同型。 -/
def intervalVertexIsoOfRecoveredHomMkEq {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (v w : (intervalMappingSpace x y) _⦋0⦌)
    (h : Truncated.HomotopyCategory.homMk (intervalMappingEdgeOfVertex v).toTruncated =
      Truncated.HomotopyCategory.homMk (intervalMappingEdgeOfVertex w).toTruncated) :
    VertexIso (X := intervalMappingSpace x y) v w := by
  let i := intervalVertexIsoOfHomMkEq (intervalMappingEdgeOfVertex v)
    (intervalMappingEdgeOfVertex w) h
  have hv : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex v) = v :=
    (intervalMappingEdgeVertexEquiv x y).apply_symm_apply v
  have hw : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex w) = w :=
    (intervalMappingEdgeVertexEquiv x y).apply_symm_apply w
  exact eqToIso (congrArg HomotopyCategory.mk hv.symm) ≪≫ i ≪≫
    eqToIso (congrArg HomotopyCategory.mk hw)

end SerrePositivity.InfinityCategories.HomotopyLimits
