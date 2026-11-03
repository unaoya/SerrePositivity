module
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalColimit

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentInvertibleTotalKan
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedCoherentEmptyProductNative
public import SerrePositivity.InfinityCategories.Core.FunctorTerminal
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：sifted な任意の小さい底上の、各値が終対象である coherent 図式の指定余極限も終対象。
方針：関手圏内の終対象の一意比較を元の全空間 Kan 比較へ移し、指定余錐へ戻す。
規約：元の余極限余錐・頂点を保持。底の quasicategory 性は要求しない。
使われ方：P_Σ の指定前層余極限の空積条件を、元の評価余錐で判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} [IsSiftedInfinity B]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hF : ∀ b, IsTerminalVertex (F.app (Opposite.op ⦋0⦌) b))
include hF

/-- 元の全空間余極限の頂点は、各値が終対象なら sifted な任意の底上で終対象。 -/
lemma siftedTerminalDiagramTotalVertex_isTerminal :
    IsTerminalVertex (F2.coherentDiagramTotalCocone F).vertex := by
  let G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} := SSet.const pointSpaceVertex
  have hf := isTerminalVertex_functorVertex_of_pointwise F hF
  have hg := isTerminalVertex_functorVertex_of_pointwise G
    (fun _ ↦ pointSpaceVertex_isTerminalVertex)
  let e : FunctorIso F G := terminalVertexIso hf hg
  let t := intervalMappingVertexOfEdge (SSet.Edge.ofTruncated (FunctorIso.edge e))
  have ht : IsInvertibleEdge (intervalMappingEdgeOfVertex t) := by
    rw [show intervalMappingEdgeOfVertex t = SSet.Edge.ofTruncated (FunctorIso.edge e) from
      (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]
    exact FunctorIso.edge_isInvertible e
  have hi := coherentInvertibleTotalKanNativeEdge_isInvertible F G t ht
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk
    (totalKanNativeEdge F G (coherentTransformationTotalKanMap F G t)).toTruncated) := hi
  let d := asIso (SSet.Truncated.HomotopyCategory.homMk
    (totalKanNativeEdge F G (coherentTransformationTotalKanMap F G t)).toTruncated)
  have hg' : IsTerminalVertex (F2.coherentDiagramTotalVertex G) := by
    rw [← F2.coherentDiagramTotalCocone_vertex G]
    exact siftedCoherentPointTotalVertex_isTerminal B
  exact hg'.of_vertexIso d.symm

/-- 元の図式の指定余極限余錐は、各値が終対象なら同じ頂点で終対象になる。 -/
lemma siftedTerminalDiagramColimit_isTerminal (q : JoinCocone F) (hq : IsColimitCone q) :
    IsTerminalVertex q.vertex := by
  have e : VertexIso (X := sliceUnder F) q (F2.coherentDiagramTotalCocone F) :=
    initialVertexIso hq (F2.coherentDiagramTotalCocone_isColimit F)
  exact (siftedTerminalDiagramTotalVertex_isTerminal F hF).of_vertexIso
    (e.map (sliceUnderProjection F)).symm

end SerrePositivity.InfinityCategories.HomotopyLimits
