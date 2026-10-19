module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeComparisonPiZero

/-!
概要：部分余極限頂点の付加で構成した射を、元の余錐の制限の π₀ の像と同定する。
方針：比較余錐から余錐圏の実際の辺を作り、元の制限と頂点の脚を厳密に照合する。
規約：比較射と脚の構成に使った選択をそのまま保持し、別の Hom 表示で代用しない。
使われ方：部分余極限対象の span の余錐を、共通部分の整合性を保って元の図式へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} {p : A ⟶ X}
  (c : JoinCocone p) (hc : IsColimitCone c) (i : A ⟶ C)
  (F : C ⟶ X) (hi : i ≫ F = p) (d : JoinCocone F)

/-- 比較余錐の頂点の脚は、付加した頂点から元の頂点への構成済みの辺そのもの。 -/
lemma colimitAttachmentComparison_leg_edge :
    ((colimitAttachmentComparison c hc i F hi d).leg (joinInr A Δ[0])).edge =
      (colimitAttachmentApexEdge c hc i F hi d).edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ joinMap (joinInr A Δ[0]) (𝟙 Δ[0]) ≫
    (coherentCoconeOfDiagramEq (colimitAttachedDiagram_left c i F hi)
      ((colimitAttachedCocone c hc i F hi d).restrict
        (pushout.inl (joinInl A Δ[0]) i))).val) = _
  rw [coherentCoconeOfDiagramEq_val]
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ joinMap (joinInr A Δ[0]) (𝟙 Δ[0]) ≫
    (joinMap (pushout.inl (joinInl A Δ[0]) i) (𝟙 Δ[0]) ≫
      (colimitAttachedCocone c hc i F hi d).val)) = _
  rw [← Category.assoc (joinMap (joinInr A Δ[0]) (𝟙 Δ[0])), ← joinMap_comp,
    Category.id_comp]
  rfl

/-- 部分余極限から元の余錐の制限への、余錐圏の中の実際の比較辺。 -/
def colimitAttachmentCoconeEdge :
    (sliceUnder p).Edge c (coherentCoconeOfDiagramEq hi (d.restrict i)) := by
  let e := coconeComparisonEdge c (colimitAttachmentComparison c hc i F hi d)
  have ht : coconeComparisonTarget c (colimitAttachmentComparison c hc i F hi d) =
      coherentCoconeOfDiagramEq hi (d.restrict i) := by
    rw [coconeComparisonTarget_eq, colimitAttachmentComparison_restrict]
  exact ⟨e.edge, e.src_eq, e.tgt_eq.trans ht⟩

/-- 元の余錐の制限を、元の指定頂点を終点とする余錐空間の点として表示する。 -/
def colimitAttachmentFiberVertex [Quasicategory X] : (coconeMappingSpace p d.vertex) _⦋0⦌ :=
  initialFiberVertexAt (sliceUnderProjection p) (coherentCoconeOfDiagramEq hi (d.restrict i))
    d.vertex (by
      change (coherentCoconeOfDiagramEq hi (d.restrict i)).vertex = d.vertex
      rw [coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict])

/-- 部分余錐の制限の π₀ の像は、構成済みの実際の部分余極限の比較辺の類になる。 -/
lemma coconeMappingSpacePiZeroEquiv_attachment [Quasicategory X] :
    coconeMappingSpacePiZeroEquiv c hc d.vertex
        (SSet.π₀.mk (colimitAttachmentFiberVertex i F hi d)) =
      SSet.Truncated.HomotopyCategory.homMk (colimitAttachmentApexEdge c hc i F hi d) := by
  have hv : (coherentCoconeOfDiagramEq hi (d.restrict i)).vertex = d.vertex := by
    rw [coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict]
  have h := leftFibrationInitialFiberPiZeroEquiv_edgeAt (sliceUnderProjection p) hc
    (colimitAttachmentCoconeEdge c hc i F hi d) d.vertex hv
  refine h.trans ?_
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact (coconeComparisonEdge_projection c (colimitAttachmentComparison c hc i F hi d)).trans
    (colimitAttachmentComparison_leg_edge c hc i F hi d)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
