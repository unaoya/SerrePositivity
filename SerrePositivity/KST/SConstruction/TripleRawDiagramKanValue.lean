module
public import SerrePositivity.KST.SConstruction.TripleRawDiagramValue
public import SerrePositivity.KST.SConstruction.KanBasedAttachmentValue

/-! # 元の十二面複体の任意の Kan 値写像で第四辺の類を検出する
概要：全三角形と三つの全境界固定円柱から、指定左辺と生成第四辺の値の一致を得る。
方針：接続全体の実写像を基点表示へ送り、六対角面の消去を適用する。
規約：円柱に関する値の等号は元の実接続の全境界固定式から証明する。
使われ方：元の raw 段評価への適用と、端点固定の実比較円柱の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial
variable {E : SSet.{u}} [KanComplex E]
local instance tripleRawDiagramKanValueGroupoid : Groupoid (hoFunctor.obj E) :=
  Groupoid.ofIsGroupoid

/-- 元の全十二面・全円柱の任意の Kan 値写像は、同じ両第四辺の値を一致させる。 -/
lemma tripleRawDiagramPasting_kanValue (c : hoFunctor.obj E)
    (P : tripleRawDiagramPasting.{u} ⟶ E) :
    kanBasedEdgeValue c (stdSimplex.δ 0 ≫ outerStagePastingLeftCell ≫
        tripleSharedDirectPastingOriginal ≫ tripleSharedDirectRealizationPastingOriginal ≫
          tripleRawDiagramPastingOriginal ≫ P) =
      kanBasedEdgeValue c (stdSimplex.δ 2 ≫ tripleRawDiagramPastingSecond ≫ P) := by
  let O := tripleSharedDirectPastingOriginal.{u} ≫
    tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal ≫ P
  let N := outerBinaryPastingOriginal.{u} ≫ outerStagePastingOriginal ≫ O
  apply tripleRawDiagramPasting_value (fun e => kanBasedEdgeValue c (e ≫ P))
  · intro T
    simpa only [Category.assoc] using kanBasedEdgeValue_triangle c (T ≫ P)
  · have h := kanBasedEdgeValue_attachment c correctionNormalizationLeftEdge
      (fixedCylinderAttachmentOriginal (SSet.boundary 1).ι
        correctionNormalizationRightAttachingEdge ≫ N)
    simpa only [correctionNormalizationPastingLeftTarget,
      correctionNormalizationPastingOriginal, N, O, Category.assoc] using h
  · have h := kanBasedEdgeValue_attachment c correctionNormalizationRightAttachingEdge N
    simpa only [correctionNormalizationPastingRightTarget,
      correctionNormalizationRightAttachingEdge, correctionNormalizationPastingOriginal,
      N, O, Category.assoc] using h
  · have h := kanBasedEdgeValue_comparisonAttachment c
      (stdSimplex.δ 2 ≫ outerStagePastingLeftCell)
      (stdSimplex.δ 2 ≫ outerStagePastingRightCell)
      (tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal ≫ P)
    simpa only [tripleSharedDirectPastingOriginal, Category.assoc] using h

/-- 同じ全実複体の両第四辺を回収する平行辺は、元のホモトピー圏で同じ射。 -/
lemma tripleRawDiagramPasting_edge_class (P : tripleRawDiagramPasting.{u} ⟶ E)
    {x y : E _⦋0⦌} (a b : E.Edge x y)
    (ha : stdSimplex.δ 0 ≫ outerStagePastingLeftCell ≫ tripleSharedDirectPastingOriginal ≫
        tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal ≫ P =
      SSet.yonedaEquiv.symm a.edge)
    (hb : stdSimplex.δ 2 ≫ tripleRawDiagramPastingSecond ≫ P =
      SSet.yonedaEquiv.symm b.edge) :
    SSet.HomotopyCategory.homMk a = SSet.HomotopyCategory.homMk b := by
  have h := tripleRawDiagramPasting_kanValue (SSet.HomotopyCategory.mk x) P
  rw [ha, hb] at h
  exact kanBasedEdgeValue_detects _ ⟨𝟙 _⟩ a b h

end SerrePositivity.KST.SConstruction
