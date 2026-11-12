module
public import SerrePositivity.KST.SConstruction.TracedTripleRawStageComparison

/-! # 全十二面と新しい全端点固定第四辺比較を同時に保持する
概要：元の指定左辺と生成辺の間に実比較円柱を貼り、元の全比較複体を保持する。
方針：同じ両全辺と入力区間境界に沿う比較円柱接続を使う。
規約：全十二面・全正規化円柱・全高次比較と、新しい全比較円柱を同時に回収する。
使われ方：隣接段との構造適合を元の高次比較族とともに構成する次工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial

/-- 元の指定左第四辺の同じ全包含。 -/
def tripleRawPrescribedEdge : (Δ[1] : SSet.{u}) ⟶ tripleRawDiagramPasting :=
  stdSimplex.δ 0 ≫ outerStagePastingLeftCell ≫ tripleSharedDirectPastingOriginal ≫
    tripleSharedDirectRealizationPastingOriginal ≫ tripleRawDiagramPastingOriginal

/-- 元の第二 BF 面の下面となる生成第四辺の同じ全包含。 -/
def tripleRawGeneratedEdge : (Δ[1] : SSet.{u}) ⟶ tripleRawDiagramPasting :=
  stdSimplex.δ 2 ≫ tripleRawDiagramPastingSecond

/-- 全十二面・全円柱・全高次比較に、第四辺の全端点固定比較を貼った実複体。 -/
def tripleRawStageComparisonPasting : SSet.{u} :=
  fixedCylinderComparisonAttachment (SSet.boundary 1).ι
    tripleRawPrescribedEdge tripleRawGeneratedEdge

/-- 元の全十二面・全比較族を持つ複体全体の同じ像。 -/
def tripleRawStageComparisonPastingOriginal :
    tripleRawDiagramPasting.{u} ⟶ tripleRawStageComparisonPasting :=
  fixedCylinderComparisonOriginal (SSet.boundary 1).ι
    tripleRawPrescribedEdge tripleRawGeneratedEdge

/-- 元の全端点固定比較円柱の同じ全像。 -/
def tripleRawStageComparisonPastingCell :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ tripleRawStageComparisonPasting :=
  fixedCylinderComparisonCell (SSet.boundary 1).ι tripleRawPrescribedEdge tripleRawGeneratedEdge

variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の全十二面・全比較族と第四辺の全端点固定円柱を同時に保持する実写像。 -/
def monicKTracedTripleRawStageComparisonPasting (n : ℕ) :
    tripleRawStageComparisonPasting.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  fixedCylinderComparisonMap (SSet.boundary 1).ι tripleRawPrescribedEdge tripleRawGeneratedEdge
    (monicKTracedTripleRawDiagramPasting F f g h n)
    (monicKTracedTripleRawStageComparison F f g h n).homotopy
    (by
      rw [tripleRawPrescribedEdge]
      simp only [Category.assoc]
      rw [monicKTracedTripleRawDiagramPasting_original,
        monicKTracedTripleSharedDirectRealizationPasting_original,
        monicKTracedTripleSharedDirectPasting_left_comparison]
      rw [SSet.Edge.map_edge, SSet.yonedaEquiv_symm_comp])
    (by
      rw [tripleRawGeneratedEdge, Category.assoc,
        monicKTracedTripleRawDiagramPasting_generated]
      rw [SSet.Edge.map_edge, SSet.yonedaEquiv_symm_comp])
    (monicKTracedTripleRawStageComparison F f g h n).relative

/-- 元の全十二面・全円柱・全高次比較の実写像全体を厳密に回収する。 -/
lemma monicKTracedTripleRawStageComparisonPasting_original (n : ℕ) :
    tripleRawStageComparisonPastingOriginal ≫
        monicKTracedTripleRawStageComparisonPasting F f g h n =
      monicKTracedTripleRawDiagramPasting F f g h n :=
  fixedCylinderComparisonMap_original _ _ _ _ _ _ _ _

/-- 元の指定左辺と生成第四辺を結ぶ同じ全比較円柱そのものも厳密に回収する。 -/
lemma monicKTracedTripleRawStageComparisonPasting_cell (n : ℕ) :
    tripleRawStageComparisonPastingCell ≫ monicKTracedTripleRawStageComparisonPasting F f g h n =
      (monicKTracedTripleRawStageComparison F f g h n).homotopy.h :=
  fixedCylinderComparisonMap_cell _ _ _ _ _ _ _ _

/-- 同じ円柱は、その構成に用いた同じ実比較三角形を厳密に保持する。 -/
lemma monicKTracedTripleRawStageComparisonPasting_triangle (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ tripleRawStageComparisonPastingCell ≫
        monicKTracedTripleRawStageComparisonPasting F f g h n =
      SSet.yonedaEquiv.symm
        (monicKTracedTripleRawStageComparisonTriangle F f g h n).simplex := by
  rw [monicKTracedTripleRawStageComparisonPasting_cell]
  exact monicKTracedTripleRawStageComparison_triangle F f g h n

end SerrePositivity.KST.SConstruction
