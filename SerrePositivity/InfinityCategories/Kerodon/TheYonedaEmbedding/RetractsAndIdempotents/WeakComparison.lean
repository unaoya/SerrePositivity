module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape

/-!
概要：元の弱い retract の商から、元の強い分裂の添字への標準写像を構成する。
方針：元の包含・射影の合成二単体を、同じ恒等長辺の商へ降ろす。
規約：元の二射と分裂頂点を保持し、単射性・inner anodyne 性は後で証明する。
使われ方：HTT 4.4.5.6 の添字包含の具体的な写像。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の包含と元の射影を持つ、強い分裂の元の二単体。 -/
def walkingRetractionTriangle : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₂ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetraction)

/-- 元の二単体の最初の辺は、元の包含。 -/
lemma walkingRetractionTriangle_section :
    stdSimplex.δ (2 : Fin 3) ≫ walkingRetractionTriangle.{u} =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection) := by
  dsimp only [walkingRetractionTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, nerve.δ₂_mk₂_eq]

/-- 元の二単体の最後の辺は、元の射影。 -/
lemma walkingRetractionTriangle_retraction :
    stdSimplex.δ (0 : Fin 3) ≫ walkingRetractionTriangle.{u} =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetraction) := by
  dsimp only [walkingRetractionTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, nerve.δ₀_mk₂_eq]

/-- 元の二単体の長辺は、同じ分裂頂点の元の恒等辺。 -/
lemma walkingRetractionTriangle_longEdge :
    stdSimplex.δ (1 : Fin 3) ≫ walkingRetractionTriangle.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse ≫ SSet.yonedaEquiv.symm (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage) := by
  dsimp only [walkingRetractionTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    nerve.δ₁_mk₂_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection_retraction, ← nerve.σ₀_mk₀_eq,
    ← stdSimplex.σ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero]
  simp only [SSet.comp_const]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse ≫
    (SSet.yonedaEquiv (X := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit)).symm (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage)
  rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 元の弱い retract の商から元の強い分裂の添字への、同じ三角形の比較。 -/
def weakComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc walkingRetractionTriangle (SSet.yonedaEquiv.symm (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage))
    walkingRetractionTriangle_longEdge

/-- 標準比較の後に元の三角形を厳密に回収する。 -/
lemma weakComparison_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ weakComparison.{u} = walkingRetractionTriangle := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc_triangle _ _ _

/-- 標準比較は元の分裂頂点を厳密に回収する。 -/
lemma weakComparison_imagePoint :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakImagePoint ≫ weakComparison.{u} = SSet.yonedaEquiv.symm (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc_imagePoint _ _ _

/-- 強い分裂は元の標準比較への制限で、同じ元の弱い retract 図式を与える。 -/
def StrongSplitting.weakDiagram {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram X := weakComparison ≫ s.val

/-- 強い分裂を制限した元の二単体は、同じ元の包含・射影の合成二単体。 -/
lemma StrongSplitting.weakDiagram_triangle {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ s.weakDiagram = walkingRetractionTriangle ≫ s.val := by
  rw [StrongSplitting.weakDiagram, ← Category.assoc, weakComparison_triangle]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.5.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison
