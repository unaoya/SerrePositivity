module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakShape
public import SerrePositivity.InfinityCategories.F2.Idempotent.Coherent

/-!
概要：元の弱い retract の商から、元の強い分裂の添字への標準写像を構成する。
方針：元の包含・射影の合成二単体を、同じ恒等長辺の商へ降ろす。
規約：元の二射と分裂頂点を保持し、単射性・inner anodyne 性は後で証明する。
使われ方：HTT 4.4.5.6 の添字包含の具体的な写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の包含と元の射影を持つ、強い分裂の元の二単体。 -/
def walkingRetractionTriangle : (Δ[2] : SSet.{u}) ⟶ SplitShape :=
  SSet.yonedaEquiv.symm (ComposableArrows.mk₂ walkingSection walkingRetraction)

/-- 元の二単体の最初の辺は、元の包含。 -/
lemma walkingRetractionTriangle_section :
    stdSimplex.δ (2 : Fin 3) ≫ walkingRetractionTriangle.{u} =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ walkingSection) := by
  dsimp only [walkingRetractionTriangle, SplitShape]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, nerve.δ₂_mk₂_eq]

/-- 元の二単体の最後の辺は、元の射影。 -/
lemma walkingRetractionTriangle_retraction :
    stdSimplex.δ (0 : Fin 3) ≫ walkingRetractionTriangle.{u} =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ walkingRetraction) := by
  dsimp only [walkingRetractionTriangle, SplitShape]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, nerve.δ₀_mk₂_eq]

/-- 元の二単体の長辺は、同じ分裂頂点の元の恒等辺。 -/
lemma walkingRetractionTriangle_longEdge :
    stdSimplex.δ (1 : Fin 3) ≫ walkingRetractionTriangle.{u} =
      longEdgeCollapse ≫ SSet.yonedaEquiv.symm (nerveEquiv.symm walkingImage) := by
  dsimp only [walkingRetractionTriangle, SplitShape]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    nerve.δ₁_mk₂_eq, walkingSection_retraction, ← nerve.σ₀_mk₀_eq,
    ← stdSimplex.σ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero]
  simp only [SSet.comp_const]
  change _ = longEdgeCollapse ≫
    (SSet.yonedaEquiv (X := nerve WalkingSplit)).symm (ComposableArrows.mk₀ walkingImage)
  rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 元の弱い retract の商から元の強い分裂の添字への、同じ三角形の比較。 -/
def weakComparison : WeakShape.{u} ⟶ SplitShape :=
  weakDesc walkingRetractionTriangle (SSet.yonedaEquiv.symm (nerveEquiv.symm walkingImage))
    walkingRetractionTriangle_longEdge

/-- 標準比較の後に元の三角形を厳密に回収する。 -/
lemma weakComparison_triangle :
    weakTriangle ≫ weakComparison.{u} = walkingRetractionTriangle := weakDesc_triangle _ _ _

/-- 標準比較は元の分裂頂点を厳密に回収する。 -/
lemma weakComparison_imagePoint :
    weakImagePoint ≫ weakComparison.{u} = SSet.yonedaEquiv.symm (nerveEquiv.symm walkingImage) :=
  weakDesc_imagePoint _ _ _

/-- 強い分裂は元の標準比較への制限で、同じ元の弱い retract 図式を与える。 -/
def StrongSplitting.weakDiagram {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) : WeakRetractionDiagram X := weakComparison ≫ s.val

/-- 強い分裂を制限した元の二単体は、同じ元の包含・射影の合成二単体。 -/
lemma StrongSplitting.weakDiagram_triangle {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) :
    weakTriangle ≫ s.weakDiagram = walkingRetractionTriangle ≫ s.val := by
  rw [StrongSplitting.weakDiagram, ← Category.assoc, weakComparison_triangle]

end SerrePositivity.InfinityCategories.F2.Idempotent
