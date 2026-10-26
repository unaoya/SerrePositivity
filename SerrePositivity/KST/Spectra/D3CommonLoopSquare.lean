module

public import SerrePositivity.KST.Spectra.D3CommonLoopCone

/-!
概要：共通 BF 対象上の実 loop 四角形と、指定比較を保持した全四角形同型。
方針：元の固定 cospan 内の同じ実錐を四角形へ移す。
規約：厳密 tail 終点と二つの元の cospan 脚を保持。対象間の全 Hom 整合は別工程。
使われ方：d3b② の共通対象上の実 loop 図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonLoopSquareSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance commonLoopSquareHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- N_X を実始点とし、元の厳密 tail を終点とする実 loop 四角形。 -/
def commonLoopSquare (X : OmegaSpectrum.{u}) : LoopSquare (coherentNerveVertex (tail X)) := by
  let F := coneSquare (commonLoopCone X)
  have hr : squareRightEdge ≫ F =
      SSet.yonedaEquiv.symm (coherentNerveEdge (basedPathProjection (tail X))).edge := by
    rw [coneSquare_right, BasedLoop.diagram, edgeCospan_left]
    rfl
  have ht : squareTopEdge ≫ F =
      SSet.yonedaEquiv.symm (coherentNerveEdge (fromPoint (tail X))).edge := by
    rw [coneSquare_top, BasedLoop.diagram, edgeCospan_right]
    rfl
  have hv : squareVertex F 1 1 = coherentNerveVertex (tail X) := by
    rw [← squareRightEdge_target, hr, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (basedPathProjection (tail X))).tgt_eq
  have h₀ : squareVertex F 1 0 = coherentNerveVertex (basedPath (tail X)) := by
    rw [← squareRightEdge_source, hr, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (basedPathProjection (tail X))).src_eq
  have h₁ : squareVertex F 0 1 = coherentNerveVertex spectrumPoint := by
    rw [← squareTopEdge_source, ht, Equiv.apply_symm_apply]
    exact (coherentNerveEdge (fromPoint (tail X))).src_eq
  exact { square := F
          zero_corner := h₁.symm ▸ pointZeroVertex.isZero
          target_eq := hv
          other_zero := h₀.symm ▸ basedPath_isZeroVertex (tail X)
          isPullback := coneSquare_isPullback _ (commonLoopCone_isLimit X) }

/-- 同じ実 loop 四角形の始点は N_X 自体。 -/
lemma commonLoopSquare_vertex (X : OmegaSpectrum.{u}) :
    (commonLoopSquare X).vertex = coherentNerveVertex (commonRefinement X) := by
  change squareVertex (coneSquare (commonLoopCone X)) 0 0 = _
  rw [coneSquare_vertex, commonLoopCone_vertex]

/-- 元の実 loop 四角形から共通四角形へ、同じ共通左脚を持つ図式比較。 -/
def commonLoopSquareInclusionIso (X : OmegaSpectrum.{u}) :
    FunctorIso (loopSourceSquare X).square (commonLoopSquare X).square := by
  have e := VertexIso.map (commonLoopConeIso X)
    (sliceSquareDiagramMap (BasedLoop.diagram (tail X)))
  rw [sliceSquareDiagramMap_vertex, sliceSquareDiagramMap_vertex] at e
  exact e

/-- 元の固定 cospan を保つ錐比較を、実四角形全体の FunctorIso へ移す。
これは対象 X ごとの図式比較であり、X 全体の関手自然同型ではない。 -/
def commonLoopSquareFunctorIso (X : OmegaSpectrum.{u}) :
    FunctorIso (commonLoopSquare X).square (BasedLoop.square (tail X)).square := by
  have e := VertexIso.map ((commonLoopConeIso X).symm.trans (loopSourceConeIso X))
    (sliceSquareDiagramMap (BasedLoop.diagram (tail X)))
  rw [sliceSquareDiagramMap_vertex, sliceSquareDiagramMap_vertex] at e
  exact e

/-- 実四角形の右辺は元の厳密 tail の path 終点射。 -/
lemma commonLoopSquare_right (X : OmegaSpectrum.{u}) :
    squareRightEdge ≫ (commonLoopSquare X).square =
      SSet.yonedaEquiv.symm (coherentNerveEdge (basedPathProjection (tail X))).edge := by
  change squareRightEdge ≫ coneSquare (commonLoopCone X) = _
  rw [coneSquare_right, BasedLoop.diagram, edgeCospan_left]
  rfl

/-- 実四角形の上辺も元の厳密 tail への一点からの射。 -/
lemma commonLoopSquare_top (X : OmegaSpectrum.{u}) :
    squareTopEdge ≫ (commonLoopSquare X).square =
      SSet.yonedaEquiv.symm (coherentNerveEdge (fromPoint (tail X))).edge := by
  change squareTopEdge ≫ coneSquare (commonLoopCone X) = _
  rw [coneSquare_top, BasedLoop.diagram, edgeCospan_right]
  rfl


end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
