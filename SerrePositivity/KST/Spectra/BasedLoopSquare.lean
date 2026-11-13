module

public import SerrePositivity.KST.Spectra.BasedLoopCone
public import SerrePositivity.KST.Spectra.LoopConeSquareVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

/-!
概要：具体的な BF 引き戻し対象を頂点に持つ、元の Sp の loop 四角形。
方針：path 錐を正方形へ移し、指定した二辺から両零角と終頂点を計算する。
規約：安定性を仮定しない。使われ方：BF cotensor による loop の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop
local instance loopSquareSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance loopSquareHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 具体的な loop 四角形の右辺は元の path の終点射。 -/
lemma square_right (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone Y) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (basedPathProjection Y)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_right, diagram, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_left]
  rfl

/-- 具体的な loop 四角形の上辺は一点からの元の射。 -/
lemma square_top (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone Y) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fromPoint Y)).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_top, diagram, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_right]
  rfl

/-- 元の Sp の loop 四角形。頂点は段ごとの具体的な BF 引き戻し。 -/
def square (Y : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) := by
  have ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone Y)) 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target, square_right, Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (basedPathProjection Y)).tgt_eq
  have h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone Y)) 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (basedPath Y) := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source, square_right, Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (basedPathProjection Y)).src_eq
  have h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone Y)) 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source, square_top, Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fromPoint Y)).src_eq
  exact {
    square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone Y)
    zero_corner := h₁.symm ▸ pointZeroVertex.isZero
    target_eq := ht
    other_zero := h₀.symm ▸ basedPath_isZeroVertex Y
    isPullback := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (cone_isLimit Y) }

/-- loop 四角形の頂点は具体的な BF 引き戻しの標準頂点に等しい。 -/
lemma square_vertex (Y : OmegaSpectrum.{u}) :
    (square Y).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (obj Y) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (cone Y)) 0 0 = _
  rw [coneSquare_vertex, cone_vertex]

end SerrePositivity.KST.Spectra.OmegaSpectrum.BasedLoop
