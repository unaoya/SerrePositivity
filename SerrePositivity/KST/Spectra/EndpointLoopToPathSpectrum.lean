module

public import SerrePositivity.KST.Spectra.BasedPathSpectrum
public import SerrePositivity.KST.Spectra.BasedPathLoopRestriction
public import SerrePositivity.KST.Spectra.SpectrumZeroMaps
public import SerrePositivity.KST.Spectra.CotensorRestriction

/-!
概要：二端点を潰した円の BF cotensor から BF path 模型への制限と、その厳密な零合成。
方針：BF 置換射影への比較式と元の path 終点の零合成を各段で合わせる。
規約：厳密な BF 射の零合成。使われ方：native な loop 引き戻しへの普遍射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 二端点を潰した円の BF cotensor から BF path 模型への実際の制限。 -/
def endpointLoopToPath (Y : OmegaSpectrum.{u}) : cotensor endpointCircle Y ⟶ basedPath Y :=
  cotensorPre (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y

/-- 元の path の列へ射影したときの厳密な比較式。 -/
lemma endpointLoopToPath_comparison (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (endpointLoopToPath Y).app n ≫ (cotensorProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).app n =
      (cotensorProjection endpointCircle Y).app n ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u})
          (Y.level n).space := cotensorPre_comparison _ _ _

/-- BF path 終点への合成は厳密に零となる。 -/
lemma endpointLoopToPath_projection_zero (Y : OmegaSpectrum.{u}) :
    endpointLoopToPath Y ≫ basedPathProjection Y = 0 := by
  apply OmegaSpectrum.Hom.ext
  intro n
  change (endpointLoopToPath Y).app n ≫ (basedPathProjection Y).app n = _
  rw [basedPathProjection_app, ← Category.assoc, endpointLoopToPath_comparison,
    Category.assoc, endpointLoop_pathEndpoint_zero, comp_zero, zero_app]

end SerrePositivity.KST.Spectra.OmegaSpectrum
