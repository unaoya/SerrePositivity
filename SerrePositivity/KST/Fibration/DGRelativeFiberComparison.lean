module
public import SerrePositivity.KST.Fibration.DGRelativeZeroPreservation
public import SerrePositivity.KST.Spectra.SpectrumFiberSquares
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NativeConeComparisonTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibrationInvertibleReflection

/-! # 元の相対 K 四角形から、同じ cospan の実 fiber への比較

元の零角と右辺を保つ。比較辺の可逆性と元の四角形の引き戻し性を同値にする。
可逆性自体は未証明で、K の局所化性を入力しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A] (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A))

/-- 元の K 四角形の右辺と上辺をそのまま底とする、Sp の構成済み極限錐。 -/
def dgRelativeKLimitCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (d.square ≫ dgKInputK A)) :=
  OmegaSpectrum.CoherentPullback.infinityCone _

theorem dgRelativeKLimitCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (dgRelativeKLimitCone A d) :=
  OmegaSpectrum.CoherentPullback.infinityCone_isLimit _

/-- 元の零角と右辺を変えず、左下の頂点を実 fiber に置き換えた四角形。 -/
def dgRelativeCanonicalFiberSquare : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (d.square ≫ dgKInputK A)) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgRelativeKLimitCone A d)
  zero_corner := by
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgRelativeKLimitCone A d) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (d.square ≫ dgKInputK A) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_top]
      exact congrArg (fun q => q ≫ (d.square ≫ dgKInputK A))
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge
    have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (dgRelativeKLimitCone A d)) 0 1 =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ dgKInputK A) 0 1 := by
      rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source, ht, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source]
    rw [hz]
    exact dgRelativeK_zero_corner A d
  right_edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_right]
    change horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (d.square ≫ dgKInputK A) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (d.square ≫ dgKInputK A))).symm
  isPullback := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (dgRelativeKLimitCone_isLimit A d)

/-- 比較元は元の K 四角形の全錐、比較先は同じ cospan の実極限錐。 -/
def dgRelativeFiberConeComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (d.square ≫ dgKInputK A))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (d.square ≫ dgKInputK A)) (dgRelativeKLimitCone A d) :=
  Classical.choice ((dgRelativeKLimitCone_isLimit A d).nonempty_edge _)

/-- 全錐の同じ比較を頂点へ射影した、元の K 頂点から実 fiber への辺。 -/
def dgRelativeFiberComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (d.square ≫ dgKInputK A)).vertex (dgRelativeKLimitCone A d).vertex :=
  (dgRelativeFiberConeComparison A d).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _))

/-- 同じ比較辺と、比較元・比較先の各元の脚の実合成三角形。 -/
def dgRelativeFiberComparisonLegTriangle
    (k : (horn 2 2 : SSet.{max (u + 1) v + 1}) _⦋0⦌) :
    SSet.Truncated.Edge.CompStruct (dgRelativeFiberComparison A d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (dgRelativeKLimitCone A d) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (d.square ≫ dgKInputK A)) k) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeComparisonLegTriangle (dgRelativeFiberConeComparison A d) k

/-- 元の相対 K 四角形が引き戻しとなる必要十分条件は、同じ実比較辺の可逆性。 -/
theorem dgRelativeK_isPullback_iff_fiberComparison_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ dgKInputK A) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Sp.{max (u + 1) v}) (dgRelativeFiberComparison A d) := by
  constructor
  · intro h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgRelativeFiberConeComparison A d)) :=
      isIso_of_isTerminal h.isTerminalHo (dgRelativeKLimitCone_isLimit A d).isTerminalHo _
    change IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (dgRelativeFiberConeComparison A d)))
    infer_instance
  · intro h
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (d.square ≫ dgKInputK A))) (dgRelativeFiberConeComparison A d) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibration_reflects_isInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)
        (SSet.Edge.ofTruncated (dgRelativeFiberConeComparison A d)) h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgRelativeFiberConeComparison A d)) := he
    exact (dgRelativeKLimitCone_isLimit A d).of_vertexIso
      (asIso (Truncated.HomotopyCategory.homMk (dgRelativeFiberConeComparison A d))).symm

end SerrePositivity.KST.Fibration
