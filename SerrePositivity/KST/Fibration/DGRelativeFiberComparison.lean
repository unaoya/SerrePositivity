module
public import SerrePositivity.KST.Fibration.DGRelativeZeroPreservation
public import SerrePositivity.KST.Spectra.SpectrumFiberSquares
public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeConeComparisonTriangles
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationInvertibleReflection

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
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A] (d : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A))

/-- 元の K 四角形の右辺と上辺をそのまま底とする、Sp の構成済み極限錐。 -/
def dgRelativeKLimitCone : JoinCone (pullbackCospan (d.square ≫ dgKInputK A)) :=
  OmegaSpectrum.CoherentPullback.infinityCone _

theorem dgRelativeKLimitCone_isLimit : IsLimitCone (dgRelativeKLimitCone A d) :=
  OmegaSpectrum.CoherentPullback.infinityCone_isLimit _

/-- 元の零角と右辺を変えず、左下の頂点を実 fiber に置き換えた四角形。 -/
def dgRelativeCanonicalFiberSquare : FiberSquare
    (squareRightArrow (d.square ≫ dgKInputK A)) where
  square := coneSquare (dgRelativeKLimitCone A d)
  zero_corner := by
    have ht : squareTopEdge ≫ coneSquare (dgRelativeKLimitCone A d) =
        squareTopEdge ≫ (d.square ≫ dgKInputK A) := by
      rw [coneSquare_top]
      exact congrArg (fun q => q ≫ (d.square ≫ dgKInputK A))
        cospanSquareBoundary_topEdge
    have hz : squareVertex (coneSquare (dgRelativeKLimitCone A d)) 0 1 =
        squareVertex (d.square ≫ dgKInputK A) 0 1 := by
      rw [← squareTopEdge_source, ht, squareTopEdge_source]
    rw [hz]
    exact dgRelativeK_zero_corner A d
  right_edge := by
    rw [coneSquare_right]
    change horn₂₂.ι₀₂ ≫ pullbackCospan (d.square ≫ dgKInputK A) = _
    rw [pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge]
    rw [squareRightArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply
      (squareRightEdge ≫ (d.square ≫ dgKInputK A))).symm
  isPullback := coneSquare_isPullback _ (dgRelativeKLimitCone_isLimit A d)

/-- 比較元は元の K 四角形の全錐、比較先は同じ cospan の実極限錐。 -/
def dgRelativeFiberConeComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (d.square ≫ dgKInputK A))))
      (pullbackCone (d.square ≫ dgKInputK A)) (dgRelativeKLimitCone A d) :=
  Classical.choice ((dgRelativeKLimitCone_isLimit A d).nonempty_edge _)

/-- 全錐の同じ比較を頂点へ射影した、元の K 頂点から実 fiber への辺。 -/
def dgRelativeFiberComparison :
    SSet.Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (pullbackCone (d.square ≫ dgKInputK A)).vertex (dgRelativeKLimitCone A d).vertex :=
  (dgRelativeFiberConeComparison A d).map ((truncation 2).map (sliceOverProjection _))

/-- 同じ比較辺と、比較元・比較先の各元の脚の実合成三角形。 -/
def dgRelativeFiberComparisonLegTriangle
    (k : (horn 2 2 : SSet.{max (u + 1) v + 1}) _⦋0⦌) :
    SSet.Truncated.Edge.CompStruct (dgRelativeFiberComparison A d)
      (F2.nativeConeLeg (dgRelativeKLimitCone A d) k)
      (F2.nativeConeLeg (pullbackCone (d.square ≫ dgKInputK A)) k) :=
  nativeConeComparisonLegTriangle (dgRelativeFiberConeComparison A d) k

/-- 元の相対 K 四角形が引き戻しとなる必要十分条件は、同じ実比較辺の可逆性。 -/
theorem dgRelativeK_isPullback_iff_fiberComparison_isInvertible :
    IsPullbackSquare (d.square ≫ dgKInputK A) ↔
      IsInvertibleEdge (X := Sp.{max (u + 1) v}) (dgRelativeFiberComparison A d) := by
  constructor
  · intro h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgRelativeFiberConeComparison A d)) :=
      isIso_of_isTerminal h.isTerminalHo (dgRelativeKLimitCone_isLimit A d).isTerminalHo _
    change IsIso ((hoFunctor.map (sliceOverProjection _)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (dgRelativeFiberConeComparison A d)))
    infer_instance
  · intro h
    have he : IsInvertibleEdge (X := sliceOver
        (pullbackCospan (d.square ≫ dgKInputK A))) (dgRelativeFiberConeComparison A d) :=
      rightFibration_reflects_isInvertibleEdge (sliceOverProjection _)
        (SSet.Edge.ofTruncated (dgRelativeFiberConeComparison A d)) h
    have : IsIso (Truncated.HomotopyCategory.homMk
        (dgRelativeFiberConeComparison A d)) := he
    exact (dgRelativeKLimitCone_isLimit A d).of_vertexIso
      (asIso (Truncated.HomotopyCategory.homMk (dgRelativeFiberConeComparison A d))).symm

end SerrePositivity.KST.Fibration
