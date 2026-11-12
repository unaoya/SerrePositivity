module

public import SerrePositivity.KST.Spectra.SpectrumCirclePointLoopComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection

/-!
概要：円評価錐の極限性を、その実際の錐の射から得た BF 比較辺の可逆性で検出する。
方針：slice 射影の右 fibration による可逆性の反映と、参照極限錐の同型不変性を使う。
規約：比較射は既に固定したもの。使われ方：普遍評価から具体的な比較射の可逆性を証明する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circlePointLoopCriterionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

private lemma invertible_ofEq_iff {X : SSet.{u + 1}} {x y x' y' : X _⦋0⦌}
    (e : X.Edge x y) (hx : x = x') (hy : y = y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.ofEq hx hy) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  subst x'
  subst y'
  rfl

/-- 厳密な BF 端点への表示変更は、同じ比較辺の可逆性を保つ。 -/
lemma circlePointLoopComparisonBFEdge_invertible_iff (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (circlePointLoopComparisonBFEdge z) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (circlePointLoopComparisonEdge z) :=
  invertible_ofEq_iff _ _ _

/-- 円評価錐が極限錐であることは、その実際の比較辺が Sp で可逆であることと同値。 -/
lemma nativeCirclePointLoopCone_isLimit_iff_comparison (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (nativeCirclePointLoopCone z) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circlePointLoopComparison z)) := by
  constructor
  · intro hc
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (circlePointLoopConeComparison z).toTruncated :=
      isIso_of_isTerminal hc.isTerminalHo
        (pointLoopReferenceCone_isLimit
          (nativeCotensorInput PointedSimplicialSet.circle z).val).isTerminalHo _
    have hp := he.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (circlePointLoopComparisonEdge z) at hp
    rw [circlePointLoopComparison_edge]
    exact (circlePointLoopComparisonBFEdge_invertible_iff z).2 hp
  · intro he
    rw [circlePointLoopComparison_edge] at he
    have hp := (circlePointLoopComparisonBFEdge_invertible_iff z).1 he
    have comparisonInvertible :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
          (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val))
        (circlePointLoopConeComparison z).toTruncated hp
    exact (pointLoopReferenceCone_isLimit
      (nativeCotensorInput PointedSimplicialSet.circle z).val).of_vertexIso
        (asIso (SSet.Truncated.HomotopyCategory.homMk
          (circlePointLoopConeComparison z).toTruncated)).symm

/-- 元の円評価四角形の極限性も、同じ実際の BF 比較辺の可逆性と同値。 -/
lemma nativeCircleEvaluationSquare_isPullback_iff_comparison (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (nativeCircleEvaluationSquare z) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circlePointLoopComparison z)) := by
  have castInvariant {K X : SSet.{u + 1}} {p q : K ⟶ X}
      (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.cast h) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
    cases h
    rfl
  have h := castInvariant (nativeCircleEvaluationSquare_cospan z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (nativeCircleEvaluationSquare z))
  exact h.symm.trans (nativeCirclePointLoopCone_isLimit_iff_comparison z)

end SerrePositivity.KST.Spectra.OmegaSpectrum
