module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonApexEquivalence
public import SerrePositivity.KST.Spectra.SpectrumCirclePointLoopCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex

/-!
概要：元の円評価四角形は Sp の引き戻しであり、元の BF 比較射自身が可逆。
方針：元の比較の apex の可逆性を slice に反映し、元の錐と形状同型に沿って極限性を移す。
規約：元の錐全体・四角形・比較射を保持。使われ方：native loop の完全忠実性と安定性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeCirclePullbackSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance nativeCirclePullbackHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

private lemma invertible_ofEq_iff {X : SSet.{u + 1}} {x y x' y' : X _⦋0⦌}
    (e : X.Edge x y) (hx : x = x') (hy : y = y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.ofEq hx hy) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  subst x'
  subst y'
  rfl

/-- 元の評価錐から元の companion 極限錐への比較辺全体が可逆。 -/
lemma circleCompanionConeComparison_isInvertible (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)))
        (circleCompanionConeComparison z).toTruncated := by
  have h := circleCompanionConeComparisonHom_isInvertible z
  rw [circleCompanionConeComparisonHom_edge] at h
  have hp := (invertible_ofEq_iff _ _ _).1 h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)))
    (circleCompanionConeComparison z).toTruncated hp

/-- 元の評価錐全体は、元の strict cospan 図式の極限錐。 -/
lemma nativeCircleStrictCone_isLimit (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (nativeCircleStrictCone z) := by
  have comparisonInvertible := circleCompanionConeComparison_isInvertible z
  exact (circleCompanionBKCoherentCone_isLimit z).of_vertexIso
    (asIso (SSet.Truncated.HomotopyCategory.homMk
      (circleCompanionConeComparison z).toTruncated)).symm

/-- 元の固定ホーン上の円評価錐そのものが極限錐。 -/
lemma nativeCirclePointLoopCone_isLimit (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (nativeCirclePointLoopCone z) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff
    (DiagramLimitTransport.restrict (nativeCirclePointLoopCone z)
      CospanShape.strictCospanHornIso.hom)
    (pointLoopCospan_strict (nativeCotensorInput PointedSimplicialSet.circle z).val)).1
      (nativeCircleStrictCone_isLimit z)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeRestrict_isLimit_iff (nativeCirclePointLoopCone z)
    CospanShape.strictCospanHornIso.hom).2 h

/-- 元の円評価錐から既存の BF 極限への元の指定比較射自身が可逆。 -/
lemma circlePointLoopComparison_isInvertible (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circlePointLoopComparison z)) :=
  (nativeCirclePointLoopCone_isLimit_iff_comparison z).1 (nativeCirclePointLoopCone_isLimit z)

/-- 元の円の普遍評価四角形そのものが、Sp の引き戻し四角形。 -/
lemma nativeCircleEvaluationSquare_isPullback (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (nativeCircleEvaluationSquare z) :=
  (nativeCircleEvaluationSquare_isPullback_iff_comparison z).2
    (circlePointLoopComparison_isInvertible z)

end SerrePositivity.KST.Spectra.OmegaSpectrum
