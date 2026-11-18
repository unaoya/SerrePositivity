module

public import SerrePositivity.EInfinity.BarrattEccles.FreeDerivedHomSpan

/-!
# 実自由 Hom と同じ D(R) Hom の接合 span の三つの弱射

概要：元の標準射・同じ中間項からの共通射・D(R) への射は実ホモトピー同値。
方針：同じ標的置換、元の実 DK 同型と各実比較のホモトピー逆を合成する。
規約：任意の新しい写像空間同値で接合の射を代用しない。
使われ方：標準自由単位の実三角形の弱同値検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma freeDerivedHomToCommonSmall_homotopyEquivalence (X : Complex A) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (freeDerivedHomToCommonSmall A X B) := by
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom_kanComplex A (Opposite.op X)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val
  have := _root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom_kanComplex A (Opposite.op X) B.carrier
  have := freeNormalizedHomMiddle_kanComplex A (Opposite.op X) B
  have h₁ := _root_.SerrePositivity.ComplexLimits.normalizedProbeTargetReplacementMap_homotopyEquivalence A X B.carrier
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_iso_hom
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeHomDoldKanIso A X B.carrier)
  have h₃ := freeNormalizedHomFromDoldKan_homotopyEquivalence A (Opposite.op X) B
  exact h₁.comp (h₂.comp h₃)

lemma freeDerivedHomToCommon_homotopyEquivalence (X : Complex A) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (freeDerivedHomToCommon A X B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    (freeDerivedHomToCommonSmall_homotopyEquivalence A X B)

lemma freeDerivedHomFromStandard_homotopyEquivalence (X : Complex A) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (freeDerivedHomFromStandard A X B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence
    (freeNormalizedHomFromStandard_homotopyEquivalence A (Opposite.op X) B)

lemma freeDerivedHomToUnderlying_homotopyEquivalence (X : Complex A) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (freeDerivedHomToUnderlying A X B) :=
  _root_.SerrePositivity.ComplexLimits.normalizedOrdinaryDerivedHomMap_homotopyEquivalence A X B.carrier

end SerrePositivity.EInfinity.BarrattEccles
