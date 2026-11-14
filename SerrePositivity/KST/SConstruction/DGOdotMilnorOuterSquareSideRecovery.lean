module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterSquareComparison
public import SerrePositivity.KST.SConstruction.StableZeroSquareShortRecovery
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition

/-!
概要：元実外周の同じ Cat^perf 全比較から指定包含・商・零左側面を厳密回収する。
方針：元側面比較と全比較の包含像の一致を同じ充満忠実性で反映する。
規約：元始域の増大屋根・resolved 商・実 c と元指定同型の値を保持。
使われ方：元 LT 絶対外周から実始域外面への指定三境界付き全認証。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元外周下側面の指定全比較を元実四辺で表示する。
方針：同じ元証人を端点等号だけで正規化する。規約：元全比較の値を保持。
使われ方：元外周の指定下境界。 -/
def dgOdotMilnorOuterBottomComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((dgOdotMilnorOuterInclusionWitness R d).comparisonOfEquivalences
      (dgOdotMilnorOuterSourceValueEquivalence R d).isQCatEquivalence
      (dgOdotMilnorOuterMiddleValueEquivalence R d).isQCatEquivalence)
    (dgOdotMilnorSourceNullOuterSquare_perfect_inclusion R d).symm
    (dgOdotMilnorOuterAbsoluteSquare_inclusion R d h).symm

/-- 概要：元外周右側面の指定全比較を元実四辺で表示する。
方針：同じ元証人を端点等号だけで正規化する。規約：元全比較の値を保持。
使われ方：元外周の指定右境界。 -/
def dgOdotMilnorOuterRightComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((dgOdotMilnorOuterProjectionWitness R d h).comparisonOfEquivalences
      (dgOdotMilnorOuterMiddleValueEquivalence R d).isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl (Q).obj).isQCatEquivalence)
    (dgOdotMilnorSourceNullOuterSquare_perfect_projection R d).symm
    (dgOdotMilnorOuterAbsoluteSquare_projection R d h).symm

/-- 概要：元外周左側面の指定全比較を元実四辺で表示する。
方針：同じ元証人を端点等号だけで正規化する。規約：元全比較の値を保持。
使われ方：元外周の指定左境界。 -/
def dgOdotMilnorOuterLeftComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorSourceNullOuterSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((dgOdotMilnorOuterZeroLeftWitness R d).comparison
      (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (dgOdotMilnorOuterSourceValueEquivalence R d).isQCatEquivalence)
      (dgOdotMilnorOuterNullZeroMap_isInvertible R d))
    (dgOdotMilnorSourceNullOuterSquare_perfect_left R d).symm
    (dgOdotMilnorOuterAbsoluteSquare_left R d h).symm

/-- 概要：元外周下指定比較は元同じ側面ホモトピーの射の類。
方針：元証人と端点正規化の同じ全写像を使う。規約：元全比較を保持。
使われ方：元包含像における指定下側面の照合。 -/
lemma dgOdotMilnorOuterBottomComparison_class : (dgOdotMilnorOuterBottomComparison R d h).hom =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterBottomHomotopy R d h)) :=
  specifiedHomotopyEndpointIso (dgOdotMilnorOuterInclusionWitness R d).homotopy ((dgOdotMilnorOuterInclusionWitness R d).comparisonOfEquivalences
      (dgOdotMilnorOuterSourceValueEquivalence R d).isQCatEquivalence
      (dgOdotMilnorOuterMiddleValueEquivalence R d).isQCatEquivalence)
    rfl _ _ (dgOdotMilnorOuterBottomHomotopy R d h) rfl

/-- 概要：元外周右指定比較は元同じ側面ホモトピーの射の類。
方針：元証人と端点正規化の同じ全写像を使う。規約：元全比較を保持。
使われ方：元包含像における指定右側面の照合。 -/
lemma dgOdotMilnorOuterRightComparison_class : (dgOdotMilnorOuterRightComparison R d h).hom =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterRightHomotopy R d h)) :=
  specifiedHomotopyEndpointIso (dgOdotMilnorOuterProjectionWitness R d h).homotopy ((dgOdotMilnorOuterProjectionWitness R d h).comparisonOfEquivalences
      (dgOdotMilnorOuterMiddleValueEquivalence R d).isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl (Q).obj).isQCatEquivalence)
    rfl _ _ (dgOdotMilnorOuterRightHomotopy R d h) rfl

/-- 概要：元外周左指定比較は元同じ側面ホモトピーの射の類。
方針：元証人と端点正規化の同じ全写像を使う。規約：元全比較を保持。
使われ方：元包含像における指定左側面の照合。 -/
lemma dgOdotMilnorOuterLeftComparison_class : (dgOdotMilnorOuterLeftComparison R d h).hom =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorOuterLeftHomotopy R d h)) :=
  specifiedHomotopyEndpointIso (dgOdotMilnorOuterZeroLeftWitness R d).homotopy ((dgOdotMilnorOuterZeroLeftWitness R d).comparison
      (perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _
        (dgOdotMilnorOuterSourceValueEquivalence R d).isQCatEquivalence)
      (dgOdotMilnorOuterNullZeroMap_isInvertible R d))
    rfl _ _ (dgOdotMilnorOuterLeftHomotopy R d h) rfl

/-- 概要：元外周の全 Cat^perf 比較の下制限は元指定全比較そのもの。
方針：元全比較と指定側面の包含像の一致を充満忠実性で反映する。
規約：元全同型の値を保持。使われ方：元外周の指定下境界の等号。 -/
lemma dgOdotMilnorOuterPerfectSquareComparison_bottom :
    (dgOdotMilnorOuterPerfectSquareComparison R d h).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge =
      dgOdotMilnorOuterBottomComparison R d h := by
  apply perfectStableInfinityInclusion_isFullyFaithful.postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  have hr := perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso_postcomp
    (dgOdotMilnorOuterRawSquareComparison R d h)
  change (dgOdotMilnorOuterPerfectSquareComparison R d h).postcomp perfectStableInfinityInclusion = _ at hr
  rw [hr]
  apply stableZeroSquareComparison_bottom
  exact specifiedHomotopyPostcomp_class (dgOdotMilnorOuterBottomHomotopy R d h)
    (dgOdotMilnorOuterBottomComparison R d h) (dgOdotMilnorOuterBottomComparison_class R d h)
    perfectStableInfinityInclusion

/-- 概要：元外周の全 Cat^perf 比較の右制限は元指定全比較そのもの。
方針：元全比較と指定側面の包含像の一致を充満忠実性で反映する。
規約：元全同型の値を保持。使われ方：元外周の指定右境界の等号。 -/
lemma dgOdotMilnorOuterPerfectSquareComparison_right :
    (dgOdotMilnorOuterPerfectSquareComparison R d h).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge =
      dgOdotMilnorOuterRightComparison R d h := by
  apply perfectStableInfinityInclusion_isFullyFaithful.postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  have hr := perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso_postcomp
    (dgOdotMilnorOuterRawSquareComparison R d h)
  change (dgOdotMilnorOuterPerfectSquareComparison R d h).postcomp perfectStableInfinityInclusion = _ at hr
  rw [hr]
  apply stableZeroSquareComparison_right
  exact specifiedHomotopyPostcomp_class (dgOdotMilnorOuterRightHomotopy R d h)
    (dgOdotMilnorOuterRightComparison R d h) (dgOdotMilnorOuterRightComparison_class R d h)
    perfectStableInfinityInclusion

/-- 概要：元外周の全 Cat^perf 比較の左制限は元指定全比較そのもの。
方針：元全比較と指定側面の包含像の一致を充満忠実性で反映する。
規約：元全同型の値を保持。使われ方：元外周の指定左境界の等号。 -/
lemma dgOdotMilnorOuterPerfectSquareComparison_left :
    (dgOdotMilnorOuterPerfectSquareComparison R d h).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge =
      dgOdotMilnorOuterLeftComparison R d h := by
  apply perfectStableInfinityInclusion_isFullyFaithful.postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  have hr := perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso_postcomp
    (dgOdotMilnorOuterRawSquareComparison R d h)
  change (dgOdotMilnorOuterPerfectSquareComparison R d h).postcomp perfectStableInfinityInclusion = _ at hr
  rw [hr]
  apply stableZeroSquareComparison_left
  exact specifiedHomotopyPostcomp_class (dgOdotMilnorOuterLeftHomotopy R d h)
    (dgOdotMilnorOuterLeftComparison R d h) (dgOdotMilnorOuterLeftComparison_class R d h)
    perfectStableInfinityInclusion
end SerrePositivity.KST.SConstruction
