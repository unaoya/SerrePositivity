module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentitySquareComparison
public import SerrePositivity.KST.SConstruction.StableZeroSquareShortRecovery
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

/-!
概要：恒等実右面の同じ Cat^perf 全比較から指定元包含・商・零左辺を厳密に回収する。
方針：元側面比較を正規化し、包含後の同じ全比較の制限を充満忠実性で反映する。
規約：元指定同型そのものを保持。使われ方：実右面の指定三境界付き全認証。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：元対角指定全比較を元実・絶対下辺で表示する。
方針：元四辺等号で端点表示のみ合わせる。規約：元全比較の値を保持。
使われ方：全右面の指定包含境界。 -/
def bottomComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (diagonalArrowComparison R d v)
    (dgOdotMilnorIdentityNullSquare_perfect_diagonal R d).symm
    (PerfectVerdierSequence.presentation_bottom (perfectIdentityLaxSequence (Q) (hQ))).symm

/-- 概要：元差指定全比較を元実・絶対右辺で表示する。
方針：元四辺等号で端点表示のみ合わせる。規約：元全比較の値を保持。
使われ方：全右面の指定商境界。 -/
def rightComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (differenceArrowComparison R d v)
    (dgOdotMilnorIdentityNullSquare_perfect_difference R d).symm (by
      rw [PerfectVerdierSequence.presentation_right, perfectIdentityLaxSequence_projection]
      rfl)

/-- 概要：元零左辺指定全比較を元実・絶対左辺で表示する。
方針：元四辺等号で端点表示のみ合わせる。規約：元全比較の値を保持。
使われ方：全右面の指定零角境界。 -/
def leftComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (zeroLeftArrowComparison R d)
    (dgOdotMilnorIdentityNullSquare_perfect_left R d).symm
    (dgOdotMilnorIdentityAbsoluteSquare_left R d).symm

/-- 概要：元包含指定全比較は元実側面ホモトピーの射の類。
方針：同じ元対角証人と端点表示の回収を使う。
規約：元全比較の値を保持。使われ方：包含後の元側面照合。 -/
lemma bottomComparison_class : (bottomComparison R d v).hom =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (bottomHomotopy R d v)) :=
  specifiedHomotopyEndpointIso (diagonalWitness R d v).homotopy (diagonalArrowComparison R d v)
    rfl _ _ (bottomHomotopy R d v) rfl

/-- 概要：元商指定全比較は元実側面ホモトピーの射の類。
方針：同じ元差証人と端点表示の回収を使う。
規約：元全比較の値を保持。使われ方：商側面の包含後照合。 -/
lemma rightComparison_class : (rightComparison R d v).hom =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (rightHomotopy R d v)) :=
  specifiedHomotopyEndpointIso (differenceWitness R d v).homotopy (differenceArrowComparison R d v)
    rfl _ _ (rightHomotopy R d v) rfl

/-- 概要：元零左辺指定全比較は元実側面ホモトピーの射の類。
方針：同じ元零左辺証人と端点表示の回収を使う。
規約：元全比較の値を保持。使われ方：零角側面の包含後照合。 -/
lemma leftComparison_class : (leftComparison R d).hom =
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (leftHomotopy R d)) :=
  specifiedHomotopyEndpointIso (zeroLeftWitness R d).homotopy (zeroLeftArrowComparison R d)
    rfl _ _ (leftHomotopy R d) rfl

/-- 概要：元全 Cat^perf 右面比較の下辺制限は元指定包含比較そのもの。
方針：同じ元全比較と指定側面の包含像の一致を充満忠実性で反映する。
規約：元全同型の値を保持。使われ方：Sp の包含境界等号。 -/
lemma perfectSquareComparison_bottom :
    (perfectSquareComparison R d v).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge = bottomComparison R d v := by
  apply perfectStableInfinityInclusion_isFullyFaithful.postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  have hr := perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso_postcomp
    (rawSquareComparison R d v)
  change (perfectSquareComparison R d v).postcomp perfectStableInfinityInclusion = _ at hr
  rw [hr]
  apply stableZeroSquareComparison_bottom
  exact specifiedHomotopyPostcomp_class (bottomHomotopy R d v) (bottomComparison R d v)
    (bottomComparison_class R d v) perfectStableInfinityInclusion

/-- 概要：元全 Cat^perf 右面比較の右辺制限は元指定商比較そのもの。
方針：同じ元全比較と指定側面の包含像の一致を充満忠実性で反映する。
規約：元全同型の値を保持。使われ方：Sp の商境界等号。 -/
lemma perfectSquareComparison_right :
    (perfectSquareComparison R d v).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge = rightComparison R d v := by
  apply perfectStableInfinityInclusion_isFullyFaithful.postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  have hr := perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso_postcomp
    (rawSquareComparison R d v)
  change (perfectSquareComparison R d v).postcomp perfectStableInfinityInclusion = _ at hr
  rw [hr]
  apply stableZeroSquareComparison_right
  exact specifiedHomotopyPostcomp_class (rightHomotopy R d v) (rightComparison R d v)
    (rightComparison_class R d v) perfectStableInfinityInclusion

/-- 概要：元全 Cat^perf 右面比較の左辺制限は元指定零左側面比較そのもの。
方針：同じ元全比較と指定側面の包含像の一致を充満忠実性で反映する。
規約：元全同型の値を保持。使われ方：Sp の零角境界への接続。 -/
lemma perfectSquareComparison_left :
    (perfectSquareComparison R d v).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge = leftComparison R d := by
  apply perfectStableInfinityInclusion_isFullyFaithful.postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  have hr := perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso_postcomp
    (rawSquareComparison R d v)
  change (perfectSquareComparison R d v).postcomp perfectStableInfinityInclusion = _ at hr
  rw [hr]
  apply stableZeroSquareComparison_left
  exact specifiedHomotopyPostcomp_class (leftHomotopy R d) (leftComparison R d)
    (leftComparison_class R d) perfectStableInfinityInclusion
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
