module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootInitialComparisonIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TrivialFibrationIsoFaithful

/-!
概要：元の左右の初期 Hom 族を、評価上で厳密に定値な実際の円柱で結ぶ。
方針：評価の自明 Kan 性で代表を選び、h Fun の忠実性で元の三比較の合成の類を保持する。
規約：評価の全時刻固定と同じ指定した類を保持。使われ方：共通 end 内の整合性の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y
local notation "I" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootInitialComparisonIso hp p c hc dB dC y
local notation "ev" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y
local notation "z" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 同じ左右の全族を、元の共通部分の可変終点上で全時刻定値に結ぶ円柱が存在する。 -/
lemma exists_specifiedCoconeRootEvaluationHomotopy :
    ∃ H : SSet.Homotopy L R, H.h ≫ ev = fst T Δ[1] ≫ z := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_homotopy_over_trivialKanFibration ev L R
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily_evaluation hp p c hc dB dC y).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily_evaluation hp p c hc dB dC y).symm)
  refine ⟨H, ?_⟩
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily_evaluation] using hH

/-- 元の左右の全初期 Hom 族を、評価上で厳密に定値な実際の円柱で結ぶ。 -/
def specifiedCoconeRootEvaluationHomotopy : SSet.Homotopy L R :=
  (exists_specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y).choose

/-- 同じ可変終点の全族を、円柱の全時刻で厳密に保持する。 -/
lemma specifiedCoconeRootEvaluationHomotopy_evaluation :
    (specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y).h ≫ ev = fst T Δ[1] ≫ z :=
  (exists_specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y).choose_spec

/-- この厳密な評価固定代表の類は、元の三比較の合成同型の同じ射である。 -/
lemma specifiedCoconeRootEvaluationHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y)) = (I).hom := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.trivialKanFibration_postcomp_iso_hom_injective ev
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y)) I
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyIso_postcomp_constant_arrow
    (specifiedCoconeRootEvaluationHomotopy hp p c hc dB dC y) ev z
    (specifiedCoconeRootEvaluationHomotopy_evaluation hp p c hc dB dC y)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootInitialComparisonIso_evaluation_hom_arrow hp p c hc dB dC y).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
