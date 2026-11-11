module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexSourceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexTargetRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexSegalComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiniteEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OriginalHomCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：二単体上の同じ元の分類 Hom 作用の同値性と分類主写像の同値を閉じる。
方針：元の source・target Segal 制限の同値性と同じ比較同型から元の作用へ戻す。
規約：元の全 cocartesian fibration・全相対 Hom・分類主写像を保持する。
使われ方：同じ元の分類作用の全単体・有限セル・骨格による降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の全相対 Hom の core を使う、二単体上の同じ分類 Hom 作用は同値。 -/
lemma cocartesianStraighteningHomInterval_twoSimplex_isQCatEquivalence
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q) := by
  have hS := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSourceRestrictionMap_id_isQCatEquivalence p q
  have hP := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexStrictPullbackMap_isQCatEquivalence (𝟭 _) p q
  have hT := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetRestrictionMap_id_isQCatEquivalence p q
  exact hT.cancel_right ((hS.comp hP).ofFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexSegalComparisonIso (𝟭 _) p q))

/-- 二単体上の同じ元の分類主写像は、追加仮定なしに充満忠実。 -/
lemma cocartesianStraighteningCoherentMap_twoSimplex_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap (ULift.{u} (Fin 3))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_isFullyFaithful_of_originalHomInterval _
    cocartesianStraighteningHomInterval_twoSimplex_isQCatEquivalence

/-- 二単体上の同じ元の分類主写像は quasicategory の同値。 -/
lemma cocartesianStraighteningCoherentMap_twoSimplex_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap (ULift.{u} (Fin 3))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    cocartesianStraighteningCoherentMap_twoSimplex_isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_isEssentiallySurjective_finite 2)

/-- 元の全相対 Hom と構成済みの分類主写像を保つ、二単体上の分類同値。 -/
def cocartesianTwoSimplexStraighteningEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve (ULift.{u} (Fin 3))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 3))))) :=
  cocartesianStraighteningCoherentMap_twoSimplex_isQCatEquivalence.choose

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
