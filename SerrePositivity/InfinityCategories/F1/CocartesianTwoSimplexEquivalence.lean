module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexSourceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexTargetRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexSegalComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianFiniteEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalHomCriterion
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：二単体上の同じ元の分類 Hom 作用の同値性と分類主写像の同値を閉じる。
方針：元の source・target Segal 制限の同値性と同じ比較同型から元の作用へ戻す。
規約：元の全 cocartesian fibration・全相対 Hom・分類主写像を保持する。
使われ方：同じ元の分類作用の全単体・有限セル・骨格による降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全相対 Hom の core を使う、二単体上の同じ分類 Hom 作用は同値。 -/
lemma cocartesianStraighteningHomInterval_twoSimplex_isQCatEquivalence
    (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3)))) :
    IsQCatEquivalence (cocartesianStraighteningHomInterval p q) := by
  have hS := cocartesianTwoSimplexSourceRestrictionMap_id_isQCatEquivalence p q
  have hP := cocartesianTwoSimplexStrictPullbackMap_isQCatEquivalence (𝟭 _) p q
  have hT := cocartesianTwoSimplexTargetRestrictionMap_id_isQCatEquivalence p q
  exact hT.cancel_right ((hS.comp hP).ofFunctorIso
    (cocartesianTwoSimplexSegalComparisonIso (𝟭 _) p q))

/-- 二単体上の同じ元の分類主写像は、追加仮定なしに充満忠実。 -/
lemma cocartesianStraighteningCoherentMap_twoSimplex_isFullyFaithful :
    IsFullyFaithful (cocartesianStraighteningCoherentMap (ULift.{u} (Fin 3))) :=
  cocartesianStraighteningCoherentMap_isFullyFaithful_of_originalHomInterval _
    cocartesianStraighteningHomInterval_twoSimplex_isQCatEquivalence

/-- 二単体上の同じ元の分類主写像は quasicategory の同値。 -/
lemma cocartesianStraighteningCoherentMap_twoSimplex_isQCatEquivalence :
    IsQCatEquivalence (cocartesianStraighteningCoherentMap (ULift.{u} (Fin 3))) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    cocartesianStraighteningCoherentMap_twoSimplex_isFullyFaithful
    (cocartesianStraighteningCoherentMap_isEssentiallySurjective_finite 2)

/-- 元の全相対 Hom と構成済みの分類主写像を保つ、二単体上の分類同値。 -/
def cocartesianTwoSimplexStraighteningEquivalence :
    QCatEquivalence (CocartesianFibrationInfinity (nerve (ULift.{u} (Fin 3))))
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 3))))) :=
  cocartesianStraighteningCoherentMap_twoSimplex_isQCatEquivalence.choose

end SerrePositivity.InfinityCategories
