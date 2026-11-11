module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalHomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportDiagramHomCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiniteEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OriginalHomCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：一次元セル上の元の Cat∞ 値分類主写像と元の全 Hom 作用の同値を閉じる。
方針：同じ輸送図式の区間作用を既存の厳密な因子分解へ戻し、本質的全射性と合わせる。
規約：構成済みの同じ分類主写像を使い、単位・余単位の構成を追加しない。
使われ方：同じ分類 Hom 作用の有限セル・骨格による降下。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 一次元セル上の元の分類主写像は、追加仮定なしに充満忠実。 -/
lemma cocartesianStraighteningCoherentMap_oneSimplex_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap (ULift.{u} (Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_isFullyFaithful_of_homInterval _
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramHomInterval_isQCatEquivalence

/-- 一次元セル上の元の分類主写像そのものは quasicategory の同値。 -/
lemma cocartesianStraighteningCoherentMap_oneSimplex_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap (ULift.{u} (Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    cocartesianStraighteningCoherentMap_oneSimplex_isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningCoherentMap_isEssentiallySurjective_finite 1)

/-- 元の全相対 Hom の core を保つ、一次元セル上の同じ分類同値のデータ。 -/
def cocartesianOneSimplexStraighteningEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve (ULift.{u} (Fin 2))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 2))))) :=
  cocartesianStraighteningCoherentMap_oneSimplex_isQCatEquivalence.choose

/-- 一次元セル上の元の全 Hom の区間作用そのものは、追加仮定なしに同値。 -/
lemma cocartesianStraighteningHomInterval_oneSimplex_isQCatEquivalence
    (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve (ULift.{u} (Fin 2)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval_factor]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence p q).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsFullyFaithful.intervalMappingPostOfEq_isQCatEquivalence
        cocartesianStraighteningCoherentMap_oneSimplex_isFullyFaithful _ _ _ _))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
