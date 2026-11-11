module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EmptyCocartesianNativeHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.EmptyIntervalDiagramHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：空の部分底上で、元の native Hom の core と分類先の実際の区間 Hom は厳密に同型。
方針：両側の同じ終対象の一意な同型を使い、任意の元の作用の因子化を厳密に保つ。
規約：元の二つの射影と分類先の二図式を保持する。
使われ方：境界による Hom 比較の零次元の初期値。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
  {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)
  (a : Over B) (hA : IsInitial a.left)

/-- 空の部分底上の同じ元の native core と同じ分類先 Hom の、終対象としての同型。 -/
def emptyCocartesianHomComparisonIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q)) : SSet.{u}) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map a.hom ≫ P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map a.hom ≫ Q)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLift_isTerminal_of_isInitial p q a hA).uniqueUpToIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.intervalDiagramHom_isTerminal_of_isInitial _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.uliftSSet_isInitial_of_isInitial hA))

/-- 同じ空境界の同型を順方向とする実際の比較。 -/
def emptyCocartesianHomComparison := (emptyCocartesianHomComparisonIso p q P Q a hA).hom

/-- 元の空境界の比較自身は同型で、前合成同値でもある。 -/
lemma emptyCocartesianHomComparison_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (emptyCocartesianHomComparison p q P Q a hA) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (emptyCocartesianHomComparisonIso p q P Q a hA)

/-- 任意の元の作用からの二つの制限は、同じ空境界の比較と厳密に可換。 -/
lemma emptyCocartesianHomComparison_factorization {T : SSet.{u + 1}}
    (r : T ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q)) : SSet.{u}))
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map a.hom ≫ P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map a.hom ≫ Q))) :
    r ≫ emptyCocartesianHomComparison p q P Q a hA = t :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.intervalDiagramHom_isTerminal_of_isInitial _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.uliftSSet_isInitial_of_isInitial hA)).hom_ext _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
