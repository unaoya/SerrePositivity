module

public import SerrePositivity.InfinityCategories.F1.CocartesianSingletonFullyFaithful
public import SerrePositivity.InfinityCategories.F1.CocartesianFiniteEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalHomCriterion
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostEquivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：零次元セル上で、元の Cat∞ 値分類写像の同値と同じ Hom 作用の同値を閉じる。
方針：一点の底での充満忠実性と既存の本質的全射性を F0 で合わせる。
規約：順方向は構成済みの同じ全 cocartesian fibration の分類主写像。
使われ方：同じ Hom 比較の有限セルと骨格による帰納の出発点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 零次元の通常の単体圏上の元の分類主写像は、追加仮定なしに充満忠実。 -/
lemma cocartesianStraighteningCoherentMap_zeroSimplex_isFullyFaithful :
    IsFullyFaithful (cocartesianStraighteningCoherentMap (ULift.{u} (Fin 1))) :=
  cocartesianStraighteningCoherentMap_isFullyFaithful_of_subsingleton (ULift.up (0 : Fin 1))

/-- 零次元セル上では、元の分類主写像そのものが quasicategory の同値。 -/
lemma cocartesianStraighteningCoherentMap_zeroSimplex_isQCatEquivalence :
    IsQCatEquivalence (cocartesianStraighteningCoherentMap (ULift.{u} (Fin 1))) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    cocartesianStraighteningCoherentMap_zeroSimplex_isFullyFaithful
    (cocartesianStraighteningCoherentMap_isEssentiallySurjective_finite 0)

/-- 元の全相対 Hom の core を保つ、零次元セル上の同じ分類同値のデータ。 -/
def cocartesianZeroSimplexStraighteningEquivalence :
    QCatEquivalence (CocartesianFibrationInfinity (nerve (ULift.{u} (Fin 1))))
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin 1))))) :=
  cocartesianStraighteningCoherentMap_zeroSimplex_isQCatEquivalence.choose

/-- 零次元セル上の元の Hom の区間作用そのものは、追加仮定なしに同値。 -/
lemma cocartesianStraighteningHomInterval_zeroSimplex_isQCatEquivalence
    (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 1)))) :
    IsQCatEquivalence (cocartesianStraighteningHomInterval p q) := by
  rw [cocartesianStraighteningHomInterval_factor]
  exact (coherentHomComparison_isQCatEquivalence p q).comp
    ((pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).comp
      (IsFullyFaithful.intervalMappingPostOfEq_isQCatEquivalence
        cocartesianStraighteningCoherentMap_zeroSimplex_isFullyFaithful _ _ _ _))

end SerrePositivity.InfinityCategories
