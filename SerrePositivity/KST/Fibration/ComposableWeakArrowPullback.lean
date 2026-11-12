module
public import SerrePositivity.KST.Fibration.ComposableWeakArrows
public import SerrePositivity.KST.Fibration.FullPredicatePullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-! # 接続した W 辺の元の図式圏の厳密な引き戻し表示 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 接続した二辺の最初の元の W 辺への制限。 -/
def composableWeakFirstMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (composableWeakArrowModel q).carrier ⟶ weakArrowCategory q :=
  fullPredicateMap ((pre horn₂₁.ι₀₁).app B.obj) (composableWeakArrowPredicate q).predicate
    (weakArrowPredicate q) (fun v hv => ((composableWeakArrowPredicate_iff q v).1 hv).1)

/-- 接続した二辺の次の元の W 辺への制限。 -/
def composableWeakNextMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (composableWeakArrowModel q).carrier ⟶ weakArrowCategory q :=
  fullPredicateMap ((pre horn₂₁.ι₁₂).app B.obj) (composableWeakArrowPredicate q).predicate
    (weakArrowPredicate q) (fun v hv => ((composableWeakArrowPredicate_iff q v).1 hv).2)

/-- 第一辺の包含後は、元のホーン上の第一辺への制限。 -/
lemma composableWeakFirstMap_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    composableWeakFirstMap q ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι =
      (SConstruction.closedStableInclusion (composableWeakArrowPredicate q)).val ≫
        (pre horn₂₁.ι₀₁).app B.obj := rfl

/-- 次の辺の包含後も、元のホーン上の同じ辺への制限。 -/
lemma composableWeakNextMap_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    composableWeakNextMap q ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι =
      (SConstruction.closedStableInclusion (composableWeakArrowPredicate q)).val ≫
        (pre horn₂₁.ι₁₂).app B.obj := rfl

/-- 二つの W 辺図式圏を、元の共有端点の図式上で貼り合わせた引き戻し。 -/
theorem composableWeakArrow_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsPullback (composableWeakFirstMap q) (composableWeakNextMap q)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι ≫
        (pre (stdSimplex.δ (0 : Fin 2))).app B.obj)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι ≫
        (pre (stdSimplex.δ (1 : Fin 2))).app B.obj) :=
  isPullback_fullPredicates (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout horn₂₁.isPushout B.obj).flip
    (composableWeakArrowPredicate q).predicate (weakArrowPredicate q) (weakArrowPredicate q)
    (composableWeakArrowPredicate_iff q)

end SerrePositivity.KST.Fibration
