module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePullbackPathLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLiftingInvertible
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativePathBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：同値を右に持ち上げる射に沿って、同じ同値写像を厳密に引き戻す。
方針：可逆辺の終点指定の持ち上げから相対 path の全境界持ち上げを得る。
規約：モデル構造の instance を仮定しない。
使われ方：実際の分類先の Hom の成分比較を同じ底へ引き戻す。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 同値を右に持ち上げる射に沿う、元の同値の厳密な引き戻しは同値。 -/
@[kerodon 01HJ]
lemma IsQCatEquivalence.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
    {E B F : SSet.{u}} [Quasicategory E] [Quasicategory B] [Quasicategory F]
    {e : E ⟶ B} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence e) (p : F ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.snd e p) := by
  letI : InnerFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration hp
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeEquivalencePathMapAt_one_trivialKanFibration p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLifting.invertibleTargetLifting hp)
  exact (he.pullback_snd_of_relativePath p).isPrecompositionEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsQCatEquivalence (pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
