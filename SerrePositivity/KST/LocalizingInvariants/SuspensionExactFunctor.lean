module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactFunctor

public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationExact
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTargetArrows
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：安定な入力圏の suspension を全単体上の完全関手として選ぶ。
方針：零終点矢印の始点評価の切断と、普遍 cofiber 関手を合成する。
規約：値域 Sp の安定性は使わない。使われ方：差の C 側の shift の明示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

instance arrow_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow_source]
    infer_instance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
    isExact_of_zero_values _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow_zero_target X)
  exact arrow_exact_of_endpoints X _

instance map_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 _)) :=
    CofiberFamily.cofiber_isExact X (𝟙 _)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrow X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 _))
  infer_instance

def exactMap (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A A := ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map A.obj, inferInstance⟩

end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
