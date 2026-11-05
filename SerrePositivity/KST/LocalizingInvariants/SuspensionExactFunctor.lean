module
public import SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExactFunctor

public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationExact
public import SerrePositivity.InfinityCategories.Core.ZeroTargetArrows
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

instance arrow_isExact : IsExactFunctor (arrow X) := by
  have : IsExactFunctor (arrow X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.SuspensionExact.arrow_source]
    infer_instance
  have : IsExactFunctor (arrow X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
    isExact_of_zero_values _ (arrow_zero_target X)
  exact arrow_exact_of_endpoints X _

instance map_isExact : IsExactFunctor (map X) := by
  have : IsExactFunctor (CofiberFamily.cofiber X (𝟙 _)) :=
    CofiberFamily.cofiber_isExact X (𝟙 _)
  change IsExactFunctor (arrow X ≫ CofiberFamily.cofiber X (𝟙 _))
  infer_instance

def exactMap (A : StableCategory.{u}) : ExactMap A A := ⟨map A.obj, inferInstance⟩

end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
