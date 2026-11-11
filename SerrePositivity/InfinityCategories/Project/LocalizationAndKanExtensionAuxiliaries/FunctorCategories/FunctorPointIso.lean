module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantHomFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：標準零単体上の関手を同じ標的へ評価する実同型。
方針：評価と定値関手の合成を、一点上の恒等射への前合成として計算する。
規約：quasicategory 性は不要。元の全単体を保つ同型。
使われ方：右端への全関手制限から同じ頂点での評価へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 一点上の関手の評価と定値関手は、元の全単体を保つ逆同型。 -/
def functorPointIso (X : SSet.{u}) : (ihom (Δ[0] : SSet.{u})).obj X ≅ X where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap Δ[0] X
  hom_inv_id := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_constantFunctorMap]
    have h : (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) : Δ[0] ⟶ Δ[0]) =
        𝟙 _ := stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, pre_id]
    rfl
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorMap_evaluate _

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
