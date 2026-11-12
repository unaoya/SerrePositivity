module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantHomFaithful

/-!
概要：一点上の関手圏と元の単体集合を定値関手と評価で同型にする。
方針：一点の自己射の一意性と定値関手の評価公式を使う。
規約：quasicategory 性を要求しない。
使われ方：余錐右頂点の Hom と元の標的の Hom の照合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：一点の定値関手と指定頂点での評価は厳密な逆同型。
方針：評価後の定値化を一点の恒等前合成へ同定する。
規約：元の一点と元の全関手圏を使う。
使われ方：余極限単位の Hom 普遍性。 -/
def constantPointFunctorIso (X : SSet.{u}) : X ≅ (ihom (Δ[0] : SSet.{u})).obj X where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap Δ[0] X
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  hom_inv_id := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorMap_evaluate _
  inv_hom_id := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_constantFunctorMap]
    have h : (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) : Δ[0] ⟶ Δ[0]) =
        𝟙 Δ[0] := stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, pre_id]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
