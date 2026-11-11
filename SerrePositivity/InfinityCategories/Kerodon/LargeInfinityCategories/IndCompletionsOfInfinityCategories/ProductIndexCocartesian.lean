module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianProductProjection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinBaseInnerFibration

/-!
概要：固定した ∞ 圏パラメータを持つ積の添字射影は cocartesian fibration。
方針：第一因子を定値にした辺を持ち上げ、可逆な第一成分の既存の判定を適用する。
規約：第二因子の充填性は不要。追加の同値性仮定を置かない。
使われ方：積上の left fibration の大域 scaffold 比較を添字上で検出する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- ∞ 圏を第一因子に持つ積の第二射影は cocartesian fibration。 -/
instance productIndex_cocartesianFibration (B D : SSet.{u}) [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (snd B D) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x e he
    refine ⟨lift (SSet.const x.1) e, ?_, lift_snd _ _, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, SSet.comp_const, SSet.yonedaEquiv_symm_comp]
        exact (SSet.yonedaEquiv_symm_zero x.1).symm
      · rw [Category.assoc, lift_snd, he, SSet.yonedaEquiv_symm_comp]
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_productSnd_of_invertible
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x.1 1))
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantEdge_isInvertible x.1

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
