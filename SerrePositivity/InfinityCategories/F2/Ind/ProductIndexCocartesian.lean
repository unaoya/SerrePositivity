module

public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianProductProjection
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinBaseInnerFibration

/-!
概要：固定した ∞ 圏パラメータを持つ積の添字射影は cocartesian fibration。
方針：第一因子を定値にした辺を持ち上げ、可逆な第一成分の既存の判定を適用する。
規約：第二因子の充填性は不要。追加の同値性仮定を置かない。
使われ方：積上の left fibration の大域 scaffold 比較を添字上で検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- ∞ 圏を第一因子に持つ積の第二射影は cocartesian fibration。 -/
instance productIndex_cocartesianFibration (B D : SSet.{u}) [Quasicategory B] :
    CocartesianFibration (snd B D) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x e he
    refine ⟨lift (SSet.const x.1) e, ?_, lift_snd _ _, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, SSet.comp_const, SSet.yonedaEquiv_symm_comp]
        exact (SSet.yonedaEquiv_symm_zero x.1).symm
      · rw [Category.assoc, lift_snd, he, SSet.yonedaEquiv_symm_comp]
    · apply SerrePositivity.InfinityCategories.F1B.isCocartesianEdge_productSnd_of_invertible
      change IsInvertibleEdge (edgeOfSimplex (PinchedHom.constant x.1 1))
      exact SerrePositivity.InfinityCategories.F1B.constantEdge_isInvertible x.1

end SerrePositivity.InfinityCategories.F2.Ind
