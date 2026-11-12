module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeCartesianTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

/-!
概要：通常の余錐の図式への制限を F1 の cartesian fibration の型に接続する。
方針：既存の終点指定の型付き cartesian lift を標準区間の射として読み替える。
規約：形状 K に充填性は不要。
使われ方：相対 join の関手の族の制限の fiber ごとの cartesian 性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐の関手圏から図式の関手圏への制限は cartesian fibration。
方針：型付き辺の終点指定の持ち上げの存在を fibration の辺の条件へ移す。
規約：値域 D の quasicategory 性だけを要求する。
使われ方：fiber の余錐制限の cartesian 輸送。 -/
instance coconeRestriction_cartesianFibration (K D : SSet.{u}) [Quasicategory D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x b hb
    let B := (ihom K).obj D
    have ht : B.δ 0 (SSet.yonedaEquiv b) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D).app (Opposite.op ⦋0⦌) x := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
    let a : SSet.Truncated.Edge (X := (truncation 2).obj B)
        (B.δ 1 (SSet.yonedaEquiv b)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D).app (Opposite.op ⦋0⦌) x) :=
      ⟨SSet.yonedaEquiv b, rfl, ht⟩
    obtain ⟨w, e, hp, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_cartesian_cocone_lift K D x _ a
    refine ⟨SSet.yonedaEquiv.symm e.edge, ?_, ?_, ?_⟩
    · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm e.tgt_eq
    · apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hp
    · simpa only [Equiv.apply_symm_apply] using he

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
