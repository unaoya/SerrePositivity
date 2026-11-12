module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornComparison

/-!
概要：Core の型付き cocartesian 輸送から F1 の cocartesian fibration 性を得る。
方針：区間の射を型付き辺に直し、持ち上げの端点と射影を Yoneda 対応で戻す。
規約：循環する instance を導入せず明示的な補題にする。
使われ方：既存の comma の反転した輸送を Kan 拡張の入力へ渡す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：型付き辺の cocartesian 輸送を持つ射は F1 の cocartesian fibration。
方針：始点指定の区間の辺の持ち上げを型付き輸送から構成する。
規約：始域と標的の quasicategory 性は不要。
使われ方：Core と F1 の cocartesian fibration の界面の逆方向。 -/
lemma cocartesianHornFibration_toCocartesianFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x b hb
    have hs : B.δ 1 (SSet.yonedaEquiv b) = p.app (Opposite.op ⦋0⦌) x := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, hb, Equiv.apply_symm_apply]
    let a : SSet.Truncated.Edge (X := (truncation 2).obj B)
        (p.app (Opposite.op ⦋0⦌) x) (B.δ 0 (SSet.yonedaEquiv b)) :=
      ⟨SSet.yonedaEquiv b, hs, rfl⟩
    obtain ⟨y, e, he, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration.exists_lift (p := p) x _ a
    refine ⟨SSet.yonedaEquiv.symm e.edge, ?_, ?_, ?_⟩
    · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm e.src_eq
    · apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact he
    · simpa only [Equiv.apply_symm_apply] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_hasCocartesianHornLifting p e).2 hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
