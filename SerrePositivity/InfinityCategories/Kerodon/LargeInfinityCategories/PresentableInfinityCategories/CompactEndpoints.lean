module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ObjectCompactCardinals

/-!
概要：小さい生成辺族の両端点に共通の正則 compact 濃度を選ぶ。
方針：二つの端点を一つの小さい族にまとめ、既存の共通濃度定理を使う。
規約：指定した全生成辺の両端点を保持し、局所置換の存在は主張しない。
使われ方：P-1 f2 の濃度評価の準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 小さい生成辺の始点・終点は、一つの正則濃度に関して全て compact。 -/
lemma exists_regular_compactEndpoints {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {I : Type u} (edges : I → C _⦋1⦌)
    (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C.δ 1 (edges i)) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C.δ 0 (edges i)) := by
  let endpoints : I × Bool → C _⦋0⦌ :=
    fun p ↦ if p.2 then C.δ 1 (edges p.1) else C.δ 0 (edges p.1)
  obtain ⟨μ, hμ, hσ, hends⟩ := hC.isAccessible.exists_common_compactCardinal endpoints σ
  exact ⟨μ, hμ, hσ, fun i ↦ ⟨hends (i, true), hends (i, false)⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
