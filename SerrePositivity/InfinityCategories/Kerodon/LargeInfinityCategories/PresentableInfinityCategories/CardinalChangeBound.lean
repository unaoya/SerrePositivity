module

public import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas

/-!
概要：濃度変更に使う、明示的な冪の評価による濃度条件を定める。
方針：κ < μ と全 β < μ・α < κ に対する β^α < μ を使う。
規約：∞ 圏の accessibility を条件のフィールドへ仮定しない。正則性は使用時に明示する。
使われ方：HTT 5.4.2.8〜9 の小さい filtered 部分表示。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 全ての小さい冪を抑える、濃度変更の明示的な十分条件。 -/
def IsCardinalChangeBound (κ μ : Cardinal.{u}) : Prop :=
  κ < μ ∧ ∀ α β : Cardinal.{u}, α < κ → β < μ → β ^ α < μ

lemma IsCardinalChangeBound.le {κ μ : Cardinal.{u}} (h : IsCardinalChangeBound κ μ) : κ ≤ μ :=
  h.1.le

/-- 始域の濃度を下げても、同じ上限の冪の評価は保持される。 -/
lemma IsCardinalChangeBound.of_le {κ κ' μ : Cardinal.{u}}
    (h : IsCardinalChangeBound κ μ) (hκ : κ' ≤ κ) : IsCardinalChangeBound κ' μ :=
  ⟨hκ.trans_lt h.1, fun α β hα hβ ↦ h.2 α β (hα.trans_le hκ) hβ⟩

/-- 明示的な冪の評価から、添字 poset 用の既存の sharply smaller 条件を得る。 -/
lemma IsCardinalChangeBound.sharplyLT {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : IsCardinalChangeBound κ μ) :
    Cardinal.SharplyLT κ μ := Cardinal.SharplyLT.of_pow_lt h.1 h.2

/-- κ ≤ θ なら、(2^θ)⁺ は明示的な冪の評価を満たす。 -/
lemma cardinalChangeBound_succ_two_pow {κ θ : Cardinal.{u}}
    (hκ : κ ≤ θ) (hθ : Cardinal.aleph0 ≤ θ) :
    IsCardinalChangeBound κ (Order.succ (2 ^ θ)) := by
  refine ⟨?_, fun α β hα hβ ↦ ?_⟩
  · simp only [Order.lt_succ_iff]
    exact hκ.trans (Cardinal.cantor _).le
  · simp only [Order.lt_succ_iff] at hβ ⊢
    refine (Cardinal.power_le_power_right hβ).trans ?_
    rw [← Cardinal.power_mul]
    refine Cardinal.power_le_power_left (by simp) ?_
    conv_rhs => rw [← Cardinal.mul_eq_self hθ]
    exact mul_le_mul_right (hα.le.trans hκ) _

/-- 任意の指定上限を超え、濃度変更に使える同じ宇宙内の正則濃度が存在する。 -/
lemma exists_regular_cardinalChangeBound (κ σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ IsCardinalChangeBound κ μ := by
  let θ := max (max κ σ) Cardinal.aleph0
  have hθ : Cardinal.aleph0 ≤ θ := le_max_right _ _
  have hκ : κ ≤ θ := (le_max_left _ _).trans (le_max_left _ _)
  have hσ : σ ≤ θ := (le_max_right _ _).trans (le_max_left _ _)
  exact ⟨Order.succ (2 ^ θ), Cardinal.isRegular_succ (hθ.trans (Cardinal.cantor θ).le),
    hσ.trans_lt ((Cardinal.cantor θ).trans_le (Order.le_succ _)),
    cardinalChangeBound_succ_two_pow hκ hθ⟩

/-- 小さい濃度族に対して、同じ宇宙の一つの正則濃度で全ての冪の評価を満たせる。 -/
lemma exists_regular_cardinalChangeBound_family {ι : Type u} (κ : ι → Cardinal.{u})
    (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ ∀ i, IsCardinalChangeBound (κ i) μ := by
  obtain ⟨θ, hθ⟩ := Cardinal.exists_le_of_small κ
  obtain ⟨μ, hμ, hσ, h⟩ := exists_regular_cardinalChangeBound θ σ
  exact ⟨μ, hμ, hσ, fun i ↦ h.of_le (hθ i)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
