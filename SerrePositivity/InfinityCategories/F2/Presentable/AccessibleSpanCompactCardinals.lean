module

public import SerrePositivity.InfinityCategories.F2.Presentable.StrongCompactCardinals

/-!
概要：accessible cospan の三圏と二関手に共通の compact 保存濃度を与える。
方針：関手の保存濃度を超える共通 accessibility 濃度を選び、compact 保存へ拡大する。
規約：小余極限の存在・保存を追加しない。
使われ方：accessible 引き戻しと固定標的 fiber の小さい compact 候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：accessible な両脚は、任意の下限を超える共通濃度で compact 対象を保存する。
方針：両関手の保存濃度を揃えてから全 compact 像の共通濃度を選ぶ。
規約：三圏の accessibility と両脚の filtered 保存も同じ濃度で保持する。
使われ方：accessible 引き戻しの小さい compact 成分模型。 -/
lemma exists_accessibleSpan_compactCardinal
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : IsAccessible E) (hD : IsAccessible D) (hB : IsAccessible B)
    (p : E ⟶ B) (q : D ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor q) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < μ ∧ IsCardinalChangeBound κ μ ∧
      IsKappaAccessible μ E ∧ IsKappaAccessible μ D ∧ IsKappaAccessible μ B ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ q ∧
      (∀ x : E _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ x →
        Compact.IsKappaCompact.{u, u + 1} μ (p.app _ x)) ∧
      (∀ y : D _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ y →
        Compact.IsKappaCompact.{u, u + 1} μ (q.app _ y)) := by
  obtain ⟨ρ, _, hpρ⟩ := hp
  obtain ⟨τ, _, hqτ⟩ := hq
  let C : ULift.{u} (Fin 3) → SSet.{u + 1} := fun i ↦ ![E, D, B] i.down
  have (i : ULift.{u} (Fin 3)) : Quasicategory (C i) := by
    rcases i with ⟨i⟩
    fin_cases i <;> dsimp [C] <;> infer_instance
  have hc : ∀ i, IsAccessible (C i) := by
    rintro ⟨i⟩
    fin_cases i
    · exact hE
    · exact hD
    · exact hB
  obtain ⟨κ, hκ, hbound, hC⟩ := exists_common_accessibilityCardinal C hc
    (max σ (max ρ τ))
  have he : IsKappaAccessible κ E := hC ⟨0⟩
  have hd : IsKappaAccessible κ D := hC ⟨1⟩
  have hb : IsKappaAccessible κ B := hC ⟨2⟩
  have hρκ : ρ ≤ κ := (le_max_left ρ τ).trans ((le_max_right σ _).trans hbound.le)
  have hτκ : τ ≤ κ := (le_max_right ρ τ).trans ((le_max_right σ _).trans hbound.le)
  have hpκ := hpρ.of_le hρκ
  have hqκ := hqτ.of_le hτκ
  obtain ⟨μ, hμ, hσ, hκμ, heμ, hdμ, hpμ, hqμ⟩ :=
    exists_common_compactPreservingCardinal he hd hb.isAccessible p q hpκ hqκ
      (max σ κ)
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hκle : κ ≤ μ := (le_max_right σ κ).trans hσ.le
  exact ⟨κ, μ, hκ, hμ, (le_max_left σ κ).trans_lt hσ, hκμ, heμ, hdμ,
    hb.of_cardinalChangeBound hκμ, hpκ.of_le hκle, hqκ.of_le hκle, hpμ, hqμ⟩

end SerrePositivity.InfinityCategories.F2.Presentable
