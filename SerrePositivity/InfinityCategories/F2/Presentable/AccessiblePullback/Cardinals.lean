module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleSpanCompactCardinals

/-!
概要：accessible cospan の相対交互構成に使う二つの共通濃度を選ぶ。
方針：元の保存濃度を超える κ₀ を選び、compact 保存への拡大 μ と両方の情報を保持する。
規約：全小余極限保存を追加しない。κ₀ の表示添字内で相対構成を行う。
使われ方：長さ κ₀ の交互構成と小さい μ-compact 生成表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：相対構成の κ₀ と小生成模型の μ を、両方の保存性を保って選ぶ。
方針：三圏の共通 accessibility と既存の compact 保存濃度選択を順に使う。
規約：κ₀ 側の accessibility と filtered 保存を結論から落とさない。
使われ方：μ-small な κ₀-filtered 表示部分の構成。 -/
lemma exists_relativeCardinals
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : IsAccessible E) (hD : IsAccessible D) (hB : IsAccessible B)
    (p : E ⟶ B) (q : D ⟶ B)
    (hpc : IsAccessibleFunctor p) (hqc : IsAccessibleFunctor q) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < κ ∧ κ < μ ∧
      IsCardinalChangeBound κ μ ∧
      IsKappaAccessible κ E ∧ IsKappaAccessible κ D ∧ IsKappaAccessible κ B ∧
      IsKappaAccessibleFunctor κ p ∧ IsKappaAccessibleFunctor κ q ∧
      IsKappaAccessible μ E ∧ IsKappaAccessible μ D ∧ IsKappaAccessible μ B ∧
      IsKappaAccessibleFunctor μ p ∧ IsKappaAccessibleFunctor μ q ∧
      (∀ x, Compact.IsKappaCompact.{u, u + 1} μ x →
        Compact.IsKappaCompact.{u, u + 1} μ (p.app _ x)) ∧
      (∀ y, Compact.IsKappaCompact.{u, u + 1} μ y →
        Compact.IsKappaCompact.{u, u + 1} μ (q.app _ y)) := by
  obtain ⟨ρ, _, hpρ⟩ := hpc
  obtain ⟨τ, _, hqτ⟩ := hqc
  let X : ULift.{u} (Fin 3) → SSet.{u + 1} := fun i ↦ ![E, D, B] i.down
  have (i : ULift.{u} (Fin 3)) : Quasicategory (X i) := by
    rcases i with ⟨i⟩
    fin_cases i <;> dsimp [X] <;> infer_instance
  have hx : ∀ i, IsAccessible (X i) := by
    rintro ⟨i⟩
    fin_cases i
    · exact hE
    · exact hD
    · exact hB
  obtain ⟨κ, hκ, hbound, hX⟩ := exists_common_accessibilityCardinal X hx (max σ (max ρ τ))
  have he : IsKappaAccessible κ E := hX ⟨0⟩
  have hd : IsKappaAccessible κ D := hX ⟨1⟩
  have hb : IsKappaAccessible κ B := hX ⟨2⟩
  have hρ : ρ ≤ κ := (le_max_left ρ τ).trans ((le_max_right σ _).trans hbound.le)
  have hτ : τ ≤ κ := (le_max_right ρ τ).trans ((le_max_right σ _).trans hbound.le)
  have hpκ := hpρ.of_le hρ
  have hqκ := hqτ.of_le hτ
  obtain ⟨μ, hμ, hκμ, hchange, heμ, hdμ, hpCompact, hqCompact⟩ :=
    exists_common_compactPreservingCardinal he hd hb.isAccessible p q hpκ hqκ κ
  have : Fact μ.IsRegular := ⟨hμ⟩
  exact ⟨κ, μ, hκ, hμ, (le_max_left σ _).trans_lt hbound, hκμ, hchange,
    he, hd, hb, hpκ, hqκ, heμ, hdμ, hb.of_cardinalChangeBound hchange,
    hpκ.of_le hκμ.le, hqκ.of_le hκμ.le, hpCompact, hqCompact⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
