module

public import SerrePositivity.Core.Setup
public import SerrePositivity.Statement

/-!
# 核の場合の証明（論文 §5.5「Proof of Theorem 1.1」）

`CoreData` と二つの比較の主張から `χ^R(D, E) > 0` を出す。論文の最後の算術

  `|G_D| a_D a_E χ^R(D, E) = (1/|G_E|) Σ_σ Σ_γ b_{σ,γ} > 0`

をそのまま書いたもの。

そのうえで、核の場合の入力束 `Inputs.Core` を Prop 値の class として置き、
`core_statement` と同じ仮定のもとで結論を出す `core_of_inputs` を与える。
-/

public section

universe u

namespace SerrePositivity

namespace CoreData

variable {R : Type u} [CommRing R] {P Q : Ideal R} (X : CoreData R P Q)

/-- (5.18) と (5.17) から各 `c_σ` は正。 -/
lemma c_pos (h : X.SecondComparison) (σ : X.GD) : 0 < X.c σ := by
  obtain ⟨b, h518, hpos⟩ := h
  have hsum : 0 < ∑ γ, b σ γ := Finset.sum_pos (fun γ _ ↦ hpos σ γ) Finset.univ_nonempty
  rw [← h518 σ] at hsum
  have hcard : (0 : ℝ) < Fintype.card X.GE := by exact_mod_cast Fintype.card_pos
  exact (mul_pos_iff_of_pos_left hcard).mp hsum

/-- 論文 §5.5 の最後の算術：Lemma 5.2 と (5.18)、Lemma 5.6 から `χ^R(D, E) > 0`。 -/
theorem chi_pos (h1 : X.FirstComparison) (h2 : X.SecondComparison) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  obtain ⟨-, h53⟩ := h1
  have hsum : 0 < ∑ σ, X.c σ := Finset.sum_pos (fun σ _ ↦ X.c_pos h2 σ) Finset.univ_nonempty
  rw [← h53] at hsum
  have hk : (0 : ℝ) < (Fintype.card X.GD : ℝ) * X.aD * X.aE := by
    have := X.aD_pos
    have := X.aE_pos
    have : (0 : ℝ) < Fintype.card X.GD := by exact_mod_cast Fintype.card_pos
    positivity
  have : (0 : ℝ) < (chi R (R ⧸ P) (R ⧸ Q) : ℝ) := (mul_pos_iff_of_pos_left hk).mp hsum
  exact_mod_cast this

end CoreData

namespace Inputs

/-- 核の場合の入力束。`core_statement` の仮定のもとで、§5.1 のデータが存在して
論文の仮定 `IsPaperData` をみたし、Lemma 5.2（第一のノルム比較）と
(5.18)・Lemma 5.6（第二のノルム比較と正値性）が成り立つ。

論文での根拠：データの存在は Lemma 2.2、Theorem 2.5、§5.1 の Galois 閉包の構成。
`FirstComparison` は Lemma 5.2（Lemma 3.5 と Theorem 3.1 による）。
`SecondComparison` は §5.2–5.5 と Theorem 4.7。 -/
class Core : Prop where
  exists_coreData :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      [IsAlgClosed (IsLocalRing.ResidueField R)]
      (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
      (P Q : Ideal R) [P.IsPrime] [Q.IsPrime],
      0 < ringKrullDim (R ⧸ P) → 0 < ringKrullDim (R ⧸ Q) →
      ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R →
      (P ⊔ Q).radical = IsLocalRing.maximalIdeal R →
      ∃ X : CoreData R P Q, X.IsPaperData ∧ X.FirstComparison ∧ X.SecondComparison

end Inputs

variable (R : Type u) [CommRing R]

/-- 核の場合（`core_statement` と同じ主張）を入力束 `Inputs.Core` から導く。 -/
theorem core_of_inputs [Inputs.Core.{u}] [IsRegularLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : 0 < ringKrullDim (R ⧸ P)) (hQ : 0 < ringKrullDim (R ⧸ Q))
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = IsLocalRing.maximalIdeal R) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  obtain ⟨X, -, h1, h2⟩ := Inputs.Core.exists_coreData R p P Q hP hQ hsum hprimary
  exact X.chi_pos h1 h2

end SerrePositivity
