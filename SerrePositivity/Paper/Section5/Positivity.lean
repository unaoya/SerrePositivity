module

public import SerrePositivity.Paper.Lemma5_2

/-!
# 核の場合の正値性（論文 §5.5）

## 概要

論文 §5.5 の最後の議論：第一のノルム比較（Lemma 5.2）

  `|G| · a · d · χ = Σ_σ c_σ`（`a = rank_{R/P} D`、`d = rank_{R/Q} E`、`χ = χ^R(R/P, R/Q)`）

と第二のノルム比較（Lemma 5.4）

  `|H| · c_σ = Σ_γ b_{σ,γ}`、各 `b_{σ,γ} > 0`

から `χ > 0` を導く。`b_{σ,γ}` は長さ代数の商の正規化長さ `λ(C/m C)`（Corollary 2.6 の 3 で正）に
当たる量である。

## 内容

- `chi_pos_of_comparisons`：最後の算術。二つの比較等式と `b > 0`、階数因子 `a, d > 0`、添字集合 `G`、
  `H` の非空性だけから `χ > 0`。環や長さ代数から独立。
- `core_of_inputs`：Lemma 5.2（`firstComparison`）を適用し、第二比較の `b` とその二つの性質を引数と
  して受け取って `χ > 0` を結論する。

## 注意

ここではデータの存在を一括で仮定する class を置かない。`core_of_inputs` は「指定した対象と仮定が
与えられたときの正値性」であり、`core_statement`（`Paper/Statement.lean`）からそれらの対象
（正規化基底 `A ⊆ D`、長さ代数、群 `G`、`H`）を構成する段階と、第二比較 Lemma 5.4 の証明は別途
必要である。Lemma 5.2 の一般論の入力と未証明結果への依存も残る。
-/

public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- **最後の算術**：`|G| · a · d · χ = Σ_σ c_σ`（`hfirst`）、`|H| · c_σ = Σ_γ b_{σ,γ}`（`hsecond`）、
`b_{σ,γ} > 0`（`hpos`）、`a, d > 0`、`G`、`H` が空でないなら、整数 `χ` は正。各 `c_σ` が正の和を `|H|` で
割ったものなので正、したがって `Σ_σ c_σ > 0`、`|G| a d > 0` で割って `χ > 0`。 -/
theorem chi_pos_of_comparisons {G H : Type u} [Fintype G] [Nonempty G]
    [Fintype H] [Nonempty H] (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (χ : ℤ) (c : G → ℝ) (b : G → H → ℝ)
    (hfirst : (Fintype.card G : ℝ) * a * d * (χ : ℝ) = ∑ σ, c σ)
    (hsecond : ∀ σ, (Fintype.card H : ℝ) * c σ = ∑ γ, b σ γ)
    (hpos : ∀ σ γ, 0 < b σ γ) : 0 < χ := by
  have hc (σ : G) : 0 < c σ := by
    have hs : 0 < ∑ γ, b σ γ := Finset.sum_pos (fun γ _ ↦ hpos σ γ) Finset.univ_nonempty
    rw [← hsecond σ] at hs
    have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
    exact (mul_pos_iff_of_pos_left hcard).mp hs
  have hs : 0 < ∑ σ, c σ := Finset.sum_pos (fun σ _ ↦ hc σ) Finset.univ_nonempty
  rw [← hfirst] at hs
  have hk : (0 : ℝ) < (Fintype.card G : ℝ) * a * d := by
    have : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    positivity
  have : (0 : ℝ) < (χ : ℝ) := (mul_pos_iff_of_pos_left hk).mp hs
  exact_mod_cast this

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  [Inputs.RegularResolution R] [Inputs.IntersectionAdditivity R]
  [Inputs.IntersectionVanishing R]

/-- **核の場合の正値性（条件付き）**：Lemma 5.2 の仮定（`firstComparison` と同じ。`D` の階数が正
`rankD` を追加）に加えて、第二比較のデータ `H`、`b : G → H → ℝ` と、等式
`|H| · c_σ = Σ_γ b_{σ,γ}`（`hsecond`）、正値性 `b > 0`（`hpos`）を仮定すると `χ^R(R/P, R/Q) > 0`。
`firstComparison` の結論を `chi_pos_of_comparisons` に渡すだけ。対象の存在を主張する定理ではなく、
与えられた対象についての条件付きの結論である。 -/
theorem core_of_inputs
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (A D E C G : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing D] [IsLocalRing D] [Algebra R D] [Algebra (R ⧸ P) D]
    [IsScalarTower R (R ⧸ P) D] [Module.Finite (R ⧸ P) D]
    [CommRing E] [Algebra R E] [Algebra (R ⧸ Q) E]
    [IsScalarTower R (R ⧸ Q) E] [Module.Finite (R ⧸ Q) E]
    [Algebra A D] [Module.Finite A D]
    [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    [Group G] [Finite G] [MulSemiringAction G D] [SMulCommClass G A D]
    {h l : ℕ} (z : Fin h → A) (hh : 0 < h)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hdimA : ringKrullDim A = h)
    (hsupport : (Ideal.span (Set.range (algebraMap A D ∘ z))).radical = maximalIdeal D)
    (hresA : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hresR : Function.Surjective ((residue D).comp (algebraMap R D)))
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A D)))
    (htrans : IsGeometricallyTransitive A D G)
    (rankD : 0 < Module.finrank (R ⧸ P) D) (rankE : 0 < Module.finrank (R ⧸ Q) E)
    (hPdim : ringKrullDim (R ⧸ P) = h) (hQdim : ringKrullDim (R ⧸ Q) = l)
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0)
    (hquot : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R)
    (H : Type u) [Fintype H] [Nonempty H] (b : G → H → ℝ)
    (hsecond : ∀ σ, (Fintype.card H : ℝ) * twistedEuler R D E C G lam σ = ∑ γ, b σ γ)
    (hpos : ∀ σ γ, 0 < b σ γ) : 0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let := Fintype.ofFinite G
  have hfirst := firstComparison P Q A D E C G z hh hz hdimA hsupport hresA hresR
    hsurj htrans rankE hPdim hQdim lam hzero hquot p hsum hprimary
  exact chi_pos_of_comparisons (Module.finrank (R ⧸ P) D) (Module.finrank (R ⧸ Q) E)
    rankD rankE _ (twistedEuler R D E C G lam) b hfirst.2 hsecond hpos

end SerrePositivity
