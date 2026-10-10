module

public import SerrePositivity.Paper.Lemma5_2

/-!
# 核の場合の正値性（論文 §5.5）

## 概要

論文 §5.5 の最後の議論：第一のノルム比較（Lemma 5.2）

  `|G| · a · d · χ = Σ_σ c_σ`（`a = rank_{R/P} D`、`d = rank_{R/Q} E`、`χ = χ^R(R/P, R/Q)`）

と第二のノルム比較（式 (5.18)）

  `|H| · c_σ = Σ_γ b_{σ,γ}`、各 `b_{σ,γ} > 0`

から `χ > 0` を導く。`b_{σ,γ}` は係数変更後の Euler 評価で、
極小性による下界は `λ(C/m C)` と生成元数の正規化極限との積である。

## 内容

- `chi_pos_of_comparisons`：最後の算術。二つの比較等式と `b > 0`、階数因子 `a, d > 0`、添字集合 `G`、
  `H` の非空性だけから `χ > 0`。環や長さ代数から独立。
- `core_of_inputs`：Lemma 5.2（`firstComparison`）を適用し、第二比較の `b` とその二つの性質を引数と
  して受け取って `χ > 0` を結論する。
- `core_of_twistedEuler_pos`：第一比較に、構成済みの各 `c_σ > 0` を直接渡す。
  `Section5.core_of_lengthAlgebras` が長さ代数の公式からこの正値性も導く。

## 注意

ここではデータの存在を一括で仮定する class を置かない。`core_of_inputs` は「指定した対象と仮定が
与えられたときの正値性」であり、`core_statement`（`Paper/Statement.lean`）からそれらの対象
（正規化基底 `A ⊆ D`、長さ代数、群 `G`、`H`）を構成する段階は別途必要である。
`Section4.symmetricPaperEuler_conjSum_eq` は第二比較の共通部分、
`Section5.paperEuler_pos_of_finiteApproximation` は個々の Euler 評価の正値性を供給する。
有限近似の極小分解の切り詰め・商での支持・正の Euler 評価をもつ対象の構成は
`Section5.exists_paperEuler_pos_of_minimalApproximation` で実装済み。
`Section5.paperBaseChangeBetti_eq_of_approximation_limit` は、商の各次数の評価を
有限近似の Tor 極限と同定する。Euler 評価はその有限交代和に一致し、共通剰余体の下では
基底環上の通常 Tor の長さから係数環上の通常 Euler 評価へも移せる。
`Section5.paperOrdinaryEulerK0_eq_twistedEuler` は、有限近似の極限を仮定として
係数環の全自己同型によるひねりの通常評価を `c_σ` と同定する。
同じ有限近似から、この評価・支持・極小性・正の零次階数をもつ対象も構成できる。
`Section5.secondComparison_of_approximation` は、同じ近似複体の支持を根基の包含で移し、
実際の K₀ 作用について全ひねりの通常評価と第二比較を導く。
`Section5.secondComparison_minimal_lower_bound` は共通下界を各共役と通常評価の両方へ渡す。
`Section5.exists_secondComparison_pos_of_approximation` は、有限近似から同じ対象について
第二比較・全共役の正値性・通常 Euler 数の正値性を同時に導く。
係数変更後の振幅・極小性と各共役のイデアル条件は内部で確認する。
`exists_secondComparison_pos_of_primary` は、通常 Koszul の有限性と下界の商の有限性も導く。
`Section5.exists_secondComparison_pos_of_lengthAlgebra` は、有限局所代数と長さ代数の公式から
局所性・根基条件・Koszul 有限性・Euler 数の一致・下界の商の正値性も確認する。
`Section5.lambdaChi_pos_of_parameter_tower` は Lemma 5.4 の近似列を内部で作り、
Lemma 5.3 と第二比較を接続して `lambdaChi > 0` を導く。
`Section5.twistedEuler_pos_of_lengthAlgebras` は本文のパラメータ系と長さ代数の公式から
各 `c_σ > 0` を導く。塔の作用・消去冪・商の正の有限な長さは内部で確認する。
`Section5.core_of_lengthAlgebras` が同じ設定で第一比較まで接続する。
正規化基底・有限拡大・群作用・長さ代数を核心定理の仮定から選ぶ段階はまだ必要。
Lemma 5.2 の未証明入力への依存も残る。
-/

public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- 第一比較と各 `c_σ > 0` から交点数の正値性を得る。
第二比較の中間評価を再び入力する必要はない。 -/
theorem chi_pos_of_firstComparison {G : Type u} [Fintype G] [Nonempty G]
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (χ : ℤ) (c : G → ℝ)
    (hfirst : (Fintype.card G : ℝ) * a * d * (χ : ℝ) = ∑ σ, c σ)
    (hc : ∀ σ, 0 < c σ) : 0 < χ := by
  have hs : 0 < ∑ σ, c σ := Finset.sum_pos (fun σ _ ↦ hc σ) Finset.univ_nonempty
  rw [← hfirst] at hs
  have hk : (0 : ℝ) < (Fintype.card G : ℝ) * a * d := by
    have : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    positivity
  have : (0 : ℝ) < (χ : ℝ) := (mul_pos_iff_of_pos_left hk).mp hs
  exact_mod_cast this

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
  exact chi_pos_of_firstComparison a d ha hd χ c hfirst hc

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- 第一比較の設定と各 `c_σ > 0` から核心の交点数の正値性を導く。
`twistedEuler_pos_of_lengthAlgebras` の結論をそのまま受け取る入口。
環・群・長さ代数の存在を核心定理の仮定から構成する部分は別途必要である。 -/
theorem core_of_twistedEuler_pos
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
    (hc : ∀ σ : G, 0 < twistedEuler R D E C G lam σ) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  let := Fintype.ofFinite G
  have hfirst := firstComparison P Q A D E C G z hh hz hdimA hsupport hresA hresR
    hsurj htrans rankE hPdim hQdim lam hzero hquot p hsum hprimary
  exact chi_pos_of_firstComparison (Module.finrank (R ⧸ P) D) (Module.finrank (R ⧸ Q) E)
    rankD rankE _ (twistedEuler R D E C G lam) hfirst.2 hc

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
