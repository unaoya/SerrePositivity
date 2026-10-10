module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import SerrePositivity.PerfectComplex.QuotientLength
public import Mathlib.Basic.ENNReal.Real

/-!
# Corollary 2.6 (3)：`λ_D(C_D/𝔡 C_D) > 0`

## 概要

論文 Corollary 2.6 の 3 番目の主張：Theorem 2.5 の長さ代数 `(C_D, λ_D)` について
`λ_D(C_D / 𝔡 C_D) > 0`。論文の証明（p.9）どおり、`D` のパラメータイデアル `H`（ここでは基底の
パラメータ `t` の像で生成されるもの）をとり、`D/H` の組成列を `C_D` でテンソルすると右完全性から
`C_D/HC_D` のフィルトレーションができ、各因子は `C_D/𝔡 C_D` の商になるので

  `0 < e(H, D) = λ_D(C_D/HC_D) ≤ ℓ(D/H) · λ_D(C_D/𝔡 C_D)`。

左の `0 < e(H, D) = λ_D(C_D/HC_D)` は (2.5) の `v = 1` と Hilbert–Samuel 重複度の正値性
（`HilbertSamuel.multiplicity_pos`、当面 `sorry`）、右の不等式は一般論
`len_quotient_map_le_length_mul`（`PerfectComplex/QuotientLength.lean`）。

Corollary 2.6 の 1・2（有限長加群の係数拡大）は `Paper/Corollary2_6.lean` の `cor_2_6_tor` で
証明済み。そこの `cor_2_6_pos` はこの定理から証明している。

## 仮定

(2.5) だけを仮定として受け取る（`hquot`）。`λ` の具体的な構成や (2.4)、(2.6) は要らない。
`D` の Noether 性は `D/H` が有限長であることに使う。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

namespace Section2

/-- **Corollary 2.6 (3)**：(2.5) をみたす `λ` について `0 < λ(C/𝔡 C)`。 -/
theorem cor_2_6_residue_pos (A D C : Type u) [CommRing A] [IsLocalRing A] [CommRing D]
    [IsLocalRing D] [IsNoetherianRing D] [Algebra A D] [CommRing C] [Algebra D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    {h : ℕ} (t : Fin h → A) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hquot : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
        ENNReal.ofReal ((v : ℝ) ^ h *
          (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ))) :
    0 < lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) := by
  -- `D/H` は有限長（`√H = m_D`）、`H = (t)D`
  have hArt : IsArtinianRing (D ⧸ Ideal.span (Set.range (algebraMap A D ∘ t))) := by
    have : IsArtinianRing (D ⧸ maximalIdeal D) := inferInstanceAs (IsArtinianRing (ResidueField D))
    exact isArtinianRing_quotient_of_le_radical (maximalIdeal D) _ (by rw [hsop.2])
  have hH : IsFiniteLength D (D ⧸ Ideal.span (Set.range (algebraMap A D ∘ t))) := by
    refine isFiniteLength_of_le_radical_annihilator (Ideal.span (Set.range (algebraMap A D ∘ t)))
      (D ⧸ Ideal.span (Set.range (algebraMap A D ∘ t))) (le_trans ?_ Ideal.le_radical)
    intro a ha
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right x _ ha
  -- (2.5) の `v = 1`：`λ(C/HC) = e(H, D) > 0`
  have h1 := hquot (algebraMap A D ∘ t) hsop 1 one_pos
  have hspan : Ideal.span (Set.range fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ 1)) =
      (Ideal.span (Set.range (algebraMap A D ∘ t))).map (algebraMap D C) := by
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [pow_one, Function.comp_def]
  rw [hspan] at h1
  have hpos := HilbertSamuel.multiplicity_pos_of_isSystemOfParameters D _ hsop
  have hposC : 0 < lam.len (C ⧸ (Ideal.span (Set.range (algebraMap A D ∘ t))).map
      (algebraMap D C)) := by
    rw [h1]
    simp only [Nat.cast_one, one_pow, one_mul]
    exact ENNReal.ofReal_pos.mpr (by exact_mod_cast hpos)
  exact len_quotient_maximalIdeal_pos lam _ hH hposC

end Section2

end SerrePositivity
