module

public import SerrePositivity.Inputs.LengthAlgebra
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing
public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.IntersectionMultiplicity.NormalizedTor
public import SerrePositivity.Paper.Section2.Corollary2_6

/-!
# Corollary 2.6：長さ代数への有限長加群の係数拡大

## 概要

Theorem 2.5 の長さ代数 `(C_D, λ_D)` について、有限長 `A` 加群 `V` の係数拡大の `λ_D` を計算する：

1. `λ_D(Tor_i^A(C_D, V)) = 0 (i > 0)`、
2. `λ_D(C_D ⊗_A V) = rank_A D · ℓ_A(V)`、
3. `λ_D(C_D / m_D C_D) > 0`。

## 方針

1・2 は `cor_2_6_tor`：一般定理 `normalizedLength_tor_of_isWeaklyRegular`
（`IntersectionMultiplicity/NormalizedTor.lean`）を、`z = t`（`A` の正則パラメータ系）、
`r = rank_A D` に適用する。(3.9) に当たる仮定は Theorem 2.5 の (2.4)、(2.6) の `v = 1`
（`lengthAlgebra_base_values_one`）から、`t` が弱正則列であることは A1
（`CommutativeAlgebra/RegularLocalRing.lean`、証明済み）から得る。`λ_D` の定義域を `m_D C` から `m_A C` に
取り替えるには `NormalizedLength.restrictToBase` を使う。

3 は `cor_2_6_pos`：(2.5) の `v = 1` で `λ_D(C_D/(t)C_D) = e((t), D) > 0`（Hilbert–Samuel 重複度の
正値性 `HilbertSamuel.multiplicity_pos`、多項式性・次元定理から証明済み）、`D/(t)D` の組成列を
テンソルして `λ_D(C_D/(t)C_D) ≤ ℓ(D/(t)D) · λ_D(C_D/m_D C_D)`。証明の本体は
`Paper/Section2/Corollary2_6.lean` の `Section2.cor_2_6_residue_pos`。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

/-- **Corollary 2.6** の 1・2（有限長加群の基底変更）：正則局所環 `A`、`A` 上有限な局所環 `D`、`A` の
正則パラメータ系 `t`（`D` のパラメータ系でもある）、Theorem 2.5 の性質をみたす `(C, λ)` について、
有限長 `A` 加群 `V` で `λ(Tor_i^A(C, V)) = 0 (i > 0)`、`λ(Tor_0^A(C, V)) = rank_A D · ℓ_A(V)`
（`Tor_0 = C ⊗_A V`）。一般定理 `normalizedLength_tor_of_isWeaklyRegular` を `z = t` に適用する。
完備性・生成的分離性などは要らず、ここに挙げた仮定で足りる。 -/
theorem cor_2_6_tor (A D : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] [Module.Finite A D] {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hdim : ringKrullDim A = h)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (C : Type u) [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hzero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0)
    (hbase : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (V : Type u) [AddCommGroup V] [Module A V] (hV : Module.length A V ≠ ⊤) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg (algebraMap A C) i V) = 0) ∧
      lam.len (TorAlg (algebraMap A C) 0 V) =
        (Module.finrank A D : ℝ≥0∞) * ENat.toENNReal (Module.length A V) := by
  have hVfl : IsFiniteLength A V := Module.length_ne_top_iff.mp hV
  have hreg := isWeaklyRegular_of_span_eq_maximalIdeal A t ht hdim
  let lam' := lam.restrictToBase A D
  obtain ⟨h39a, h39b⟩ := lengthAlgebra_base_values_one hzero hbase hsop
  have := normalizedLength_tor_of_isWeaklyRegular (algebraMap A C) t ht hreg lam'
    (Module.finrank A D) h39a h39b V hVfl
  exact ⟨this.1, this.2.1⟩

/-- **Corollary 2.6** の 3：`λ_D(C_D / m_D C_D) > 0`。(2.5) の `v = 1` と Hilbert–Samuel 重複度の
正値性（`HilbertSamuel.multiplicity_pos`、多項式性・次元定理から証明済み）、`D/(t)D` の組成列を `C` でテンソルする
右完全性の議論（`Section2.cor_2_6_residue_pos`）による。(2.5) 以外の性質や、完備性・分離性などは
要らない。 -/
theorem cor_2_6_pos (A D C : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] [Algebra A D] [CommRing C] [Algebra D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    {h : ℕ} (t : Fin h → A) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hquot : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
        ENNReal.ofReal ((v : ℝ) ^ h *
          (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ))) :
    0 < lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) :=
  Section2.cor_2_6_residue_pos A D C lam t hsop hquot

end SerrePositivity
