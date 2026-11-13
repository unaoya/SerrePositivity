module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.LengthAlgebra.Flat
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable

/-! # 有限長加群の Tor の正規化長さ（論文 Lemma 3.4・Corollary 2.6）

## 概要

正則局所環 `A`（次元 `e`）の正則パラメータ系 `z`、`A` 上有限な局所環 `T`、`T` 代数 `C` と正規化長さ `λ` が (3.9) `λ(H_i(z^v; C)) = 0`（`i > 0`）、`λ(C/(z^v)C) = v^e rank_A T` をみたすとき、有限長 `A` 加群 `V` について `λ(Tor_i^A(C, V)) = 0`（`i > 0`）、`λ(Tor_0^A(C, V)) = rank_A T · ℓ_A(V)`、すべて有限（Lemma 3.4、`lemma_3_4`）。Theorem 2.5 の (2.4)・(2.6) を (3.9) の形に書き直し（`lengthAlgebra_base_values`）、`T = D` の場合として Corollary 2.6 の 1・2（`cor_2_6_tor`）を得る。

## 方針

一般定理 `normalizedLength_tor_of_isWeaklyRegular`（IntersectionMultiplicity/NormalizedTor）に (3.9) の `v = 1` を渡す。`z` が弱正則列であることは正則局所環の一般論から、`λ` の定義域の `m_T C` から `m_A C` への取り替えは `m_T^N ⊆ m_A T` による。

## 規約

`Tor_i^A(C, V)` は `TorAlg (algebraMap A C) i V`（論文の `Tor_i^A(V, C)` と変数の順序が逆、Mathlib の規約）。Corollary 2.6 の 3（`λ_D(C_D/𝔡C_D) > 0`）は主経路の `Section4.residue_length_pos_of_lengthAlgebra_values`（Paper/Section4/LengthHypotheses）が担う。

## 使われ方

論文の主張として残す（主経路では使わない）。
-/

@[expose] public noncomputable section

universe u

section Lemma3_4Part

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

/-- **Lemma 3.4**：以下に明記した仮定のもとで、有限長 `A` 加群 `V` に対して (3.10)：
`λ(Tor_i^A(C, V)) = 0 (i > 0)`、`λ(Tor_0^A(C, V)) = rank_A T · ℓ_A(V)`（`Tor_0 = C ⊗_A V`）、
すべて有限。`z` を弱正則列にし（A1）、`λ` の定義域を `m_A C` に取り替えて、一般定理
`normalizedLength_tor_of_isWeaklyRegular` に (3.9) の `v = 1` を渡す。 -/
theorem lemma_3_4 (A T C : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    {e : ℕ} (z : Fin e → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hdim : ringKrullDim A = e)
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0)
    (hquot : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (V : Type u) [AddCommGroup V] [Module A V] (hV : Module.length A V ≠ ⊤) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg (algebraMap A C) i V) = 0) ∧
      lam.len (TorAlg (algebraMap A C) 0 V) =
        (Module.finrank A T : ℝ≥0∞) * ENat.toENNReal (Module.length A V) ∧
      (∀ i : ℕ, lam.len (TorAlg (algebraMap A C) i V) ≠ ⊤) := by
  have hVfl : IsFiniteLength A V := Module.length_ne_top_iff.mp hV
  have hreg := isWeaklyRegular_of_span_eq_maximalIdeal A z hz hdim
  have hN : ∃ N : ℕ, (maximalIdeal T) ^ N ≤ (maximalIdeal A).map (algebraMap A T) := by
    exact maximalIdeal_pow_le_map_of_finite (R := A) T
  let lam' : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)) :=
    lam.restrict _ (fun M _ _ hM ↦ IsPowTorsion.of_pow_le hN M hM)
  have hz1 : (fun j ↦ algebraMap A C (z j ^ 1)) = algebraMap A C ∘ z := by
    funext j
    simp
  have h39a : ∀ i : ℕ, 0 < i → lam'.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0 := by
    intro i hi
    have := hzero 1 one_pos i hi
    rwa [hz1] at this
  have h39b : lam'.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T := by
    have := hquot 1 one_pos
    rw [hz1] at this
    simpa [lam'] using this
  exact normalizedLength_tor_of_isWeaklyRegular (algebraMap A C) z hz hreg lam'
    (Module.finrank A T) h39a h39b V hVfl

end SerrePositivity

end Lemma3_4Part

section Corollary2_6Part

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

section preparation

variable {A D C : Type u} [CommRing A] [CommRing D] [IsLocalRing D]
  [Algebra A D] [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
  {h : ℕ} {t : Fin h → A}

/-- (2.4) と (2.6) を、基底 `A` のパラメータ系 `t` の冪 `t^v` について、`A → C` の像で書き直したもの：
`λ(H_i(t^v; C)) = 0 (i > 0)` と `λ(C/(t^v)C) = v^h · rank_A D`。`t` の `D` での像がパラメータ系で
あること（`hsop`）を使い、`algebraMap D C ∘ algebraMap A D = algebraMap A C` で書き換えるだけ。
Corollary 2.6 と Lemma 3.5 で、`NormalizedTor.lean` の仮定 (3.9) の形にするために使う。 -/
theorem lengthAlgebra_base_values
    {lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))}
    (hzero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0)
    (hbase : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (v : ℕ) (hv : 0 < v) :
    (∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (t j ^ v)) i) = 0) ∧
    lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (t j ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞) := by
  have heq : (fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ v)) =
      (fun j ↦ algebraMap A C (t j ^ v)) := by
    funext j
    simp [IsScalarTower.algebraMap_apply A D C]
  constructor
  · intro i hi
    have hz := hzero (algebraMap A D ∘ t) hsop v hv i hi
    rw [heq] at hz
    exact hz
  · have hq := hbase v hv
    change lam.len (C ⧸ Ideal.span
      (Set.range fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ v))) = _ at hq
    rw [heq] at hq
    exact hq

end preparation

/-- **Corollary 2.6** の 1・2（有限長加群の基底変更）：正則局所環 `A`、`A` 上有限な局所環 `D`、`A` の
正則パラメータ系 `t`（`D` のパラメータ系でもある）、Theorem 2.5 の性質をみたす `(C, λ)` について、
有限長 `A` 加群 `V` で `λ(Tor_i^A(C, V)) = 0 (i > 0)`、`λ(Tor_0^A(C, V)) = rank_A D · ℓ_A(V)`
（`Tor_0 = C ⊗_A V`）。(2.4)・(2.6) を `lengthAlgebra_base_values` で (3.9) の形にし、`T = D` として
Lemma 3.4（`lemma_3_4`）を適用する。 -/
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
  have hv := lengthAlgebra_base_values hzero hbase hsop
  have := lemma_3_4 A D C t ht hdim lam (fun v hv' ↦ (hv v hv').1) (fun v hv' ↦ (hv v hv').2) V hV
  exact ⟨this.1, this.2.1⟩

end SerrePositivity

end Corollary2_6Part

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Eq (3.10)"] _root_.SerrePositivity.lemma_3_4
attribute [cite Paper "Lemma 3.4"] _root_.SerrePositivity.lemma_3_4
attribute [cite Paper "Lemma 4.4"] _root_.SerrePositivity.lemma_3_4
