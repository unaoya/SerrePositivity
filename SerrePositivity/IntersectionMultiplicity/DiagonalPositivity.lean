module

public import SerrePositivity.IntersectionMultiplicity.DiagonalDimension
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicityProof
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicityLimit
public import Mathlib.RingTheory.LocalRing.Quotient

/-! # 冪級数環での Serre の正値性（対角線論法）

## 概要

体 `k` 上の冪級数環 `R = k[[X_1, …, X_d]]` と素イデアル `P, Q` について、
`R/P ⊗ R/Q` が有限長で `dim R/P + dim R/Q = d` なら `χ^R(R/P, R/Q) > 0`。

## 方針

対角線の商 `T = R[[Y]] / (PS + Q^{i₂} S)` と対角線の元の像 `z = δ` について：

- 全ての `n` で `ℓ_R Tor_n^R(R/P, R/Q) = ℓ_T H_n(z; T)`（`length_torModule_eq_length_koszulHomologySelf`）。
- `dim T = dim R/Q + dim R/P = d`（`ringKrullDim_diagonalQuot`）。
- `T/(z) ≅ H_0(z; T)` の長さは `ℓ(R/P ⊗ R/Q) < ∞` なので `(z)` は極大イデアル準素。
  よって `z` は `T` のパラメータ系。
- `χ^R(R/P, R/Q) = χ(z; T) = e((z); T) > 0`（Koszul 重複度公式と重複度の正値性）。

## 使われ方

解説の付録 A（「引用している結果」の対角線論法の段落）の工程（結論 $\chi=e(\delta;T)>0$）。剰余標数零の正則局所環での正値性の核。
-/

@[expose] public noncomputable section

universe u

open IsLocalRing MvPowerSeries TensorProduct

namespace SerrePositivity.DiagonalRing

variable (k : Type u) [Field k] (d : ℕ)

local notation "𝓡" => MvPowerSeries (Fin d) k

/-- 有限長の商のイデアルは、極大イデアルに含まれれば極大イデアル準素。 -/
theorem radical_eq_maximalIdeal_of_length_ne_top {B : Type u} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (I : Ideal B) (hIm : I ≤ maximalIdeal B)
    (hI : Module.length B (B ⧸ I) ≠ ⊤) : I.radical = maximalIdeal B := by
  have hlen := Module.length_ne_top_iff.mp hI
  have : IsArtinian B (B ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  have : IsArtinianRing (B ⧸ I) := isArtinian_of_tower B inferInstance
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  apply le_antisymm
  · exact (Ideal.IsPrime.radical_le_iff (maximalIdeal.isMaximal B).isPrime).mpr hIm
  · intro x hx
    exact ⟨n, hn (Ideal.pow_mem_pow hx n)⟩

/-- 符号付きの和の添字の付け替え：`Σ_{i ∈ [-d, 0]} (-1)^i a_{-i} = Σ_{n ≤ d} (-1)^n a_n`。 -/
theorem sum_Icc_negOnePow_eq_sum_range (a : ℤ → ℝ) :
    ∑ i ∈ Finset.Icc (-(d : ℤ)) 0, ((i.negOnePow : ℤ) : ℝ) * a i =
      ∑ n ∈ Finset.range (d + 1), ((-1 : ℤ) ^ n : ℝ) * a (-(n : ℤ)) := by
  refine Finset.sum_nbij' (fun i : ℤ ↦ (-i).toNat) (fun n : ℕ ↦ -(n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [Finset.mem_range]
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro i hi
    have := Finset.mem_Icc.mp hi
    change -(((-i).toNat : ℕ) : ℤ) = i
    omega
  · intro n _
    simp
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi' : -(((-i).toNat : ℕ) : ℤ) = i := by omega
    rw [hi']
    congr 1
    have : i = -(((-i).toNat : ℕ) : ℤ) := hi'.symm
    conv_lhs => rw [this, Int.negOnePow_neg, Int.coe_negOnePow_natCast]
    push_cast
    rfl

/-- **冪級数環での正値性**：`R = k[[X_1, …, X_d]]`、素イデアル `P, Q` について、`R/P ⊗ R/Q` が
有限長で `dim R/P + dim R/Q = dim R` なら `χ^R(R/P, R/Q) > 0`。対角線の商 `T` の Koszul Euler 数が
`T` の重複度に等しいことによる。 -/
theorem chi_pos_of_prime (P Q : Ideal 𝓡) [P.IsPrime] [Q.IsPrime]
    (hfin : Module.length 𝓡 ((𝓡 ⧸ P) ⊗[𝓡] (𝓡 ⧸ Q)) ≠ ⊤)
    (hdim : ringKrullDim (𝓡 ⧸ P) + ringKrullDim (𝓡 ⧸ Q) = ringKrullDim 𝓡) :
    0 < chi 𝓡 (𝓡 ⧸ P) (𝓡 ⧸ Q) := by
  have hP : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have hQ : Q ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  let T := diagonalQuot k d P Q
  let := localDiagonalQuot k d P Q hP hQ
  have hT := coeffIdeal_sup_varIdeal_ne_top k d P Q hP hQ
  let z : Fin d → T := algebraMap (DiagonalRing k d) T ∘ diag k d
  have hlen : ∀ n, torLength 𝓡 n (𝓡 ⧸ P) (𝓡 ⧸ Q) = Module.length T (koszulHomologySelf z n) :=
    length_torModule_eq_length_koszulHomologySelf k d P Q hT
  -- `dim T = d`
  have hdimT : ringKrullDim T = d := by
    rw [ringKrullDim_diagonalQuot k d P Q hP hQ, add_comm, hdim, ringKrullDim_mvPowerSeries_field]
  -- `(z)` は極大イデアル準素
  have hzm : Ideal.span (Set.range z) ≤ maximalIdeal T := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hδ : diag k d i ∈ maximalIdeal (DiagonalRing k d) :=
      sub_mem (const_mem_maximalIdeal k d (X_mem_maximalIdeal k d i)) (var_mem_maximalIdeal k d i)
    have hloc : IsLocalHom (algebraMap (DiagonalRing k d) T) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    exact map_maximalIdeal_le (algebraMap (DiagonalRing k d) T) (Ideal.mem_map_of_mem _ hδ)
  have hz0 : Module.length T (T ⧸ Ideal.span (Set.range z)) ≠ ⊤ := by
    obtain ⟨e⟩ := koszulComplex_homology_zero_equiv z
    rw [← e.length_eq]
    have h0 := hlen 0
    rw [torLength, (torModuleZeroEquiv 𝓡 (𝓡 ⧸ P) (𝓡 ⧸ Q)).length_eq] at h0
    change Module.length T (koszulHomologySelf z 0) ≠ ⊤
    rw [← h0]
    exact hfin
  have hsop : IsSystemOfParameters T z :=
    ⟨hdimT, radical_eq_maximalIdeal_of_length_ne_top _ hzm hz0⟩
  -- 重複度は正で、Koszul Euler 数に等しい
  have hmult := HilbertSamuel.multiplicity_pos_of_isSystemOfParameters T z hsop
  have heq := KoszulMultiplicityProof.multiplicity_eq_chiOrd_koszul z hsop
  -- `χ` を Koszul Euler 数で書く
  have hvanish : ∀ i, d < i → torLength 𝓡 i (𝓡 ⧸ P) (𝓡 ⧸ Q) = 0 := by
    intro i hi
    rw [hlen i, Module.length_eq_zero_iff]
    have hX : CategoryTheory.Limits.IsZero ((koszulComplex z).X (-(i : ℤ))) :=
      koszulComplex_isZero_X_of_lt z _ (by omega)
    exact ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X _ _ hX)
  have hchi : (chi 𝓡 (𝓡 ⧸ P) (𝓡 ⧸ Q) : ℝ) = chiOrd (koszulComplex z) := by
    rw [chi_eq_sum_range 𝓡 _ _ d hvanish, HilbertSamuel.chiOrd_koszul_eq_sum,
      sum_Icc_negOnePow_eq_sum_range d]
    push_cast
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [hlen n]
  have : (0 : ℝ) < chi 𝓡 (𝓡 ⧸ P) (𝓡 ⧸ Q) := by
    rw [hchi, ← heq]
    exact_mod_cast hmult
  exact_mod_cast this

end SerrePositivity.DiagonalRing
