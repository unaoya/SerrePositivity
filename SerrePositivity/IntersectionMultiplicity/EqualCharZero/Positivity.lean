module

public import SerrePositivity.IntersectionMultiplicity.EqualCharZero.Tor
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Formula
public import Mathlib.RingTheory.LocalRing.Quotient
public import SerrePositivity.IntersectionMultiplicity.Additivity
public import SerrePositivity.CommutativeAlgebra.CharZeroCoefficientField
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # 剰余標数零での Serre の正値性

## 概要

冪級数環 k[[X_1, …, X_d]] の素イデアル P, Q で R/P ⊗ R/Q が有限長かつ dim R/P + dim R/Q = d なら χ^R(R/P, R/Q) > 0（対角線論法）。これと完備化・Cohen の構造定理・デヴィサージュから、剰余体が標数零の正則局所環での正値性を示す。

## 方針

平坦な完備化は長さ・次元・正則性・χ を保ち、完備なら標数零の係数体を持つ冪級数環になる。素イデアル商へはデヴィサージュで帰着する。

## 規約

消滅には `intersectionVanishing_of_adams`（証明済み）を使う。

## 使われ方

Paper の主定理（等標数零の場合）。
-/

@[expose] public noncomputable section

universe u

section DiagonalPositivityPart

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
  have heq := KoszulMultiplicity.multiplicity_eq_chiOrd_koszul z hsop
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

end DiagonalPositivityPart

section EqualCharZeroPositivityPart

open IsLocalRing TensorProduct

namespace SerrePositivity

/-- **Cohen 同型（標数零）**：剰余体が標数零の完備正則局所環 `R` は、剰余体上の冪級数環と同型。 -/
theorem exists_mvPowerSeries_ringEquiv_of_charZero (R : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] :
    ∃ (K : Type u) (_ : Field K) (d : ℕ), Nonempty (MvPowerSeries (Fin d) K ≃+* R) := by
  classical
  obtain ⟨g, hg⟩ := exists_residue_section_of_charZero R
  obtain ⟨d, x, hrange, _, hdim⟩ := exists_regular_generators_fin R
  have hx : ∀ i, x i ∈ maximalIdeal R := fun i ↦ hrange ▸ Ideal.subset_span ⟨i, rfl⟩
  let c := adicPowerSeriesEval g (maximalIdeal R) x hx
  have hsurj : Function.Surjective c := by
    apply adicPowerSeriesEval_surjective g (maximalIdeal R) x hx hrange
    intro a
    exact ⟨a, RingHom.congr_fun hg a⟩
  let := isRegularLocalRing_mvPowerSeries_fin (ResidueField R) d
  let : IsDomain (MvPowerSeries (Fin d) (ResidueField R)) := isDomain_of_isRegularLocalRing _
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hf0
    have hdrop := ringKrullDim_succ_le_of_surjective c hsurj
      (mem_nonZeroDivisors_iff_ne_zero.mpr hf0) hf
    rw [ringKrullDim_mvPowerSeries_field, hdim] at hdrop
    have : (d : WithBot ℕ∞) + 1 ≤ d := hdrop
    have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : ℕ) := by exact_mod_cast this
    have := WithBot.coe_le_coe.mp h'
    norm_cast at this
    omega
  exact ⟨ResidueField R, inferInstance, d, ⟨RingEquiv.ofBijective c ⟨hinj, hsurj⟩⟩⟩

/-- 完備な剰余標数零の正則局所環での正値性。 -/
theorem chi_pos_of_complete_residueCharZero (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  obtain ⟨k, _, d, ⟨e⟩⟩ := exists_mvPowerSeries_ringEquiv_of_charZero R
  let B := MvPowerSeries (Fin d) k
  let : Algebra R B := e.symm.toRingHom.toAlgebra
  have : Module.Flat R B :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective e.symm.bijective)
  have hm : (maximalIdeal R).map (algebraMap R B) = maximalIdeal B :=
    map_ringEquiv_maximalIdeal e.symm
  rw [← chi_baseChange_of_map_maximalIdeal R B hm M N]
  apply chi_pos_of_prime_quotients (DiagonalRing.chi_pos_of_prime k d) (B ⊗[R] M) (B ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R B hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R B hm M,
      supportDim_baseChange_of_map_maximalIdeal R B hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R B hm]

/-- **剰余標数零の Serre の正値性**：剰余体が標数零の正則局所環 `R` と有限生成加群 `M, N` について、
`M ⊗ N` が有限長で `dim M + dim N = dim R` なら `χ^R(M, N) > 0`。完備化で完備な場合に帰着する。 -/
theorem chi_pos_of_residueCharZero (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [CharZero (ResidueField R)]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  let S := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing S := isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    AdicCompletion.maximalIdeal_eq_map.symm
  let : IsRegularLocalRing S := isRegularLocalRing_of_flat_of_map_maximalIdeal R S hm
  let : CharZero (ResidueField S) := charZero_of_injective_ringHom
    (f := ResidueField.map (algebraMap R S)) (RingHom.injective _)
  rw [← chi_baseChange_of_map_maximalIdeal R S hm M N]
  apply chi_pos_of_complete_residueCharZero S (S ⊗[R] M) (S ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R S hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R S hm M,
      supportDim_baseChange_of_map_maximalIdeal R S hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R S hm]

end SerrePositivity

end EqualCharZeroPositivityPart
