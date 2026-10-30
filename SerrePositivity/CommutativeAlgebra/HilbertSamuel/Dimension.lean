module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Polynomial
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.PolynomialGrowth
public import Mathlib.RingTheory.Finiteness.Ideal
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Existence
public import SerrePositivity.CommutativeAlgebra.RegularSequence

/-! # Samuel の次元定理

## 概要

Noether 局所環 `R` と有限加群 `M` について、Samuel 多項式の次数は `dim M` に等しい
（Atiyah–Macdonald 11.14 の一部）。正則元で割ると次数が一つ下がること、Artin–Rees による増大の比較、
次元を持ち上げる系を含む。

## 方針

上界は生成元の個数（パラメータ系）による。下界は正則元・パラメータで割ったときの増大の比較と Artin–Rees
（正則元の逆像に対する版、`exists_comap_pow_smul_top_le`）による。

## 規約

名前空間は `HilbertSamuel`。

## 使われ方

正則局所環の随伴次数環の表示の単射性（`RegularLocalRing/Graded`）と、パラメータの冪の長さの評価（B2）。
-/

@[expose] public noncomputable section

universe u v w

section ArtinRees

open scoped Pointwise

namespace SerrePositivity.HilbertSamuel

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The quotient by a scalar gives a short exact sequence in each filtration
degree; the first term is the quotient by the inverse image under multiplication. -/
lemma samuelFunction_quotSMulTop_eq (I : Ideal R) (x : R) (n : ℕ) :
    samuelFunction R I M n =
      Module.length R (M ⧸ (I ^ n • ⊤ : Submodule R M).comap
        (LinearMap.lsmul R M x)) + samuelFunction R I (QuotSMulTop x M) n := by
  let N : Submodule R M := I ^ n • ⊤
  let f : M →ₗ[R] M := LinearMap.lsmul R M x
  let P : Submodule R M := N.comap f
  let T : Submodule R M := x • ⊤
  let q : M →ₗ[R] QuotSMulTop x M := T.mkQ
  let U : Submodule R (QuotSMulTop x M) := I ^ n • ⊤
  let a : M ⧸ P →ₗ[R] M ⧸ N := P.mapQ N f le_rfl
  let b : M ⧸ N →ₗ[R] QuotSMulTop x M ⧸ U :=
    N.mapQ U q (Submodule.smul_top_le_comap_smul_top (I ^ n) q)
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker (P.mapQ N f le_rfl) = ⊥
    rw [Submodule.ker_mapQ, Submodule.mkQ_map_self]
  have hb : Function.Surjective b := by
    intro z
    obtain ⟨z, rfl⟩ := U.mkQ_surjective z
    obtain ⟨z, rfl⟩ := T.mkQ_surjective z
    exact ⟨N.mkQ z, rfl⟩
  have hf : LinearMap.range f = T := by
    change LinearMap.range (LinearMap.lsmul R M x) = x • ⊤
    rw [Submodule.pointwise_smul_def, Submodule.map_top]
    rfl
  have hab : Function.Exact a b := by
    apply LinearMap.exact_iff.mpr
    symm
    change LinearMap.range (P.mapQ N f le_rfl) = LinearMap.ker
      (N.mapQ U q (Submodule.smul_top_le_comap_smul_top (I ^ n) q))
    rw [Submodule.range_mapQ, Submodule.ker_mapQ, hf,
      Submodule.comap_smul_top_of_surjective (I ^ n) q (T.mkQ_surjective),
      Submodule.map_sup]
    change T.map N.mkQ = N.map N.mkQ ⊔ (LinearMap.ker q).map N.mkQ
    rw [show LinearMap.ker q = T from Submodule.ker_mkQ T,
      Submodule.mkQ_map_self, bot_sup_eq]
  exact Module.length_eq_add_of_exact a b ha hb hab

/-- Artin–Rees bounds the inverse image of powers by multiplication by a
regular element, with a strictly positive shift. -/
lemma exists_comap_pow_smul_top_le [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (x : R) (hx : IsSMulRegular M x) :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      (I ^ n • ⊤ : Submodule R M).comap (LinearMap.lsmul R M x) ≤
        I ^ (n - c) • ⊤ := by
  let f : M →ₗ[R] M := LinearMap.lsmul R M x
  have hf : Function.Injective f := hx
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k + 1, by omega, fun n hn => ?_⟩
  have hkn : k ≤ n := by omega
  have he : (I ^ n • ⊤ : Submodule R M).comap f ≤ I ^ (n - k) • ⊤ := by
    apply (Submodule.map_le_map_iff_of_injective hf _ _).mp
    rw [Submodule.map_comap_eq, inf_comm, hk n hkn,
      Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  exact he.trans (Submodule.smul_mono
    (Ideal.pow_le_pow_right (by omega : n - (k + 1) ≤ n - k)) le_rfl)

/-- Killing a regular element lowers the Samuel growth by one bounded
difference. No subtraction, and no finite-length hypotheses, are needed. -/
theorem exists_samuelFunction_quotSMulTop_add_le [IsNoetherianRing R]
    [Module.Finite R M] (I : Ideal R) (x : R) (hx : IsSMulRegular M x) :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      samuelFunction R I (QuotSMulTop x M) n + samuelFunction R I M (n - c) ≤
        samuelFunction R I M n := by
  obtain ⟨c, hc, h⟩ := exists_comap_pow_smul_top_le I x hx
  refine ⟨c, hc, fun n hn => ?_⟩
  have hl := Module.length_le_of_surjective (Submodule.factor (h n hn))
    (Submodule.factor_surjective (h n hn))
  calc
    _ ≤ samuelFunction R I (QuotSMulTop x M) n +
        Module.length R (M ⧸ (I ^ n • ⊤ : Submodule R M).comap
          (LinearMap.lsmul R M x)) := add_le_add_right hl _
    _ = samuelFunction R I M n := by
      rw [add_comm]
      exact (samuelFunction_quotSMulTop_eq (M := M) I x n).symm

end SerrePositivity.HilbertSamuel

end ArtinRees

section RegularGrowth

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

/-- Transfer an additive inequality between finite extended natural numbers to rational
numbers. This is the numerical passage from length inequalities to polynomial values. -/
theorem toNat_rat_add_le_of_add_le {a b c : ℕ∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hc : c ≠ ⊤) (h : a + b ≤ c) :
    (a.toNat : ℚ) + (b.toNat : ℚ) ≤ (c.toNat : ℚ) := by
  have hn := ENat.toNat_le_toNat h hc
  rw [ENat.toNat_add ha hb] at hn
  exact_mod_cast hn

variable {R M N : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]

/-- Any nonzero finite module with Samuel function bounded by that of a regular quotient
has strictly lower polynomial degree than the original module. -/
theorem IsSamuelPoly.natDegree_lt_of_le_regular_quotient
    {I : Ideal R} (hI : I.radical = maximalIdeal R) {P Q : ℚ[X]}
    (hP : IsSamuelPoly R I M P) (hQ : IsSamuelPoly R I N Q)
    (x : R) (hx : IsSMulRegular M x)
    (hN : ∀ n : ℕ, samuelFunction R I N n ≤
      samuelFunction R I (QuotSMulTop x M) n) :
    Q.natDegree < P.natDegree := by
  obtain ⟨c, hc, hdiff⟩ := exists_samuelFunction_quotSMulTop_add_le I x hx
  apply natDegree_lt_of_eventually_eval_add_shift_le
    (hQ.leadingCoeff_pos_of_nontrivial hI) c
  obtain ⟨k, hk⟩ := eventually_atTop.mp hP
  have hPshift : ∀ᶠ n : ℕ in atTop,
      samuelFunction R I M (n - c) ≠ ⊤ ∧
        ((samuelFunction R I M (n - c)).toNat : ℚ) = P.eval ((n - c : ℕ) : ℚ) := by
    apply eventually_atTop.mpr
    refine ⟨k + c, fun n hn => hk (n - c) ?_⟩
    omega
  filter_upwards [hP, hQ, hPshift, eventually_ge_atTop c] with n hnP hnQ hnPc hnc
  rw [← hnQ.2, ← hnPc.2, ← hnP.2]
  apply toNat_rat_add_le_of_add_le hnQ.1 hnPc.1 hnP.1
  exact (add_le_add (hN n) le_rfl).trans (hdiff n hnc)

end SerrePositivity.HilbertSamuel

end RegularGrowth

section GrowthComparison

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

variable (R : Type u) [CommRing R]

/-- A power containment gives a linear change of index in the Samuel length bound. -/
theorem samuelFunction_le_mul_of_pow_le
    (M : Type u) [AddCommGroup M] [Module R M]
    {I J : Ideal R} {c : ℕ} (hJI : J ^ c ≤ I) (n : ℕ) :
    samuelFunction R I M n ≤ samuelFunction R J M (c * n) := by
  have h := samuelFunction_antitone_ideal R M n hJI
  change samuelFunction R I M n ≤ samuelFunction R (J ^ c) M n at h
  rwa [samuelFunction_pow] at h

variable [IsNoetherianRing R] [IsLocalRing R]

/-- The selected Samuel polynomial represents the length function of any finite module over
a Noetherian local ring, for an ideal whose radical is the maximal ideal. -/
theorem isSamuelPoly_poly_of_radical
    (I : Ideal R) (hI : I.radical = maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsSamuelPoly R I M (poly R I M) := by
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  obtain ⟨P, hP, _⟩ := exists_isSamuelPoly R I hI x hx.symm M
  exact isSamuelPoly_poly R ⟨P, hP⟩

/-- A power containment bounds the degree of one Samuel polynomial by the other. -/
theorem natDegree_poly_le_of_pow_le
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) {c : ℕ} (hc : 0 < c) (hJI : J ^ c ≤ I) :
    (poly R I R).natDegree ≤ (poly R J R).natDegree := by
  have hP := isSamuelPoly_poly_of_radical R I hI R
  have hQ := isSamuelPoly_poly_of_radical R J hJ R
  have hQcn : ∀ᶠ n : ℕ in atTop,
      samuelFunction R J R (c * n) ≠ ⊤ ∧
        ((samuelFunction R J R (c * n)).toNat : ℚ) = (poly R J R).eval ((c * n : ℕ) : ℚ) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hQ
    apply eventually_atTop.mpr
    exact ⟨N, fun n hn => hN (c * n) (hn.trans (Nat.le_mul_of_pos_left n hc))⟩
  apply natDegree_le_of_eventually_eval_affine_le
    (hP.leadingCoeff_pos R hI) c 0
  filter_upwards [hP, hQcn] with n hnI hnJ
  simp only [Nat.add_zero]
  rw [← hnI.2, ← hnJ.2]
  exact_mod_cast ENat.toNat_le_toNat (samuelFunction_le_mul_of_pow_le R R hJI n) hnJ.1

/-- Increasing a primary ideal cannot increase the degree of its Samuel polynomial. -/
theorem natDegree_poly_antitone_of_le
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) (hIJ : I ≤ J) :
    (poly R J R).natDegree ≤ (poly R I R).natDegree :=
  natDegree_poly_le_of_pow_le R J I hJ hI (c := 1) (by decide) (by simpa using hIJ)

/-- Ideals with maximal radical contain positive powers of one another. -/
theorem exists_pos_pow_le_of_radical_eq
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) :
    ∃ c : ℕ, 0 < c ∧ J ^ c ≤ I := by
  have hle : J ≤ I.radical := Ideal.le_radical.trans_eq (hJ.trans hI.symm)
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle J.fg_of_isNoetherianRing
  exact ⟨c + 1, Nat.succ_pos c, (Ideal.pow_le_pow_right (Nat.le_succ c)).trans hc⟩

/-- The Samuel polynomial degree is independent of the ideal with maximal radical. This
comparison is independent of its later identification with Krull dimension. -/
theorem natDegree_poly_eq_of_radical_eq
    (I J : Ideal R) (hI : I.radical = maximalIdeal R)
    (hJ : J.radical = maximalIdeal R) :
    (poly R I R).natDegree = (poly R J R).natDegree := by
  obtain ⟨c, hc, hJI⟩ := exists_pos_pow_le_of_radical_eq R I J hI hJ
  obtain ⟨d, hd, hIJ⟩ := exists_pos_pow_le_of_radical_eq R J I hJ hI
  exact le_antisymm (natDegree_poly_le_of_pow_le R I J hI hJ hc hJI)
    (natDegree_poly_le_of_pow_le R J I hJ hI hd hIJ)

end SerrePositivity.HilbertSamuel

end GrowthComparison

section Dimension

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A generating family bounds the degree of the selected Samuel polynomial. -/
theorem natDegree_poly_le_of_generators (I : Ideal R)
    (hI : I.radical = maximalIdeal R) {s : ℕ} (x : Fin s → R)
    (hx : Ideal.span (Set.range x) = I)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (poly R I M).natDegree ≤ s := by
  obtain ⟨P, hP, hdeg⟩ := exists_isSamuelPoly R I hI x hx.symm M
  rwa [poly_eq R hP]

/-- Parameters chosen inside `I` bound its Samuel degree by the ring dimension. -/
theorem natDegree_poly_le_dim (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    (poly R I R).natDegree ≤ dimToNat (ringKrullDim R) := by
  obtain ⟨z, hz, hrad⟩ := exists_radical_span_eq_maximalIdeal_of_radical_eq R I hI
  let J := Ideal.span (Set.range z)
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hz i)
  exact (natDegree_poly_antitone_of_le R J I hrad hI hJI).trans
    (natDegree_poly_le_of_generators R J hrad z rfl R)

/-- A prime quotient cannot have larger Samuel degree than the original ring. -/
theorem natDegree_poly_primeQuotient_le (I : Ideal R)
    (hI : I.radical = maximalIdeal R) (p : PrimeSpectrum R) :
    (poly R I (R ⧸ p.asIdeal)).natDegree ≤ (poly R I R).natDegree := by
  have hP := isSamuelPoly_poly_of_radical R I hI (R ⧸ p.asIdeal)
  have hQ := isSamuelPoly_poly_of_radical R I hI R
  apply natDegree_le_of_eventually_eval_le
    (hP.leadingCoeff_pos_of_nontrivial hI)
  filter_upwards [hP, hQ] with n hnP hnQ
  rw [← hnP.2, ← hnQ.2]
  exact_mod_cast ENat.toNat_le_toNat
    (samuelFunction_le_of_surjective I p.asIdeal.mkQ p.asIdeal.mkQ_surjective n) hnQ.1

/-- Strict inclusion of prime ideals strictly decreases the Samuel degree of their quotients. -/
theorem natDegree_poly_primeQuotient_lt (I : Ideal R)
    (hI : I.radical = maximalIdeal R) (p q : PrimeSpectrum R) (hpq : p < q) :
    (poly R I (R ⧸ q.asIdeal)).natDegree < (poly R I (R ⧸ p.asIdeal)).natDegree := by
  obtain ⟨x, hxq, hxp⟩ := Set.exists_of_ssubset
    (show (p.asIdeal : Set R) ⊂ q.asIdeal from hpq)
  exact (isSamuelPoly_poly_of_radical R I hI (R ⧸ p.asIdeal)).natDegree_lt_of_le_regular_quotient
    hI (isSamuelPoly_poly_of_radical R I hI (R ⧸ q.asIdeal)) x
    (isSMulRegular_quotient_of_notMem_prime p.asIdeal hxp)
    (samuelFunction_idealQuotient_le_quotSMulTop I p.asIdeal q.asIdeal hpq.le x hxq)

/-- Every strict prime chain is bounded by the Samuel degree of its initial prime quotient. -/
theorem primeChain_length_le_natDegree (I : Ideal R)
    (hI : I.radical = maximalIdeal R) (c : LTSeries (PrimeSpectrum R)) :
    c.length ≤ (poly R I (R ⧸ c.head.asIdeal)).natDegree := by
  induction c using RelSeries.inductionOn with
  | singleton p => simp
  | cons c p hp ih =>
    simp only [RelSeries.cons_length, RelSeries.head_cons]
    exact Nat.succ_le_of_lt (ih.trans_lt (natDegree_poly_primeQuotient_lt R I hI p c.head hp))

/-- Prime chains give the lower bound for the Samuel polynomial degree. -/
theorem dim_le_natDegree_poly (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    dimToNat (ringKrullDim R) ≤ (poly R I R).natDegree := by
  have hdim : ringKrullDim R ≤ ((poly R I R).natDegree : WithBot ℕ∞) := by
    change (⨆ c : LTSeries (PrimeSpectrum R), (c.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun c => ?_
    exact_mod_cast (primeChain_length_le_natDegree R I hI c).trans
      (natDegree_poly_primeQuotient_le R I hI c.head)
  rw [← natCast_dimToNat_ringKrullDim R] at hdim
  exact_mod_cast hdim

/-- **Hilbert–Samuel dimension theorem**: the Samuel degree of the ring is its Krull
dimension (Atiyah–Macdonald, Theorem 11.14). Parameters give the upper bound;
Artin–Rees and induction on prime chains give the lower bound. -/
theorem natDegree_poly_eq_dim (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    (poly R I R).natDegree = dimToNat (ringKrullDim R) :=
  le_antisymm (natDegree_poly_le_dim R I hI) (dim_le_natDegree_poly R I hI)

end SerrePositivity.HilbertSamuel

end Dimension
