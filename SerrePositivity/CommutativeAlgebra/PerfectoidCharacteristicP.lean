module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import Mathlib.RingTheory.WittVector.Complete
public import SerrePositivity.CommutativeAlgebra.PerfectionIdempotents
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # 標数 p の perfectoid 環の完全性の基礎

BMS Example 3.15 では、θ の核の元 p が distinguished であることから核を生成し、
標数 p の perfectoid 環を完全な傾斜と同定する。本ファイルでは、この議論に必要な
純粋な Witt ベクトルと逆極限の補題を整備する。追加の引用は用いない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open MvPolynomial

/-- 標数 p では、単項な Fontaine 核は p 自身で生成される。 -/
theorem ker_fontaineTheta_eq_span_p_of_charP
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p))} := by
  let K := RingHom.ker (WittVector.fontaineTheta S p)
  let : K.IsPrincipal := hker
  let ξ : WittVector p (PreTilt S p) := Submodule.IsPrincipal.generator K
  have hgen : Ideal.span {ξ} = K := Ideal.span_singleton_generator K
  have hξ : ξ ∈ K := Submodule.IsPrincipal.generator_mem K
  have hp : (p : WittVector p (PreTilt S p)) ∈ K := by
    simp [K, RingHom.mem_ker, CharP.cast_eq_zero]
  have hdiv : ξ ∣ (p : WittVector p (PreTilt S p)) := by
    apply Ideal.mem_span_singleton.mp
    rwa [hgen]
  obtain ⟨a, ha⟩ := hdiv
  have hzero : ξ.coeff 0 * a.coeff 0 = 0 := by
    have hh := congrArg (fun z : WittVector p (PreTilt S p) => z.coeff 0) ha
    simpa [WittVector.mul_coeff_zero, WittVector.coeff_p_zero] using hh.symm
  have hsplit : ξ.coeff 0 ^ p * a.coeff 1 + ξ.coeff 1 * a.coeff 0 ^ p = 1 := by
    have hh := congrArg (fun z : WittVector p (PreTilt S p) => z.coeff 1) ha
    simpa [witt_mul_coeff_one, WittVector.coeff_p_one, CharP.cast_eq_zero] using hh.symm
  have hproj : PreTilt.coeff 0 (ξ.coeff 0) = 0 := by
    rw [← WittVector.mk_fontaineTheta]
    have hh : WittVector.fontaineTheta S p ξ = 0 := hξ
    rw [hh, map_zero]
  have haunit : IsUnit (a.coeff 0) :=
    isUnit_of_coefficient_equations (PreTilt.coeff 0)
      (fun e he hz => perfection_idempotent_eq_zero_of_coeff_zero (ModP S p) p e he hz)
      (ξ.coeff 0) (a.coeff 0) (a.coeff 1) (ξ.coeff 1) p
      (Fact.out : p.Prime).pos hzero hsplit hproj
  have hξzero : ξ.coeff 0 = 0 := by
    exact haunit.mul_right_eq_zero.mp (by simpa only [mul_comm] using hzero)
  apply le_antisymm
  · change K ≤ _
    rw [← hgen]
    apply Ideal.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact (WittVector.mem_span_p_iff_coeff_zero_eq_zero ξ).mpr hξzero
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp)

/-- 標数 p の整 perfectoid 環の Frobenius は全単射。
単項核の仮定から実際に θ の核=(p) を導き、W(tilt)/(p)≃tilt を利用する。 -/
theorem IsIntegralPerfectoid.perfectRing_of_charP
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (hS : IsIntegralPerfectoid S p) : PerfectRing S p := by
  rcases hS with hsub | ⟨hp, hc, _, hF, hker⟩
  · let : Subsingleton S := hsub
    exact ⟨⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ x⟩⟩⟩
  · let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    let := hc
    have hθ : Function.Surjective (WittVector.fontaineTheta S p) :=
      surjective_fontaineTheta hF
    have hK := ker_fontaineTheta_eq_span_p_of_charP S p hker
    let E : PreTilt S p ≃+* S :=
      (WittVector.quotientPEquiv).symm.trans
        ((Ideal.quotEquivOfEq hK.symm).trans (RingHom.quotientKerEquivOfSurjective hθ))
    refine ⟨⟨?_, ?_⟩⟩
    · intro x y hxy
      apply E.symm.injective
      apply injective_pow_p (PreTilt S p) p
      simpa only [← map_pow] using congrArg E.symm hxy
    · intro x
      obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := PreTilt S p) (p := p)).2 (E.symm x)
      refine ⟨E y, ?_⟩
      change y ^ p = E.symm x at hy
      change (E y) ^ p = x
      rw [← map_pow, hy, E.apply_symm_apply]

/-- 完全な標数 p の可換環は被約。 -/
theorem isReduced_of_perfectRing_charP
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p] [PerfectRing S p] :
    IsReduced S := by
  apply (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr
  intro x hx
  apply injective_pow_p S p
  simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using hx

/-- 標数 p の整 perfectoid 環は被約。完全性を追加仮定とせず、四条件から導く。 -/
theorem IsIntegralPerfectoid.isReduced_of_charP
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (hS : IsIntegralPerfectoid S p) : IsReduced S := by
  let := hS.perfectRing_of_charP S p
  exact isReduced_of_perfectRing_charP S p

/-- p=0 と整 perfectoid の四条件から直接完全性を得る。零環も含む。 -/
theorem IsIntegralPerfectoid.perfectRing_of_p_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    (hS : IsIntegralPerfectoid S p) (hp : (p : S) = 0) : PerfectRing S p := by
  rcases subsingleton_or_nontrivial S with hsub | hnontrivial
  · let : Subsingleton S := hsub
    exact ⟨⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ x⟩⟩⟩
  · let : Nontrivial S := hnontrivial
    let : CharP S p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    exact hS.perfectRing_of_charP S p

/-- p=0 の整 perfectoid 環は被約。標数クラスは追加仮定にせず内部で構成する。 -/
theorem IsIntegralPerfectoid.isReduced_of_p_eq_zero
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    (hS : IsIntegralPerfectoid S p) (hp : (p : S) = 0) : IsReduced S := by
  rcases subsingleton_or_nontrivial S with hsub | hnontrivial
  · let : Subsingleton S := hsub
    infer_instance
  · let : Nontrivial S := hnontrivial
    let : CharP S p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    exact hS.isReduced_of_charP S p

end SerrePositivity
