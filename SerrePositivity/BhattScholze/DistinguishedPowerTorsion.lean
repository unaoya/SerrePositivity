module

public import SerrePositivity.BhattScholze.DistinguishedTorsion

/-! # distinguished元の冪商の有界pねじれ

著者公開版Lemma 2.34(2)を、正則なdistinguished元の冪商に反復適用する。
A/(dⁿ)のp冪ねじれはpⁿで消える。商の古典的・導来完備性は結論しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 正則なdistinguished元dについて、dⁿ∣pᴺfならdⁿ∣pⁿf。 -/
theorem IsDistinguished.pow_dvd_p_pow_mul_of_dvd_p_pow_mul
    {D : DeltaStructure p A} [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) {d : A}
    (hd : D.IsDistinguished d) (hdreg : Function.Injective (fun x : A ↦ d * x))
    (n N : ℕ) (f : A) (hdf : d ^ n ∣ (p : A) ^ N * f) :
    d ^ n ∣ (p : A) ^ n * f := by
  induction n generalizing N f with
  | zero => simp
  | succ n ih =>
    by_cases hN : N = 0
    · subst N
      simpa only [pow_zero, one_mul] using hdf.mul_left ((p : A) ^ (n + 1))
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
      obtain ⟨g, hg⟩ := hdf
      have hdpf : d ∣ (p : A) * f := hd.dvd_p_mul_of_dvd_p_pow_mul hp
        (m + 1) (Nat.succ_pos m) f (by
          refine ⟨d ^ n * g, ?_⟩
          rw [hg, pow_succ]
          ring)
      obtain ⟨h, hh⟩ := hdpf
      have he : (p : A) ^ m * h = d ^ n * g := by
        apply hdreg
        change d * ((p : A) ^ m * h) = d * (d ^ n * g)
        calc
          _ = (p : A) ^ m * (d * h) := by ring
          _ = (p : A) ^ m * ((p : A) * f) := by rw [hh]
          _ = (p : A) ^ (m + 1) * f := by rw [pow_succ]; ring
          _ = d ^ (n + 1) * g := hg
          _ = _ := by rw [pow_succ]; ring
      obtain ⟨k, hk⟩ := ih m h ⟨g, he⟩
      refine ⟨k, ?_⟩
      calc
        (p : A) ^ (n + 1) * f = d * ((p : A) ^ n * h) := by
          rw [pow_succ, mul_assoc, hh]
          ring
        _ = d * (d ^ n * k) := by rw [hk]
        _ = d ^ (n + 1) * k := by rw [pow_succ]; ring

/-- 正則なdistinguished元の冪商A/(dⁿ)のp冪ねじれはpⁿで消える。 -/
theorem IsDistinguished.quotient_power_p_pow_torsion_killed_by_p_pow
    {D : DeltaStructure p A} [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) {d : A}
    (hd : D.IsDistinguished d) (hdreg : Function.Injective (fun x : A ↦ d * x))
    (n N : ℕ) (x : A ⧸ Ideal.span {d ^ n})
    (hx : (p : A ⧸ Ideal.span {d ^ n}) ^ N * x = 0) :
    (p : A ⧸ Ideal.span {d ^ n}) ^ n * x = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hdf : d ^ n ∣ (p : A) ^ N * f := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, map_pow, map_natCast] using hx
  have h := hd.pow_dvd_p_pow_mul_of_dvd_p_pow_mul hp hdreg n N f hdf
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  simpa only [map_mul, map_pow, map_natCast] using hz

/-- p進分離な完全δ環のdistinguished冪商のp冪ねじれはpⁿで消える。
完全性からp正則性とmod p被約性、分離性からd正則性を供給する。 -/
theorem IsPerfect.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    {D : DeltaStructure p A} (hD : D.IsPerfect)
    [IsHausdorff (Ideal.span {(p : A)}) A] {d : A} (hd : D.IsDistinguished d)
    (n N : ℕ) (x : A ⧸ Ideal.span {d ^ n})
    (hx : (p : A ⧸ Ideal.span {d ^ n}) ^ N * x = 0) :
    (p : A ⧸ Ideal.span {d ^ n}) ^ n * x = 0 := by
  let := hD.perfectRing_mod_p
  let : IsReduced (A ⧸ Ideal.span {(p : A)}) :=
    (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr (by
      intro y hy
      exact (PerfectRing.bijective_frobenius (R := A ⧸ Ideal.span {(p : A)}) (p := p)).1
        (by simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using hy))
  exact hd.quotient_power_p_pow_torsion_killed_by_p_pow hD.p_mul_injective
    (hD.distinguished_mul_injective hd) n N x hx

end SerrePositivity.BhattScholze.DeltaStructure
