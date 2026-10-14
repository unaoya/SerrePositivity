module

public import SerrePositivity.BhattScholze.DistinguishedRegular

/-! # distinguished商の有界p冪ねじれ

BS著者公開版Lemma 2.34(2)。p正則でmod pが被約なδ環をdistinguished元で割ると、
商の任意のp冪ねじれはpで消える。導来完備性やperfectoid性は仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- pを零に送る環準同型ではδ(p²f)の像は零。δ積公式の各項から直接従う。 -/
theorem map_delta_p_sq_mul {B : Type*} [CommRing B] (D : DeltaStructure p A)
    (q : A →+* B) (hqp : q (p : A) = 0) (f : A) : q (D.delta ((p : A) ^ 2 * f)) = 0 := by
  rw [show (p : A) ^ 2 * f = (p : A) * ((p : A) * f) by ring, D.delta_mul]
  simp only [map_add, map_mul, map_pow, hqp, zero_pow (Fact.out : p.Prime).ne_zero,
    zero_mul, mul_zero, add_zero]

/-- p²f=gdでdがdistinguished、mod pが被約ならpはgを割る。
δとφの等式をmod pで組み合わせてg^(2p)=0を得る（BS Lemma 2.34(2)の核心）。 -/
theorem p_dvd_of_p_sq_mul_eq_mul_distinguished (D : DeltaStructure p A)
    [IsReduced (A ⧸ Ideal.span {(p : A)})] {d f g : A}
    (hd : D.IsDistinguished d) (he : (p : A) ^ 2 * f = g * d) : (p : A) ∣ g := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  have hqp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hδ : q g ^ p * q (D.delta d) + q (D.delta g) * q d ^ p = 0 := by
    have h := congrArg (fun x ↦ q (D.delta x)) he
    rw [D.map_delta_p_sq_mul q hqp f, D.delta_mul] at h
    simpa only [map_add, map_mul, map_pow, hqp, zero_mul, mul_zero, add_zero] using h.symm
  have hφ : q g ^ p * q d ^ p = 0 := by
    have h := congrArg (fun x ↦ q (D.frobeniusLift x)) he
    rw [map_mul, map_pow, map_natCast, map_mul, map_mul, map_pow, hqp,
      zero_pow (by decide : 2 ≠ 0), zero_mul, map_mul,
      D.map_frobeniusLift_of_map_p_eq_zero q hqp g,
      D.map_frobeniusLift_of_map_p_eq_zero q hqp d] at h
    exact h.symm
  have hnil : q g ^ (p + p) = 0 := by
    apply (hd.map q).mul_right_eq_zero.mp
    rw [pow_add]
    linear_combination q g ^ p * hδ - q (D.delta g) * hφ
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero hnil))

/-- dがp²fを割ればpfを割る。p正則性で共通のp因子を消去する。 -/
theorem IsDistinguished.dvd_p_mul_of_dvd_p_sq_mul {D : DeltaStructure p A}
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) {d f : A}
    (hd : D.IsDistinguished d) (hdf : d ∣ (p : A) ^ 2 * f) : d ∣ (p : A) * f := by
  obtain ⟨g, hg⟩ := hdf
  obtain ⟨r, hr⟩ := D.p_dvd_of_p_sq_mul_eq_mul_distinguished hd (by
    rw [hg]; exact mul_comm d g)
  refine ⟨r, ?_⟩
  apply hp
  change (p : A) * ((p : A) * f) = (p : A) * (d * r)
  calc
    _ = (p : A) ^ 2 * f := by ring
    _ = d * g := hg
    _ = _ := by rw [hr]; ring

/-- distinguished元dによる商のp冪ねじれはpで消える、という可除性表示。
正のすべての指数Nについてd∣p^Nfからd∣pfを得る。 -/
theorem IsDistinguished.dvd_p_mul_of_dvd_p_pow_mul {D : DeltaStructure p A}
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) {d : A}
    (hd : D.IsDistinguished d) (N : ℕ) (hN : 0 < N) (f : A)
    (hdf : d ∣ (p : A) ^ N * f) : d ∣ (p : A) * f := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction n generalizing f with
  | zero => simpa only [Nat.succ_eq_add_one, zero_add, pow_one] using hdf
  | succ n ih =>
      have hstep : d ∣ (p : A) * ((p : A) ^ n * f) :=
        hd.dvd_p_mul_of_dvd_p_sq_mul hp (by
          convert hdf using 1
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega)
      apply ih f (Nat.succ_pos n)
      convert hstep using 1
      rw [pow_succ]
      ring

/-- 商A/(d)で任意のp冪により零化される元はpで零化される（BS Lemma 2.34(2)）。
N=0も含む。商のp進完備性を仮定しない。 -/
theorem IsDistinguished.quotient_p_pow_torsion_killed_by_p {D : DeltaStructure p A}
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) {d : A}
    (hd : D.IsDistinguished d) (N : ℕ) (x : A ⧸ Ideal.span {d})
    (hx : (p : A ⧸ Ideal.span {d}) ^ N * x = 0) : (p : A ⧸ Ideal.span {d}) * x = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  by_cases hN : N = 0
  · subst N
    simpa only [pow_zero, one_mul, mul_zero] using
      congrArg (fun y ↦ (p : A ⧸ Ideal.span {d}) * y) hx
  · have hdf : d ∣ (p : A) ^ N * f := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, map_pow, map_natCast] using hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr
      (hd.dvd_p_mul_of_dvd_p_pow_mul hp N (Nat.pos_of_ne_zero hN) f hdf)

/-- 完全δ環のdistinguished商のp冪ねじれはpで消える。
完全δ構造からp正則性とmod pの被約性を供給し、完備性は要求しない。 -/
theorem IsPerfect.distinguished_quotient_p_pow_torsion_killed_by_p
    {D : DeltaStructure p A} (hD : D.IsPerfect) {d : A} (hd : D.IsDistinguished d)
    (N : ℕ) (x : A ⧸ Ideal.span {d}) (hx : (p : A ⧸ Ideal.span {d}) ^ N * x = 0) :
    (p : A ⧸ Ideal.span {d}) * x = 0 := by
  let := hD.perfectRing_mod_p
  let : IsReduced (A ⧸ Ideal.span {(p : A)}) :=
    (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr (by
      intro y hy
      exact (PerfectRing.bijective_frobenius (R := A ⧸ Ideal.span {(p : A)}) (p := p)).1
        (by simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using hy))
  exact hd.quotient_p_pow_torsion_killed_by_p hD.p_mul_injective N x hx

end SerrePositivity.BhattScholze.DeltaStructure
