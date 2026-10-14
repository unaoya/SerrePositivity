module

public import SerrePositivity.BhattScholze.Distinguished
public import SerrePositivity.BhattScholze.DeltaRankOne
public import SerrePositivity.BhattScholze.PerfectDeltaModP

/-! # distinguished元の非零因子性

BS著者公開版Lemma 2.34(1)。mod pの被約性から零因子のp可除性を導き、
pの消去とp進分離性により零因子を零と判定する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- mod pが被約なら、distinguished元dを消す元fはpで割り切れる。
δ(fd)=0とφ(fd)=0を組み合わせ、mod pでf^(2p)=0を得る（BS Lemma 2.34）。 -/
theorem p_dvd_of_mul_distinguished_eq_zero (D : DeltaStructure p A)
    [IsReduced (A ⧸ Ideal.span {(p : A)})] {d f : A}
    (hd : D.IsDistinguished d) (hfd : f * d = 0) : (p : A) ∣ f := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  have hqp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hδ := congrArg D.delta hfd
  rw [D.delta_mul, D.delta_zero] at hδ
  have hφ := congrArg D.frobeniusLift hfd
  rw [map_mul, map_zero, D.frobeniusLift_apply d] at hφ
  have hprod : f ^ p * D.frobeniusLift f = 0 := by
    apply hd.mul_left_eq_zero.mp
    linear_combination D.frobeniusLift f * hδ - D.delta f * hφ
  have hnil : q f ^ (p + p) = 0 := by
    have h := congrArg q hprod
    rw [map_mul, map_pow, D.map_frobeniusLift_of_map_p_eq_zero q hqp f, map_zero] at h
    rwa [pow_add]
  apply Ideal.mem_span_singleton.mp
  exact Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero hnil)

/-- p正則・p進分離でmod pが被約なδ環のdistinguished元は非零因子。
零因子を繰り返しpで割り、各p^nでの可除性からp進分離性を適用する（BS Lemma 2.34(1)）。 -/
theorem IsDistinguished.mul_injective {D : DeltaStructure p A}
    [IsReduced (A ⧸ Ideal.span {(p : A)})]
    [IsHausdorff (Ideal.span {(p : A)}) A]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) {d : A}
    (hd : D.IsDistinguished d) : Function.Injective (fun x : A ↦ d * x) := by
  have hdiv (n : ℕ) : ∀ f : A, f * d = 0 → (p : A) ^ n ∣ f := by
    induction n with
    | zero => intro f _; simp
    | succ n ih =>
        intro f hf
        obtain ⟨r, hr⟩ := D.p_dvd_of_mul_distinguished_eq_zero hd hf
        have hrd : r * d = 0 := by
          apply hp
          change (p : A) * (r * d) = (p : A) * 0
          rw [← mul_assoc, ← hr, hf, mul_zero]
        obtain ⟨s, hs⟩ := ih r hrd
        refine ⟨s, ?_⟩
        rw [hr, hs, pow_succ]
        ring
  have hker (f : A) (hf : f * d = 0) : f = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {(p : A)})
    intro n
    simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
      using (Ideal.mem_span_singleton.mpr (hdiv n f hf))
  intro x y hxy
  change d * x = d * y at hxy
  apply sub_eq_zero.mp
  apply hker
  rw [sub_mul, mul_comm x d, mul_comm y d, hxy, sub_self]

/-- p進分離な完全δ環のdistinguished元は非零因子。
完全δ構造からp正則性とmod pの完全性・被約性を供給する。 -/
theorem IsPerfect.distinguished_mul_injective {D : DeltaStructure p A}
    (hD : D.IsPerfect) [IsHausdorff (Ideal.span {(p : A)}) A] {d : A}
    (hd : D.IsDistinguished d) : Function.Injective (fun x : A ↦ d * x) := by
  let := hD.perfectRing_mod_p
  let : IsReduced (A ⧸ Ideal.span {(p : A)}) :=
    (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr (by
      intro x hx
      exact (PerfectRing.bijective_frobenius (R := A ⧸ Ideal.span {(p : A)}) (p := p)).1
        (by simpa only [zero_pow (Fact.out : p.Prime).ne_zero] using hx))
  exact hd.mul_injective hD.p_mul_injective

end SerrePositivity.BhattScholze.DeltaStructure
