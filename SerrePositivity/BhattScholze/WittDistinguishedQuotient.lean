module

public import SerrePositivity.BhattScholze.WittDistinguished
public import SerrePositivity.BhattScholze.PerfectDeltaQuotientFrobenius

/-! # distinguished Witt商のp乗根と単元係数

著者公開版Lemma 2.33・Theorem 3.10の具体的なWitt商の計算。
商の完備性とFontaine核の単項性はまだ結論しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- distinguished Witt元は[x₀]+p*u（u単元）と書ける。
任意の完全係数環でのLemma 2.33の具体的な展開。 -/
theorem exists_teichmuller_add_p_mul_unit_of_distinguished (d : WittVector p k)
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    ∃ u : (WittVector p k)ˣ,
      d = WittVector.teichmuller p (d.coeff 0) + (p : WittVector p k) * u := by
  have hm : d - WittVector.teichmuller p (d.coeff 0) ∈ Ideal.span {(p : WittVector p k)} := by
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change (WittVector.constantCoeff : WittVector p k →+* k)
      (d - WittVector.teichmuller p (d.coeff 0)) = 0
    rw [map_sub]
    simp
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
  have he : d = WittVector.teichmuller p (d.coeff 0) + (p : WittVector p k) * y := by
    linear_combination hy
  have h1 : d.coeff 1 = y.coeff 0 ^ p := by
    rw [he, witt_add_coeff_one, WittVector.teichmuller_coeff_pos p _ 1 (by decide)]
    simp only [WittVector.teichmuller_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.coeff_p_zero, zero_mul, WittVector.teichmuller_zero, add_zero,
      WittVector.teichmuller_coeff_pos p _ 1 (by decide), zero_add,
      witt_mul_coeff_one, WittVector.coeff_p_one, zero_pow (Fact.out : p.Prime).ne_zero,
      one_mul, CharP.cast_eq_zero]
  have hy0 : IsUnit (y.coeff 0) := by
    apply (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
    rw [← h1]
    exact (wittDeltaStructure_isDistinguished_iff p k d).mp hd
  obtain ⟨u, hu⟩ := PerfectoidFrobeniusCriterion.witt_isUnit_of_constantCoeff k p y hy0
  exact ⟨u, by simpa only [hu] using he⟩

/-- dを零に送るWitt環からの射の終域で、pは単元倍のp乗。
可除性だけでなく具体的なπと単元の存在を結論する。 -/
theorem exists_unit_mul_pow_p_of_distinguished_map_eq_zero
    (d : WittVector p k) (hd : (wittDeltaStructure p k).IsDistinguished d)
    {S : Type v} [CommRing S] (q : WittVector p k →+* S) (hqd : q d = 0) :
    ∃ (π : S) (v : Sˣ), (p : S) = v * π ^ p := by
  obtain ⟨u, hu⟩ := exists_teichmuller_add_p_mul_unit_of_distinguished p k d hd
  obtain ⟨a, ha⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 (d.coeff 0)
  change a ^ p = d.coeff 0 at ha
  let w := Units.map q.toMonoidHom u
  let π := q (WittVector.teichmuller p a)
  have h : π ^ p + (p : S) * (w : S) = 0 := by
    rw [hu, map_add, map_mul, map_natCast] at hqd
    change q (WittVector.teichmuller p (d.coeff 0)) + (p : S) * q (u : WittVector p k) = 0 at hqd
    change q (WittVector.teichmuller p a) ^ p + (p : S) * q (u : WittVector p k) = 0
    rw [← map_pow, ← map_pow, ha]
    exact hqd
  have hπ : π ^ p = -((p : S) * (w : S)) := eq_neg_of_add_eq_zero_left h
  refine ⟨π, -w⁻¹, ?_⟩
  rw [hπ]
  simp [mul_comm, mul_assoc]

/-- distinguished Witt元による商で、p=単元·π^p。 -/
theorem witt_distinguished_quotient_exists_unit_mul_pow_p (d : WittVector p k)
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    ∃ (π : WittVector p k ⧸ Ideal.span {d}) (v : (WittVector p k ⧸ Ideal.span {d})ˣ),
      (p : WittVector p k ⧸ Ideal.span {d}) = v * π ^ p :=
  exists_unit_mul_pow_p_of_distinguished_map_eq_zero p k d hd (Ideal.Quotient.mk _)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)))

end SerrePositivity.BhattScholze
