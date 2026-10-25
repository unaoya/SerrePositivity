module

public import SerrePositivity.BhattScholze.Delta.DeltaRing
public import SerrePositivity.BhattScholze.Delta.DeltaPrime
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Span

/-! # distinguished元の単元倍と因子

BS著者公開版§2.3、Lemma 2.23–2.25。
原典のrad(A)はJacobson根基であり、nilradicalとは区別する。
完備性・p正則性を追加せず、δの積公式とJacobson根基の単元判定を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

private theorem unit_add_radical {a b : A} (ha : IsUnit a)
    (hb : b ∈ Ideal.jacobson (⊥ : Ideal A)) : IsUnit (a + b) := by
  obtain ⟨u, rfl⟩ := ha
  have h := (Ideal.mem_jacobson_bot.mp hb) (↑(u⁻¹) : A)
  have he : (↑u : A) * (b * ↑(u⁻¹) + 1) = ↑u + b := by
    simp [mul_add, mul_left_comm, add_comm]
  rw [← he]
  exact u.isUnit.mul h

private theorem unit_add_radical_iff {a b : A}
    (hb : b ∈ Ideal.jacobson (⊥ : Ideal A)) : IsUnit (a + b) ↔ IsUnit a := by
  constructor
  · intro h
    simpa using unit_add_radical h ((Ideal.jacobson (⊥ : Ideal A)).neg_mem hb)
  · exact fun h ↦ unit_add_radical h hb

/-- distinguished元の単元倍はdistinguished。
d,pがJacobson根基に属する仮定により、δ積公式の補正項が単元性を変えない（BS Lemma 2.23）。 -/
theorem IsDistinguished.unit_mul {D : DeltaStructure p A} {d : A}
    (hd : D.IsDistinguished d) (u : Aˣ)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    D.IsDistinguished ((u : A) * d) := by
  change IsUnit (D.delta ((u : A) * d))
  rw [D.delta_mul, add_assoc]
  apply unit_add_radical ((u.isUnit.pow p).mul hd)
  exact (Ideal.jacobson (⊥ : Ideal A)).add_mem
    ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_left (D.delta ↑u)
      ((Ideal.jacobson (⊥ : Ideal A)).pow_mem_of_mem hdr p (Fact.out : p.Prime).pos))
    ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_right (D.delta d)
      ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_right (D.delta ↑u) hpr))

/-- 単元倍でdistinguished性は変わらない。逆単元によるLemma 2.23を使う。 -/
theorem isDistinguished_unit_mul_iff (D : DeltaStructure p A) (d : A) (u : Aˣ)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    D.IsDistinguished ((u : A) * d) ↔ D.IsDistinguished d := by
  constructor
  · intro h
    have hrd := (Ideal.jacobson (⊥ : Ideal A)).mul_mem_left (u : A) hdr
    simpa only [Units.val_inv_eq_inv_val, ← mul_assoc, Units.inv_mul, one_mul]
      using h.unit_mul (u⁻¹) hrd hpr
  · exact fun h ↦ h.unit_mul u hdr hpr

/-- f*hがdistinguishedでf,pがJacobson根基に属すれば、fはdistinguishedでhは単元。
δ積公式から根基内の二項を除き、h^p*δ(f)の単元性を得る（BS Lemma 2.24）。 -/
theorem isDistinguished_factor (D : DeltaStructure p A) (f h : A)
    (hfh : D.IsDistinguished (f * h))
    (hfr : f ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    D.IsDistinguished f ∧ IsUnit h := by
  have hr : f ^ p * D.delta h + (p : A) * D.delta f * D.delta h ∈
      Ideal.jacobson (⊥ : Ideal A) :=
    (Ideal.jacobson (⊥ : Ideal A)).add_mem
      ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_right (D.delta h)
        ((Ideal.jacobson (⊥ : Ideal A)).pow_mem_of_mem hfr p (Fact.out : p.Prime).pos))
      ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_right (D.delta h)
        ((Ideal.jacobson (⊥ : Ideal A)).mul_mem_right (D.delta f) hpr))
  have hu : IsUnit (D.delta f * h ^ p) := by
    apply (unit_add_radical_iff hr).mp
    have he : D.delta f * h ^ p + (f ^ p * D.delta h + (p : A) * D.delta f * D.delta h) =
        D.delta (f * h) := by
      rw [D.delta_mul]
      ring
    rw [he]
    exact hfh
  obtain ⟨hf, hh⟩ := (Commute.all _ _).isUnit_mul_iff.mp hu
  exact ⟨hf, (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp hh⟩

/-- distinguished元dについてpは(d,φ(d))に属する（BS Lemma 2.25の順方向）。
この方向にはJacobson根基の仮定もp正則性も不要。 -/
theorem IsDistinguished.p_mem_span {D : DeltaStructure p A} {d : A}
    (hd : D.IsDistinguished d) : (p : A) ∈ Ideal.span {d, D.frobeniusLift d} := by
  let I := Ideal.span {d, D.frobeniusLift d}
  have hdp : d ^ p ∈ I :=
    I.pow_mem_of_mem (Ideal.subset_span (by simp)) p (Fact.out : p.Prime).pos
  have hφ : D.frobeniusLift d ∈ I := Ideal.subset_span (by simp)
  have hm : (p : A) * D.delta d ∈ I := by
    have h := I.sub_mem hφ hdp
    simpa only [D.frobeniusLift_apply, add_sub_cancel_left] using h
  obtain ⟨u, hu⟩ := hd
  have h := I.mul_mem_right (↑(u⁻¹) : A) hm
  rw [← hu, mul_assoc, Units.mul_inv, mul_one] at h
  exact h

/-- pが(d,φ(d))に属しd,pがJacobson根基に属すればdはdistinguished。
δ(d)を含む極大イデアルがあると仮定し、p(1-bδ(d))=cdへδを適用する。
剰余体では左辺のδが1、右辺のδが0となる（BS Lemma 2.25の逆方向）。 -/
theorem isDistinguished_of_p_mem_span (D : DeltaStructure p A) (d : A)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A))
    (hspan : (p : A) ∈ Ideal.span {d, D.frobeniusLift d}) : D.IsDistinguished d := by
  by_contra hunit
  obtain ⟨M, hM, hδM⟩ := exists_max_ideal_of_mem_nonunits hunit
  let := hM
  let q := Ideal.Quotient.mk M
  have hJM : Ideal.jacobson (⊥ : Ideal A) ≤ M := sInf_le ⟨bot_le, hM⟩
  have hqd : q d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hJM hdr)
  have hqp : q (p : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hJM hpr)
  have hqδ : q (D.delta d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hδM
  have hp0 : (p : A ⧸ M) = 0 := by simpa only [map_natCast] using hqp
  let : CharP (A ⧸ M) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hspan
  let c := a + b * d ^ (p - 1)
  let e := 1 - b * D.delta d
  have hpow : d ^ (p - 1) * d = d ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
  have heq : (p : A) * e = c * d := by
    rw [D.frobeniusLift_apply] at hab
    dsimp only [c, e]
    linear_combination -hab - b * hpow
  have h := congrArg (fun x ↦ q (D.delta x)) heq
  have hqe : q e = 1 := by simp [e, hqδ]
  rw [D.delta_mul, D.delta_mul] at h
  simp only [map_add, map_mul, map_pow, hqp, hqd, hqδ, D.map_delta_p q,
    hqe, zero_pow (Fact.out : p.Prime).ne_zero, one_pow, zero_mul, mul_zero,
    zero_add, add_zero, one_mul] at h
  exact one_ne_zero h

/-- d,pがJacobson根基に属すれば、distinguished性はp∈(d,φ(d))と同値。
完備性・p正則性を仮定しないBS著者版Lemma 2.25。 -/
theorem isDistinguished_iff_p_mem_span (D : DeltaStructure p A) (d : A)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    D.IsDistinguished d ↔ (p : A) ∈ Ideal.span {d, D.frobeniusLift d} :=
  ⟨fun h ↦ h.p_mem_span, D.isDistinguished_of_p_mem_span d hdr hpr⟩

/-- 同じ主イデアルを生成する元のdistinguished性は一致する。
両生成元とpがJacobson根基に属する仮定でLemma 2.24を両方向に適用する。
非零因子の仮定は不要（BS Lemma 2.25の末尾）。 -/
theorem isDistinguished_iff_of_span_eq (D : DeltaStructure p A) (d e : A)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (her : e ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A))
    (heq : Ideal.span {d} = Ideal.span {e}) : D.IsDistinguished d ↔ D.IsDistinguished e := by
  constructor
  · intro hd
    have hm : d ∈ Ideal.span {e} := heq ▸ Ideal.mem_span_singleton_self d
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hm
    rw [hr] at hd
    exact (D.isDistinguished_factor e r hd her hpr).1
  · intro he
    have hm : e ∈ Ideal.span {d} := heq.symm ▸ Ideal.mem_span_singleton_self e
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hm
    rw [hr] at he
    exact (D.isDistinguished_factor d r he hdr hpr).1

end SerrePositivity.BhattScholze.DeltaStructure
