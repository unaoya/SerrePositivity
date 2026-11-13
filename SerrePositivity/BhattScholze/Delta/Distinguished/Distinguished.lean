module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.Jacobson.Ideal
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.Ideal.Span

/-!
# distinguished 元（BS 著者版 §2.3：BS 著者版 Example 2.20(1)、BS 著者版 Lemma 2.23〜2.25）

## 概要
δ(p) ≡ 1 mod p（標数 p の環へは δ(p) ↦ 1）、p ∈ rad なら p は distinguished、単元倍・因子、
p ∈ (d, φ(d)) との同値と、それが主イデアルだけで決まること。

## 方針
積公式を展開して根基に入る項を除く。BS 著者版 Lemma 2.25 の逆向きは δ(d) を含む極大イデアルでの計算（局所化・完備化を使わない）。

## 規約
rad は Jacobson 根基。完備性・p 正則性を仮定しない。

## 使われ方
prism の定義（Prism/Basic）、BS 著者版 Lemma 2.28、BS 著者版 Proposition 3.13 の単元係数。
-/

@[expose] public noncomputable section
universe u v

/-! ## δ(p)のmod p計算

W₂切断の自然数上の値とMathlibの標数pにおけるWitt係数を用いる。
BS 著者版 Example 2.20(1)の単元性に必要な合同式を、p正則性なしで証明する。
-/

section DeltaPrime

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 標数pの環への任意の環準同型はδ(p)を1に送る。
δ射である必要はなく、W₂切断が自然数を保存することから従う。 -/
theorem map_delta_p {B : Type v} [CommRing B] [CharP B p]
    (D : DeltaStructure p A) (f : A →+* B) : f (D.delta (p : A)) = 1 := by
  have h := wittTwoMap_coeff (p := p) f (D.sectionHom (p : A)) (1 : Fin 2)
  simp only [map_natCast] at h
  change (p : WittVector p B).coeff 1 = f ((p : WittVector p A).coeff 1) at h
  rw [WittVector.coeff_p_one] at h
  change f ((D.sectionHom (p : A)).coeff 1) = 1
  rw [map_natCast]
  exact h.symm

/-- δ(p)はmod pで1に一致する（BS 著者版 Example 2.20 (1) の合同式の部分）。
  零環・pねじれを持つ環も含む。 -/
theorem delta_p_sub_one_mem (D : DeltaStructure p A) :
    D.delta (p : A) - 1 ∈ Ideal.span {(p : A)} := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rcases subsingleton_or_nontrivial (A ⧸ I) with hsub | hnontrivial
  · let := hsub
    exact Subsingleton.elim _ _
  · let := hnontrivial
    have hp0 : (p : A ⧸ I) = 0 := by
      rw [← map_natCast q]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    let : CharP (A ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
    change q (D.delta (p : A) - 1) = 0
    rw [map_sub, D.map_delta_p q, map_one, sub_self]

/-- pがJacobson根基に属するδ環ではpがdistinguished（BS 著者版 Example 2.20 (1) の p が Jacobson 根基にある δ 環への一般化）。
δ(p)-1が(p)に属する合同式とJacobson根基の単元判定を使う。 -/
theorem isDistinguished_p (D : DeltaStructure p A)
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) : D.IsDistinguished (p : A) := by
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  have hle : Ideal.span {(p : A)} ≤ Ideal.jacobson (⊥ : Ideal A) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpr)
  exact hle D.delta_p_sub_one_mem

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaPrime

/-! ## distinguished元の単元倍と因子

BS著者公開版§2.3、BS 著者版 Lemma 2.23–2.25。
原典のrad(A)はJacobson根基であり、nilradicalとは区別する。
完備性・p正則性を追加せず、δの積公式とJacobson根基の単元判定を使う。
-/

section Distinguished

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

/-- distinguished元の単元倍はdistinguished（BS 著者版 Lemma 2.23）。
d,pがJacobson根基に属する仮定により、δ積公式の補正項が単元性を変えない。 -/
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

/-- 単元倍でdistinguished性は変わらない（BS 著者版 Lemma 2.23 の単元倍に関する同値の形）。
  逆単元によるBS 著者版 Lemma 2.23を使う。 -/
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

/-- f*hがdistinguishedでf,pがJacobson根基に属すれば、fはdistinguishedでhは単元（BS 著者版 Lemma 2.24）。
δ積公式から根基内の二項を除き、h^p*δ(f)の単元性を得る。 -/
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

/-- distinguished元dについてpは(d,φ(d))に属する（BS 著者版 Lemma 2.25の順方向）。
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
剰余体では左辺のδが1、右辺のδが0となる（BS 著者版 Lemma 2.25の逆方向）。 -/
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

/-- d,pがJacobson根基に属すれば、distinguished性はp∈(d,φ(d))と同値（BS 著者版 Lemma 2.25 の第一文）。
完備性・p正則性を仮定しないBS 著者版 Lemma 2.25。 -/
theorem isDistinguished_iff_p_mem_span (D : DeltaStructure p A) (d : A)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    D.IsDistinguished d ↔ (p : A) ∈ Ideal.span {d, D.frobeniusLift d} :=
  ⟨fun h ↦ h.p_mem_span, D.isDistinguished_of_p_mem_span d hdr hpr⟩

/-- 同じ主イデアルを生成する元のdistinguished性は一致する（BS 著者版 Lemma 2.25 の第二文）。
両生成元とpがJacobson根基に属する仮定でBS 著者版 Lemma 2.24を両方向に適用する。
非零因子の仮定は不要。 -/
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

end Distinguished

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 2.20" (partial := special) "(1) d=p だけ（p 正則性なし）。(2) q-de Rham、(3) \\(A_{\\inf}(\\mathcal O_C)\\) の ξ は本体にない（Thm 3.10 側の perfectPrismWittGenerator_isDistinguished は完全 prism の生成元を W(A/p) へ移したもので、ξ の主張ではない）。(4) Breuil–Kisin はなし ／ DOC1 照合：ok 2 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.DeltaStructure.delta_p_sub_one_mem
attribute [cite BS19 "Ex 2.20" (partial := special) "(1) d=p だけ（p 正則性なし）。(2) q-de Rham、(3) \\(A_{\\inf}(\\mathcal O_C)\\) の ξ は本体にない（Thm 3.10 側の perfectPrismWittGenerator_isDistinguished は完全 prism の生成元を W(A/p) へ移したもので、ξ の主張ではない）。(4) Breuil–Kisin はなし ／ DOC1 照合：ok 2 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_p
attribute [cite BS19 "Lemma 2.23"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.unit_mul
attribute [cite BS19 "Lemma 2.23"] _root_.SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_unit_mul_iff
attribute [cite BS19 "Lemma 2.24"] _root_.SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_factor
attribute [cite BS19 "Lemma 2.25"] _root_.SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_of_span_eq
attribute [cite BS19 "Lemma 2.25"] _root_.SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span
attribute [cite BS19 "Lemma 3.1" (partial := special) "主イデアル（向き付き）の場合だけ。locally principal・Prop 3.1(3) の局所化は未（D5 で不要）。向き付き prism の定義と distinguished 性の同値として E3 経路の土台 ／ DOC1 照合：ok 3 件 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.DeltaStructure.isDistinguished_iff_p_mem_span
