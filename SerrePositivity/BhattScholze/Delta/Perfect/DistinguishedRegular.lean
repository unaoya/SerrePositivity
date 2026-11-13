module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.CommutativeAlgebra.Adic.BoundedTorsionQuotient

/-!
# distinguished 元の正則性と商の p 冪ねじれ（BS 著者版 Lemma 2.34）

## 概要
p ねじれなし・p 進分離で A/p が被約な δ 環の distinguished 元は非零因子で、A/(d) の p 冪ねじれは p で消える。
冪 dⁿ への反復、完全 p 進完備 δ 環での商の p 進完備性。
distinguished 商の p 進完備性は、BS 著者版 Theorem 3.10 の商が perfectoid になる方向で使う。

## 方針
fd = 0 に δ と φ を当てて mod p で f^{2p} = 0 を得、被約性と p 進分離性を使う。

## 規約
商の導来完備性・perfectoid 性は仮定しない。

## 使われ方
完全 prism の性質（BS 著者版 Lemma 3.8）、BS 著者版 Theorem 3.10、prism の完全化。
-/

@[expose] public noncomputable section
universe u

/-! ## distinguished元の非零因子性

BS 著者版 Lemma 2.34(1)。mod pの被約性から零因子のp可除性を導き、
pの消去とp進分離性により零因子を零と判定する。
-/

section DistinguishedRegular

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- mod pが被約なら、distinguished元dを消す元fはpで割り切れる。
δ(fd)=0とφ(fd)=0を組み合わせ、mod pでf^(2p)=0を得る（BS 著者版 Lemma 2.34）。 -/
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

/-- p正則・p進分離でmod pが被約なδ環のdistinguished元は非零因子（BS 著者版 Lemma 2.34 (1)）。
零因子を繰り返しpで割り、各p^nでの可除性からp進分離性を適用する。 -/
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

/-- p進分離な完全δ環のdistinguished元は非零因子（BS 著者版 Lemma 2.34 (1) の完全 δ 環の場合）。
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

end DistinguishedRegular

/-! ## distinguished商の有界p冪ねじれ

BS 著者版 Lemma 2.34(2)。p正則でmod pが被約なδ環をdistinguished元で割ると、
商の任意のp冪ねじれはpで消える。導来完備性やperfectoid性は仮定しない。
-/

section DistinguishedTorsion

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- pを零に送る環準同型ではδ(p²f)の像は零。δ積公式の各項から直接従う。 -/
theorem map_delta_p_sq_mul {B : Type*} [CommRing B] (D : DeltaStructure p A)
    (q : A →+* B) (hqp : q (p : A) = 0) (f : A) : q (D.delta ((p : A) ^ 2 * f)) = 0 := by
  rw [show (p : A) ^ 2 * f = (p : A) * ((p : A) * f) by ring, D.delta_mul]
  simp only [map_add, map_mul, map_pow, hqp, zero_pow (Fact.out : p.Prime).ne_zero,
    zero_mul, mul_zero, add_zero]

/-- p²f=gdでdがdistinguished、mod pが被約ならpはgを割る。
δとφの等式をmod pで組み合わせてg^(2p)=0を得る（BS 著者版 Lemma 2.34(2)の核心）。 -/
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

/-- 商A/(d)で任意のp冪により零化される元はpで零化される（BS 著者版 Lemma 2.34 (2)）。
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

end DistinguishedTorsion

/-! ## distinguished元の冪商の有界pねじれ

BS 著者版 Lemma 2.34(2)を、正則なdistinguished元の冪商に反復適用する。
A/(dⁿ)のp冪ねじれはpⁿで消える。商の古典的・導来完備性は結論しない。
-/

section DistinguishedPowerTorsion

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

end DistinguishedPowerTorsion

/-! ## 完全p進完備δ環のdistinguished商と冪商のp完備性

受領したF5に既存BS BS 著者版 Lemma 2.34の有界ねじれ評価を供給する。
商のp正則性・Noether性・有限表示性を仮定しない。
-/

section DistinguishedQuotientComplete

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全p進完備δ環のdistinguished商は、pねじれを許して古典的p進完備。 -/
theorem IsPerfect.distinguished_quotient_isAdicComplete {D : DeltaStructure p A}
    (hD : D.IsPerfect) [IsAdicComplete (Ideal.span {(p : A)}) A] {d : A}
    (hd : D.IsDistinguished d) :
    IsAdicComplete (Ideal.span {(p : A ⧸ Ideal.span {d})}) (A ⧸ Ideal.span {d}) := by
  apply isAdicComplete_principal_quotient_natCast_of_bounded_torsion A p d
  refine ⟨1, fun n x hx ↦ ?_⟩
  simpa only [pow_one] using hD.distinguished_quotient_p_pow_torsion_killed_by_p hd n x hx

/-- distinguished元の全冪商は古典的p進完備。零冪商も含む。 -/
theorem IsPerfect.distinguished_power_quotient_isAdicComplete {D : DeltaStructure p A}
    (hD : D.IsPerfect) [IsAdicComplete (Ideal.span {(p : A)}) A] {d : A}
    (hd : D.IsDistinguished d) (k : ℕ) :
    IsAdicComplete (Ideal.span {(p : A ⧸ Ideal.span {d ^ k})}) (A ⧸ Ideal.span {d ^ k}) := by
  apply isAdicComplete_principal_power_quotient_natCast_of_bounded_torsion A p d k
  exact ⟨k, fun n x hx ↦ hD.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow hd k n x hx⟩

end SerrePositivity.BhattScholze.DeltaStructure

end DistinguishedQuotientComplete

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.34"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.mul_injective
attribute [cite BS19 "Lemma 2.34"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsDistinguished.quotient_p_pow_torsion_killed_by_p
attribute [cite BS19 "Lemma 2.34"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.distinguished_mul_injective
