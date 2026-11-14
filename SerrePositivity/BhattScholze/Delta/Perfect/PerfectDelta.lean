module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
public import Mathlib.RingTheory.Nilpotent.Basic
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.WittVector.Complete
public import SerrePositivity.CommutativeAlgebra.Witt.Lift
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine

/-!
# 完全 δ 環の構造（BS 著者版 §2.4：BS 著者版 Lemma 2.28・Lemma 2.32・2.33、BS 著者版 Corollary 2.31、BS 著者版 Example 2.6）

## 概要
Frobenius は p ねじれを消す（BS 著者版 Lemma 2.28。p が冪零な δ 環は零環、BS 著者版 Example 2.6）、完全 δ 環は p ねじれなしで A/p は完全、
Frobenius 同型は δ 射、p 冪の元は rank 1（BS 著者版 Lemma 2.32）、
完全な標数 p の環の Witt 環の δ 構造と復元 A ≅ W(A/p)（BS 著者版 Corollary 2.31）、
Teichmüller 係数による distinguished 判定（BS 著者版 Lemma 2.33）。

## 方針
px = 0 に δ を当て、δ(p) ≡ 1 mod p で消去する。rank 1 は pδ(x) ∣ δ(x^p) の反復。Witt 環の側は Mathlib の Witt Frobenius と共通基盤の復元から。

## 規約
Z_(p) 代数や p ∈ rad を仮定しない。BS 著者版 Corollary 2.31 は圏同値ではなく対象ごと。

## 使われ方
完全 prism（Prism）、完全化、Witt 商の Fontaine 比較。
-/

@[expose] public noncomputable section
universe u v

/-! ## Frobenius持上げによるpねじれの消去

BS 著者版 Lemma 2.28の代数的証明。δ(p)≡1 mod pを用いるので、
Z_(p)代数やpのJacobson根基への所属を仮定せず、任意のδ構造で証明する。
-/

section DeltaTorsion

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- px=0ならφ(x)=0かつp^pδ(x)=0（BS 著者版 Lemma 2.28 (1) の証明中の p ねじれの計算）。
δ積公式とφの環準同型則を使い、最後はδ(p)≡1 mod pで消去する。 -/
theorem torsion_calculation (D : DeltaStructure p A) {x : A} (hx : (p : A) * x = 0) :
    D.frobeniusLift x = 0 ∧ (p : A) ^ p * D.delta x = 0 := by
  have hpow (a : A) : a ^ (p - 1) * a = a ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
  have hpx : (p : A) ^ (p - 1) * x = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (show p - 1 ≠ 0 by have := (Fact.out : p.Prime).two_le; omega)
    rw [hn, pow_succ, mul_assoc, hx, mul_zero]
  have hφp : (p : A) * D.frobeniusLift x = 0 := by
    have h := congrArg D.frobeniusLift hx
    simpa only [map_mul, map_natCast, map_zero] using h
  have hφpow : (p : A) ^ (p - 1) * D.frobeniusLift x = 0 := by
    have h := congrArg D.frobeniusLift hpx
    simpa only [map_mul, map_pow, map_natCast, map_zero] using h
  have hxp : (p : A) ^ (p - 1) * x ^ p = 0 := by
    rw [← hpow x]
    calc
      (p : A) ^ (p - 1) * (x ^ (p - 1) * x) =
          x ^ (p - 1) * ((p : A) ^ (p - 1) * x) := by ring
      _ = 0 := by rw [hpx, mul_zero]
  have hpd : (p : A) ^ p * D.delta x = 0 := by
    have h := congrArg (fun a ↦ (p : A) ^ (p - 1) * a) (D.frobeniusLift_apply x)
    rw [hφpow, mul_add, hxp, zero_add, ← mul_assoc, hpow (p : A)] at h
    exact h.symm
  have hδφ : D.delta (p : A) * D.frobeniusLift x = 0 := by
    have h := congrArg D.delta hx
    rw [D.delta_mul, D.delta_zero, hpd, zero_add] at h
    rw [D.frobeniusLift_apply]
    linear_combination h
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp D.delta_p_sub_one_mem
  have hφ : D.frobeniusLift x = 0 := by
    linear_combination hδφ - D.frobeniusLift x * hr - r * hφp
  exact ⟨hφ, hpd⟩

/-- φが単射ならpの乗法は単射（BS 著者版 Lemma 2.28 (1)）。
  完備性は不要。 -/
theorem p_mul_injective_of_frobeniusLift_injective (D : DeltaStructure p A)
    (hφ : Function.Injective D.frobeniusLift) : Function.Injective (fun x : A ↦ (p : A) * x) := by
  intro x y hxy
  change (p : A) * x = (p : A) * y at hxy
  have hz : (p : A) * (x - y) = 0 := by rw [mul_sub, hxy, sub_self]
  have h := (D.torsion_calculation hz).1
  have he : x - y = 0 := hφ (h.trans D.frobeniusLift.map_zero.symm)
  exact sub_eq_zero.mp he

/-- 完全δ環ではpは正則。完全prismとWitt環の比較に使う。 -/
theorem IsPerfect.p_mul_injective {D : DeltaStructure p A} (hD : D.IsPerfect) :
    Function.Injective (fun x : A ↦ (p : A) * x) :=
  D.p_mul_injective_of_frobeniusLift_injective hD.1

/-- 被約δ環ではpの乗法は単射（BS 著者版 Lemma 2.28 (2)）。
p^pδ(x)=0からpδ(x)の冪が零となり、被約性を二度使ってpx=0からx=0を導く。 -/
theorem p_mul_injective_of_isReduced (D : DeltaStructure p A) [IsReduced A] :
    Function.Injective (fun x : A ↦ (p : A) * x) := by
  have hker (x : A) (hx : (p : A) * x = 0) : x = 0 := by
    obtain ⟨hφ, hpd⟩ := D.torsion_calculation hx
    have hpow : D.delta x ^ (p - 1) * D.delta x = D.delta x ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
    have hnil : ((p : A) * D.delta x) ^ p = 0 := by
      rw [mul_pow, ← hpow]
      calc
        (p : A) ^ p * (D.delta x ^ (p - 1) * D.delta x) =
            D.delta x ^ (p - 1) * ((p : A) ^ p * D.delta x) := by ring
        _ = 0 := by rw [hpd, mul_zero]
    have hpδ : (p : A) * D.delta x = 0 := eq_zero_of_pow_eq_zero hnil
    have hxp : x ^ p = 0 := by
      simpa only [D.frobeniusLift_apply, hpδ, add_zero] using hφ
    exact eq_zero_of_pow_eq_zero hxp
  intro x y hxy
  change (p : A) * x = (p : A) * y at hxy
  apply sub_eq_zero.mp
  apply hker
  rw [mul_sub, hxy, sub_self]

/-- δ環でpが冪零なら零環である（BS 著者版 Example 2.6 の末尾の結論）。
φは自然数pを固定しpねじれを零に送るため、p^n=0から順に指数を下げる。 -/
theorem subsingleton_of_isNilpotent_p (D : DeltaStructure p A)
    (hp : IsNilpotent (p : A)) : Subsingleton A := by
  have hpow (n : ℕ) (hn : (p : A) ^ n = 0) : (1 : A) = 0 := by
    induction n with
    | zero => simpa only [pow_zero] using hn
    | succ n ih =>
        have hx : (p : A) * (p : A) ^ n = 0 := by
          rw [mul_comm, ← pow_succ]
          exact hn
        have h := (D.torsion_calculation hx).1
        have hprev : (p : A) ^ n = 0 := by simpa only [map_pow, map_natCast] using h
        exact ih hprev
  obtain ⟨n, hn⟩ := hp
  exact subsingleton_of_zero_eq_one (hpow n hn).symm

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaTorsion

/-! ## p冪根を持つ元のrank 1性

BS 著者版 Lemma 2.32。δの積公式を(pδ(x))で割った商で反復し、
δ(x^p)がpδ(x)で割り切れることから一般δ環での可除性を証明する。
p正則性・自由δ環への帰着を使わない代数的な証明。
-/

section DeltaRankOne

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ(x^p)はpδ(x)で割り切れる。
(pδ(x))による商ではδ積公式の第三項が消え、通常の冪の微分と同じ帰納式になる。 -/
theorem p_mul_delta_dvd_delta_pow (D : DeltaStructure p A) (x : A) :
    (p : A) * D.delta x ∣ D.delta (x ^ p) := by
  let I := Ideal.span {(p : A) * D.delta x}
  let q := Ideal.Quotient.mk I
  have hz : q (p : A) * q (D.delta x) = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hpow (m : ℕ) : q (D.delta (x ^ (m + 1))) =
      (m + 1 : ℕ) * q x ^ (p * m) * q (D.delta x) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, D.delta_mul, map_add, map_add, map_mul, map_mul, map_mul,
          map_mul, map_pow, map_pow, ih]
        have hpowers : (q x ^ (m + 1)) ^ p = q x ^ (p * m) * q x ^ p := by
          rw [← pow_mul, Nat.add_mul, Nat.one_mul, Nat.mul_comm m p, pow_add]
        rw [hpowers]
        have herr : q (p : A) * ((m + 1 : ℕ) * q x ^ (p * m) * q (D.delta x)) *
            q (D.delta x) = 0 := by
          calc
            _ = ((m + 1 : ℕ) * q x ^ (p * m) * q (D.delta x)) *
                (q (p : A) * q (D.delta x)) := by ring
            _ = 0 := by rw [hz, mul_zero]
        rw [herr, add_zero, Nat.mul_succ, pow_add]
        simp only [map_pow]
        push_cast
        ring
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := hpow (p - 1)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).pos] at h
  rw [h]
  calc
    (p : A ⧸ I) * q x ^ (p * (p - 1)) * q (D.delta x) =
        q x ^ (p * (p - 1)) * (q (p : A) * q (D.delta x)) := by rw [map_natCast]; ring
    _ = 0 := by rw [hz, mul_zero]

/-- δ(x^(p^n))はp^nδ(x)で割り切れる。一般δ環で成立し、pねじれを許す。 -/
theorem pow_mul_delta_dvd_delta_pow (D : DeltaStructure p A) (x : A) (n : ℕ) :
    (p : A) ^ n * D.delta x ∣ D.delta (x ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := D.p_mul_delta_dvd_delta_pow (x ^ p ^ n)
      have hdiv := (mul_dvd_mul_left (p : A) ih).trans h
      simpa only [pow_succ, ← pow_mul, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- δ(x^(p^n))∈(p^n)（BS 著者版 Lemma 2.32 の第一文）。
  p正則性は要求しない。 -/
theorem pow_p_dvd_delta_pow (D : DeltaStructure p A) (x : A) (n : ℕ) :
    (p : A) ^ n ∣ D.delta (x ^ p ^ n) :=
  (dvd_mul_right ((p : A) ^ n) (D.delta x)).trans (D.pow_mul_delta_dvd_delta_pow x n)

/-- p進分離なδ環で、すべてのp^n乗根を持つ元はrank 1、すなわちδ(y)=0（BS 著者版 Lemma 2.32 の第二文）。
根の両立性は要求しない。 -/
theorem delta_eq_zero_of_has_pow_roots (D : DeltaStructure p A)
    [IsHausdorff (Ideal.span {(p : A)}) A] (y : A)
    (hy : ∀ n : ℕ, ∃ x : A, x ^ p ^ n = y) : D.delta y = 0 := by
  apply IsHausdorff.haus' (I := Ideal.span {(p : A)})
  intro n
  obtain ⟨x, hx⟩ := hy n
  have h := D.pow_p_dvd_delta_pow x n
  rw [hx] at h
  simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] using
    (Ideal.mem_span_singleton.mpr h)

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaRankOne

/-! ## 完全δ環のmod pの完全性

BS 著者版 Corollary 2.31の(1)から(2)の代数的部分。
φが全単射ならA/(p)のp乗写像も全単射である。完備性はこの部分には不要。
-/

section PerfectDeltaModP

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ構造のmod p商は完全環（BS 著者版 Corollary 2.31 (1) から (3) の対象上の部分）。
  φがpを固定するので、φによる(p)の逆像も(p)。
零環を含み、古典的・導来完備性はいずれも仮定しない。 -/
theorem IsPerfect.perfectRing_mod_p {D : DeltaStructure p A} (hD : D.IsPerfect) :
    PerfectRing (A ⧸ Ideal.span {(p : A)}) p := by
  let I := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  have hqp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hmod (x : A) : q (D.frobeniusLift x) = q x ^ p :=
    D.map_frobeniusLift_of_map_p_eq_zero q hqp x
  refine ⟨⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change q a ^ p = q b ^ p at hxy
    have hz : q (D.frobeniusLift (a - b)) = 0 := by
      rw [map_sub, map_sub, hmod a, hmod b, hxy, sub_self]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    obtain ⟨s, hs⟩ := hD.2 r
    have he : a - b = (p : A) * s := by
      apply hD.1
      rw [map_mul, map_natCast, hs]
      exact hr
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ⟨s, he⟩
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨q b, (hmod b).symm.trans (congrArg q hb)⟩

end SerrePositivity.BhattScholze.DeltaStructure

end PerfectDeltaModP

/-! ## 完全δ環のFrobenius同型とδ

p正則なδ環のFrobeniusはδ射であり、完全δ環では逆Frobeniusもδ射となる。
完全化に使うFrobeniusの反復図式をδ環の図式として扱うための補題。
-/

section PerfectDeltaFrobenius

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p正則なδ環のFrobenius持上げはδと可換。
φ自身との可換性から、p正則な終域におけるδ射の判定を使う。 -/
theorem isDeltaHom_frobeniusLift (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) : D.IsDeltaHom D D.frobeniusLift :=
  isDeltaHom_of_map_frobeniusLift D.frobeniusLift hp (fun _ ↦ rfl)

/-- 完全δ環のFrobeniusを環同型として束ねる。 -/
def frobeniusEquiv (D : DeltaStructure p A) (hD : D.IsPerfect) : A ≃+* A :=
  RingEquiv.ofBijective D.frobeniusLift hD

/-- 完全δ環のFrobenius同型はδ射。前段で証明したp正則性を使う。 -/
theorem frobeniusEquiv_isDeltaHom (D : DeltaStructure p A) (hD : D.IsPerfect) :
    D.IsDeltaHom D (D.frobeniusEquiv hD).toRingHom :=
  D.isDeltaHom_frobeniusLift hD.p_mul_injective

/-- 完全δ環の逆Frobeniusもδ射。完全化図式とWitt比較の自然性に用いる。 -/
theorem frobeniusEquiv_symm_isDeltaHom (D : DeltaStructure p A) (hD : D.IsPerfect) :
    D.IsDeltaHom D (D.frobeniusEquiv hD).symm.toRingHom :=
  (D.frobeniusEquiv_isDeltaHom hD).symm

/-- 完全δ環のFrobeniusは各mod p^n商の環自己同型を誘導する。
φ(p)=pから(p)^nの像が同じイデアルであることを使う。 -/
def frobeniusModPowEquiv (D : DeltaStructure p A) (hD : D.IsPerfect) (n : ℕ) :
    A ⧸ (Ideal.span {(p : A)}) ^ n ≃+* A ⧸ (Ideal.span {(p : A)}) ^ n :=
  Ideal.quotientEquiv _ _ (D.frobeniusEquiv hD) (by
    simp only [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast])

/-- mod p^n Frobenius同型は代表元上で元環のφを適用する。 -/
@[simp] theorem frobeniusModPowEquiv_mk (D : DeltaStructure p A) (hD : D.IsPerfect)
    (n : ℕ) (x : A) :
    D.frobeniusModPowEquiv hD n (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n) x) =
      Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n) (D.frobeniusLift x) := rfl

/-- mod p^n Frobenius同型は商の遷移写像と両立する。
完備化でFrobeniusとその逆を比較するための具体的な可換図式。 -/
theorem frobeniusModPowEquiv_compatible (D : DeltaStructure p A) (hD : D.IsPerfect)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : A)}) hmn).comp
        (D.frobeniusModPowEquiv hD n).toRingHom =
      (D.frobeniusModPowEquiv hD m).toRingHom.comp
        (Ideal.Quotient.factorPow (Ideal.span {(p : A)}) hmn) := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end SerrePositivity.BhattScholze.DeltaStructure

end PerfectDeltaFrobenius

/-! ## 完全な標数p環のWitt環のδ構造

BS 著者版 Corollary 2.31の(3)から(1)。MathlibのWitt Frobenius、
p正則性・完備性を再利用して一意なδ構造を与える。圏同値全体はまだ構成しない。
-/

section WittDelta

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- Witt Frobeniusを持ち上げとするδ構造の存在・一意性（BS 著者版 Corollary 2.31 の W(k) 上の δ 構造の一意性の部分）。
Witt環のp正則性とmod pの第0座標公式を既存Mathlibから供給する。 -/
theorem existsUnique_wittDeltaStructure :
    ∃! D : DeltaStructure p (WittVector p k), D.frobeniusLift = WittVector.frobenius := by
  have hp : Function.Injective (fun x : WittVector p k ↦ (p : WittVector p k) * x) := by
    intro x y hxy
    change (p : WittVector p k) * x = (p : WittVector p k) * y at hxy
    apply sub_eq_zero.mp
    apply WittVector.eq_zero_of_p_mul_eq_zero
    rw [mul_comm, mul_sub, hxy, sub_self]
  apply DeltaStructure.existsUnique_of_frobeniusLift hp WittVector.frobenius
  intro x
  apply Ideal.mem_span_singleton.mp
  apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
  change (WittVector.constantCoeff : WittVector p k →+* k)
    (WittVector.frobenius x - x ^ p) = 0
  rw [map_sub, map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.coeff_frobenius_charP, sub_self]

/-- 完全な標数p環のWitt環の標準δ構造。Frobenius持上げから一意に選ぶ。 -/
def wittDeltaStructure : DeltaStructure p (WittVector p k) :=
  (existsUnique_wittDeltaStructure p k).choose

/-- 標準Witt δ構造のFrobenius持上げはMathlibのWitt Frobenius。 -/
@[simp] theorem wittDeltaStructure_frobeniusLift :
    (wittDeltaStructure p k).frobeniusLift = WittVector.frobenius :=
  (existsUnique_wittDeltaStructure p k).choose_spec.1

/-- 標準Witt δ構造は完全。MathlibのWitt Frobenius同型を使う。 -/
theorem wittDeltaStructure_isPerfect : (wittDeltaStructure p k).IsPerfect := by
  change Function.Bijective (wittDeltaStructure p k).frobeniusLift
  rw [wittDeltaStructure_frobeniusLift]
  exact WittVector.frobenius_bijective p k

/-- 標準Witt δ環はp進完備。新しい完備性モデルを導入せずMathlibのインスタンスを返す。 -/
theorem wittDeltaStructure_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := inferInstance

/-- 同じWitt Frobeniusを持つδ構造は標準構造に一致する。 -/
theorem wittDeltaStructure_unique (D : DeltaStructure p (WittVector p k))
    (hD : D.frobeniusLift = WittVector.frobenius) : D = wittDeltaStructure p k :=
  (existsUnique_wittDeltaStructure p k).choose_spec.2 D hD

/-- 完全な標数p環の間の写像が誘導するWitt写像は標準δ構造と可換。
Witt Frobeniusの座標公式と、終域のp正則性によるδの復元を使う。 -/
theorem wittDeltaStructure_map_isDeltaHom {l : Type v} [CommRing l] [CharP l p]
    [PerfectRing l p] (f : k →+* l) :
    (wittDeltaStructure p k).IsDeltaHom (wittDeltaStructure p l) (WittVector.map f) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift
  · exact (wittDeltaStructure_isPerfect p l).p_mul_injective
  · intro x
    rw [wittDeltaStructure_frobeniusLift, wittDeltaStructure_frobeniusLift]
    apply WittVector.ext
    intro n
    simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

end SerrePositivity.BhattScholze

end WittDelta

/-! ## 受領F4による完全p進完備δ環のWitt復元

零環を含む復元環同型と標準商図式を、完全δ構造からのp正則性に接続する。
標準Witt δ構造との比較では剰余環のCharPを明示し、零環の一般復元と区別する。
-/

section PerfectDeltaWittRecovery

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全p進完備δ環は、零環を含めてそのmod p環のWitt環と同型（BS 著者版 Corollary 2.31 の対象上の Witt 復元）。 -/
def perfectDeltaWittRecoveryEquiv (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] : WittVector p (ModP A p) ≃+* A := by
  let := hD.perfectRing_mod_p
  exact strictPRecoveryEquiv p A hD.p_mul_injective

/-- 復元同型は標準mod p写像と第0Witt座標を両立させる。 -/
theorem perfectDeltaWittRecoveryEquiv_mod_p (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] :
    (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp
      (perfectDeltaWittRecoveryEquiv D hD).toRingHom = WittVector.constantCoeff := by
  let := hD.perfectRing_mod_p
  exact strictPRecoveryEquiv_mod_p p A hD.p_mul_injective

/-- 標準Witt環からp正則p進完備δ環への任意の環射はδ射（BS 著者版 Corollary 2.31 の射に関する帰結の一形態）。
Witt持上げの一意性を使い、環射の連続性は仮定しない。 -/
theorem wittDeltaStructure_ringHom_isDeltaHom_of_complete
    {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (D : DeltaStructure p A) [IsAdicComplete (Ideal.span {(p : A)}) A]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) (f : WittVector p k →+* A) :
    (wittDeltaStructure p k).IsDeltaHom D f := by
  let W := wittDeltaStructure p k
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hqp : q (p : A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hqfp : (q.comp f) (p : WittVector p k) = 0 := by
    change q (f (p : WittVector p k)) = 0
    rw [map_natCast, hqp]
  have he : f.comp W.frobeniusLift = D.frobeniusLift.comp f := by
    apply wittLift_unique
    apply RingHom.ext
    intro x
    change (q.comp f) (W.frobeniusLift x) = q (D.frobeniusLift (f x))
    rw [W.map_frobeniusLift_of_map_p_eq_zero (q.comp f) hqfp,
      D.map_frobeniusLift_of_map_p_eq_zero q hqp]
    rfl
  exact DeltaStructure.isDeltaHom_of_map_frobeniusLift f hp (RingHom.congr_fun he)

/-- 剰余環が標数pを持つ場合、復元同型の順射は標準Witt δ構造からのδ射。 -/
theorem perfectDeltaWittRecoveryEquiv_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [CharP (ModP A p) p] :
    letI := hD.perfectRing_mod_p
    (wittDeltaStructure p (ModP A p)).IsDeltaHom D
      (perfectDeltaWittRecoveryEquiv D hD).toRingHom := by
  let := hD.perfectRing_mod_p
  exact wittDeltaStructure_ringHom_isDeltaHom_of_complete D hD.p_mul_injective _

/-- 標準Witt δ構造との復元同型の逆射もδ射。 -/
theorem perfectDeltaWittRecoveryEquiv_symm_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect)
    [IsAdicComplete (Ideal.span {(p : A)}) A] [CharP (ModP A p) p] :
    letI := hD.perfectRing_mod_p
    D.IsDeltaHom (wittDeltaStructure p (ModP A p))
      (perfectDeltaWittRecoveryEquiv D hD).symm.toRingHom := by
  let := hD.perfectRing_mod_p
  exact (perfectDeltaWittRecoveryEquiv_isDeltaHom D hD).symm

end SerrePositivity.BhattScholze

end PerfectDeltaWittRecovery

/-! ## Witt環のdistinguished元の係数判定

BS 著者版 Lemma 2.33の具体的なWitt環の場合。
Teichmüller元はrank 1であり、標準δの第0係数は元の第1Witt係数に等しい。
既存の共通Witt単元判定を用い、第1係数でdistinguished性を判定する。
-/

section WittDistinguished

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- 完全係数環のTeichmüller元はrank 1。すべてのp冪根をTeichmüller写像で持ち上げ、
前段の一般δ環のrank 1定理を適用する。 -/
@[simp] theorem wittDeltaStructure_delta_teichmuller (x : k) :
    (wittDeltaStructure p k).delta (WittVector.teichmuller p x) = 0 := by
  apply DeltaStructure.delta_eq_zero_of_has_pow_roots
  intro n
  obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p ^ n)).2 x
  change y ^ p ^ n = x at hy
  refine ⟨WittVector.teichmuller p y, ?_⟩
  rw [← map_pow, hy]

/-- 標準Witt δの第0係数は元の第1Witt係数。
元を[x₀]+p*yと書き、δの加法・積公式を第0係数で比較する（BS 著者版 Lemma 2.33）。 -/
theorem wittDeltaStructure_delta_coeff_zero (d : WittVector p k) :
    ((wittDeltaStructure p k).delta d).coeff 0 = d.coeff 1 := by
  let D := wittDeltaStructure p k
  let q : WittVector p k →+* k := WittVector.constantCoeff
  have hqp : q (p : WittVector p k) = 0 := by simp [q, CharP.cast_eq_zero]
  have hm : d - WittVector.teichmuller p (d.coeff 0) ∈
      Ideal.span {(p : WittVector p k)} := by
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change q (d - WittVector.teichmuller p (d.coeff 0)) = 0
    rw [map_sub]
    simp only [q, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
  have he : d = WittVector.teichmuller p (d.coeff 0) + (p : WittVector p k) * y := by
    linear_combination hy
  have hc : q ((WittVector.teichmuller p (WittVector.teichmuller p (d.coeff 0)) +
      WittVector.teichmuller p ((p : WittVector p k) * y)).coeff 1) = 0 := by
    simp only [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, map_mul, hqp,
      zero_mul, WittVector.teichmuller_zero, add_zero, WittVector.teichmuller_coeff_pos p _ 1
        (by decide)]
  have hδ : q (D.delta d) = q y ^ p := by
    rw [he, D.delta_add, map_add, map_add, hc]
    rw [show D.delta (WittVector.teichmuller p (d.coeff 0)) = 0 from
      wittDeltaStructure_delta_teichmuller p k _]
    rw [map_zero, zero_add, add_zero, D.delta_mul]
    simp only [map_add, map_mul, map_pow, hqp, zero_pow (Fact.out : p.Prime).ne_zero,
      zero_mul, D.map_delta_p q, one_mul, add_zero, zero_add]
  have hd1 : d.coeff 1 = q y ^ p := by
    rw [he, witt_add_coeff_one, WittVector.teichmuller_coeff_pos p _ 1 (by decide)]
    simp only [WittVector.teichmuller_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.coeff_p_zero, zero_mul, WittVector.teichmuller_zero, add_zero,
      WittVector.teichmuller_coeff_pos p _ 1 (by decide), zero_add,
      witt_mul_coeff_one, WittVector.coeff_p_one, zero_pow (Fact.out : p.Prime).ne_zero,
      one_mul, CharP.cast_eq_zero]
    rfl
  exact hδ.trans hd1.symm

/-- 完全係数環のWitt元がdistinguishedであることと第1Witt係数の単元性は同値（BS 著者版 Lemma 2.33 の第 1 Witt 座標で書いた判定）。
δの第0係数の計算と既存共通Witt単元判定を使う。 -/
theorem wittDeltaStructure_isDistinguished_iff (d : WittVector p k) :
    (wittDeltaStructure p k).IsDistinguished d ↔ IsUnit (d.coeff 1) := by
  constructor
  · intro hd
    have h := hd.map (WittVector.constantCoeff : WittVector p k →+* k)
    simpa only [WittVector.constantCoeff_apply, wittDeltaStructure_delta_coeff_zero] using h
  · intro hd
    apply PerfectoidFrobeniusCriterion.witt_isUnit_of_constantCoeff k p
    rw [wittDeltaStructure_delta_coeff_zero]
    exact hd

/-- Teichmüller展開のpの係数でのdistinguished判定（BS 著者版 Lemma 2.33 の Teichmüller 係数で書いた判定）。
Mathlibの展開ではこの係数は逆Frobeniusを第1Witt係数に適用した元。
Frobeniusは単元性を保存・反映するので第1係数判定と同値になる。 -/
theorem wittDeltaStructure_isDistinguished_iff_teichmuller_coefficient (d : WittVector p k) :
    (wittDeltaStructure p k).IsDistinguished d ↔
      IsUnit ((_root_.frobeniusEquiv k p).symm (d.coeff 1)) := by
  apply (wittDeltaStructure_isDistinguished_iff p k d).trans
  simpa only [frobeniusEquiv_symm_pow_p] using
    (isUnit_pow_iff (a := (_root_.frobeniusEquiv k p).symm (d.coeff 1))
      (Fact.out : p.Prime).ne_zero)

end SerrePositivity.BhattScholze

end WittDistinguished

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 2.31" (partial := special) "圏同値ではなく対象ごと（A ≅ W(A/p)、W(R) の δ 構造の一意性、環準同型が δ 射）と本体 docstring に明記 ／ DOC1 照合：ok 4 件。完全 p 完備 δ 環からの環準同型が δ 射であることの強い形は Prism/PerfectPrismHomLift の perfectSource_ringHom_isDeltaHom（終域は p 進分離でよい） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.DeltaStructure.IsPerfect.perfectRing_mod_p
attribute [cite BS19 "Cor 2.31" (partial := special) "圏同値ではなく対象ごと（A ≅ W(A/p)、W(R) の δ 構造の一意性、環準同型が δ 射）と本体 docstring に明記 ／ DOC1 照合：ok 4 件。完全 p 完備 δ 環からの環準同型が δ 射であることの強い形は Prism/PerfectPrismHomLift の perfectSource_ringHom_isDeltaHom（終域は p 進分離でよい） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_wittDeltaStructure
attribute [cite BS19 "Cor 2.31" (partial := special) "圏同値ではなく対象ごと（A ≅ W(A/p)、W(R) の δ 構造の一意性、環準同型が δ 射）と本体 docstring に明記 ／ DOC1 照合：ok 4 件。完全 p 完備 δ 環からの環準同型が δ 射であることの強い形は Prism/PerfectPrismHomLift の perfectSource_ringHom_isDeltaHom（終域は p 進分離でよい） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.perfectDeltaWittRecoveryEquiv
attribute [cite BS19 "Cor 2.31" (partial := special) "圏同値ではなく対象ごと（A ≅ W(A/p)、W(R) の δ 構造の一意性、環準同型が δ 射）と本体 docstring に明記 ／ DOC1 照合：ok 4 件。完全 p 完備 δ 環からの環準同型が δ 射であることの強い形は Prism/PerfectPrismHomLift の perfectSource_ringHom_isDeltaHom（終域は p 進分離でよい） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.wittDeltaStructure_ringHom_isDeltaHom_of_complete
attribute [cite BS19 "Ex 2.6" (partial := special) "最後の主張（p 冪零な δ 環は零環）と Z 上の δ 構造の一意性の形だけ。Z_(p)（Lean は p と互いに素な整数での局所化）が δ 環の始対象であることは公開の existsUnique_primeLocalIntDeltaHom（Ex 2.21 の構成で使う） ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：relativeFreeDeltaStructure_int_eq（Z 上の二構成の一致で、Z_(p) の始性や δ 構造の一意性を主張する型ではない。） ／ DOC1 照合：ok 1 件 ／ 11-12 夜更新（ノート本文の更新時）。ℤ 上の δ 構造の存在と一意性は非公開の補題だけ"] _root_.SerrePositivity.BhattScholze.DeltaStructure.subsingleton_of_isNilpotent_p
attribute [cite BS19 "Lemma 2.28"] _root_.SerrePositivity.BhattScholze.DeltaStructure.p_mul_injective_of_frobeniusLift_injective
attribute [cite BS19 "Lemma 2.28"] _root_.SerrePositivity.BhattScholze.DeltaStructure.p_mul_injective_of_isReduced
attribute [cite BS19 "Lemma 2.28"] _root_.SerrePositivity.BhattScholze.DeltaStructure.torsion_calculation
attribute [cite BS19 "Lemma 2.32"] _root_.SerrePositivity.BhattScholze.DeltaStructure.delta_eq_zero_of_has_pow_roots
attribute [cite BS19 "Lemma 2.32"] _root_.SerrePositivity.BhattScholze.DeltaStructure.pow_p_dvd_delta_pow
attribute [cite BS19 "Lemma 2.33" (partial := special) "W(R) の Teichmüller 展開で述べる。Thm 3.10 の Witt 商計算（Prism/Perfectoid/WittQuotientTilt）に使用 ／ DOC1 照合：ok 2 件。本体は W(k) の標準 δ 構造の場合だけ（一般の完全 p 完備 A へは移していない） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff
attribute [cite BS19 "Lemma 2.33" (partial := special) "W(R) の Teichmüller 展開で述べる。Thm 3.10 の Witt 商計算（Prism/Perfectoid/WittQuotientTilt）に使用 ／ DOC1 照合：ok 2 件。本体は W(k) の標準 δ 構造の場合だけ（一般の完全 p 完備 A へは移していない） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.wittDeltaStructure_isDistinguished_iff_teichmuller_coefficient
