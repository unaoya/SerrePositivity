module

public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismBoundedTargetRigidity
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing

/-!
# André A1-a：完全な源からの環射の δ 保存性

## 概要

完全 δ 環から p 進分離な δ 環への環射は δ を自動的に保つ。
BS Lemma 4.8（著者版 pp.38–39）の一般有界標的への持上げの δ 判定部分。

## 方針

まず環射の剛性で Frobenius 持上げとの可換性を得る。二つの W₂ 射の第1座標の差は
p で消える導分となり、完全な源の p 冪近似で消える。原典の逆 Frobenius 極限とは異なる経路。

## 規約

標的の p 正則性は不要。環射の存在は本ファイルでは主張しない。

## 使われ方

一般有界 prism への基底環射を構成した後、その δ 保存性を追加仮定なく供給する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

omit [Fact p.Prime] in
private theorem additive_twisted_derivation_eq_zero
    (hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c)
    (g : A →+* B) (e : A →+ B)
    (hm : ∀ a b, e (a * b) = g a * e b + e a * g b)
    (he : ∀ a, (p : B) * e a = 0) : ∀ a, e a = 0 := by
  have h1 : e 1 = 0 := by
    have h := hm 1 1
    simp only [one_mul, map_one, mul_one] at h
    linear_combination -h
  have hn (n : ℕ) : e (n : A) = 0 := by
    simpa only [nsmul_one, map_nsmul, h1, nsmul_zero] using e.map_nsmul n (1 : A)
  have hpow (b : A) (n : ℕ) : e (b ^ n) = (n : B) * g b ^ (n - 1) * e b := by
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hm, map_pow, ih]
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
        ring
  intro a
  obtain ⟨b, c, ha⟩ := hA a
  rw [ha, map_add, hpow, hm, map_natCast, hn, zero_mul, add_zero, he, add_zero]
  calc
    (p : B) * g b ^ (p - 1) * e b = g b ^ (p - 1) * ((p : B) * e b) := by ring
    _ = 0 := by rw [he, mul_zero]

/-- 概要：完全な源から p 進分離な δ 標的への環射は Frobenius 持上げと可換。
方針：二つの合成射は mod p で一致するため、p 冪近似による環射の剛性を使う。
規約：標的の p 正則性は要求しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の δ 保存性の直接証明。 -/
theorem perfectSource_ringHom_map_frobenius
    (D : DeltaStructure p A) (hD : D.IsPerfect) (E : DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B] (f : A →+* B) :
    E.frobeniusLift.comp f = f.comp D.frobeniusLift := by
  have hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c := by
    intro a
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨b, D.delta b, hb.symm.trans (D.frobeniusLift_apply b)⟩
  apply ringHom_ext_of_pow_add_natCast_mul p hA (Ideal.span {(p : B)})
    (Ideal.mem_span_singleton_self _) _ _
  ext a
  simp only [RingHom.comp_apply, E.frobeniusLift_apply, D.frobeniusLift_apply,
    map_add, map_mul, map_pow, map_natCast]
  have hp : Ideal.Quotient.mk (Ideal.span {(p : B)}) (p : B) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hp' : (p : B ⧸ Ideal.span {(p : B)}) = 0 := (map_natCast _ p).symm.trans hp
  simp only [hp', zero_mul, add_zero]

/-- 概要：同じ第0成分と ghost 成分を持つ W₂ 射は p 冪近似を持つ源で一致。
方針：第1座標の差は p で消える導分となり、源の p 冪近似で消える。
規約：標的の p 正則性・完備性は不要。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の p ねじれを許す δ 判定。 -/
theorem wittTwoHom_ext_of_perfectSource_approximation
    (hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c)
    (f : A →+* B) (s t : A →+* WittTwo p B)
    (hs : (wittTwoProjection p B).comp s = f)
    (ht : (wittTwoProjection p B).comp t = f)
    (hghost : (wittTwoFrobenius p B).comp s = (wittTwoFrobenius p B).comp t) :
    s = t := by
  let e : A →+ B := {
    toFun a := (s a).coeff 1 - (t a).coeff 1
    map_zero' := by simp
    map_add' := by
      intro a b
      have hs' := wittTwoLift_delta_add f s hs a b
      have ht' := wittTwoLift_delta_add f t ht a b
      dsimp only at hs' ht'
      rw [hs', ht']
      abel }
  have he (a : A) : (p : B) * e a = 0 := by
    have h := RingHom.congr_fun hghost a
    simp only [RingHom.comp_apply, wittTwoFrobenius_apply,
      wittTwoLift_coeff_zero f s hs, wittTwoLift_coeff_zero f t ht] at h
    change (p : B) * ((s a).coeff 1 - (t a).coeff 1) = 0
    linear_combination h
  have hm (a b : A) : e (a * b) =
      ((wittTwoFrobenius p B).comp s) a * e b +
        e a * ((wittTwoFrobenius p B).comp s) b := by
    change (s (a * b)).coeff 1 - (t (a * b)).coeff 1 = _
    have hs' := wittTwoLift_delta_mul f s hs a b
    have ht' := wittTwoLift_delta_mul f t ht a b
    dsimp only at hs' ht'
    rw [hs', ht']
    simp only [RingHom.comp_apply, wittTwoFrobenius_apply,
      wittTwoLift_coeff_zero f s hs]
    change _ = (f a ^ p + (p : B) * (s a).coeff 1) *
      ((s b).coeff 1 - (t b).coeff 1) +
      ((s a).coeff 1 - (t a).coeff 1) * (f b ^ p + (p : B) * (s b).coeff 1)
    have h := he a
    change (p : B) * ((s a).coeff 1 - (t a).coeff 1) = 0 at h
    linear_combination -((s b).coeff 1 - (t b).coeff 1) * h
  have hz := additive_twisted_derivation_eq_zero hA
    ((wittTwoFrobenius p B).comp s) e hm he
  ext a i
  fin_cases i
  · exact (wittTwoLift_coeff_zero f s hs a).trans (wittTwoLift_coeff_zero f t ht a).symm
  · exact sub_eq_zero.mp (hz a)

/-- 概要：完全 δ 源から p 進分離な δ 標的への環射は δ を自動的に保つ。
方針：Frobenius 可換性を環射の剛性で得て、二つの W₂ 射を第1座標の導分で比較する。
規約：標的の p 正則性は不要。環射の存在は主張しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の一般有界 prism への基底射の δ 判定。 -/
theorem perfectSource_ringHom_isDeltaHom
    (D : DeltaStructure p A) (hD : D.IsPerfect) (E : DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B] (f : A →+* B) : D.IsDeltaHom E f := by
  apply (D.isDeltaHom_iff_sectionHom_comp E f).mpr
  apply wittTwoHom_ext_of_perfectSource_approximation (f := f)
  · intro a
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨b, D.delta b, hb.symm.trans (D.frobeniusLift_apply b)⟩
  · ext a
    simp only [RingHom.comp_apply, wittTwoProjection_apply, wittTwoMap_coeff, D.coeff_zero]
  · ext a
    exact E.coeff_zero (f a)
  · have h := perfectSource_ringHom_map_frobenius D hD E f
    ext a
    simp only [RingHom.comp_apply, wittTwoFrobenius_apply, wittTwoMap_coeff,
      D.coeff_zero, E.coeff_zero]
    have ha := RingHom.congr_fun h a
    simp only [RingHom.comp_apply, E.frobeniusLift_apply, D.frobeniusLift_apply,
      map_add, map_pow, map_mul, map_natCast] at ha
    exact ha.symm

/-- 概要：完全 δ 源から一般有界 prism への環射は δ を自動的に保つ。
方針：有界 prism の p 分離性を一般の δ 保存性定理へ渡す。
規約：標的の完全性・p 正則性は要求しない。環射は明示する。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の持上げた基底環射の δ 判定。 -/
theorem perfectSource_ringHom_isDeltaHom_to_boundedPrism
    (D : DeltaStructure p A) (hD : D.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (f : A →+* B) : D.IsDeltaHom Q.deltaStructure f := by
  let := boundedPrism_isHausdorff_prime Q hB
  exact perfectSource_ringHom_isDeltaHom D hD Q.deltaStructure f

end SerrePositivity.BhattScholze.Andre
