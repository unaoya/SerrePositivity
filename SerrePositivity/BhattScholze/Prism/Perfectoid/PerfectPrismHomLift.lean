module


public meta import SerrePositivity.Util.Citation
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientPerfectoid
public import SerrePositivity.CommutativeAlgebra.Witt.Lift
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prism.Bounded.Tilt
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-!
# 完全 prism からの射の一意な持ち上げ（BS 著者版 Lemma 4.8）

## 概要
完全 prism の商から完全な、または有界な向き付き prism の商への環射は、prism の射に一意に持ち上がる。
完全な源からの環射は δ を自動的に保ち、商上の値で決まる。Witt 商への射の一意な持ち上げも含む。

## 方針
原典の変形理論ではなく、tilt の比較と Witt 持ち上げの一意性による。

## 規約
標的は有界（原典は任意の prism）。prismatic site の対象は有界なので E3 には足りる。

## 使われ方
BS 著者版 Theorem 3.10 の充満忠実性、BS 著者版 Corollary 7.3、A0（完全試験 prism）。有界な標的の版は旧 Andre/Remark715 から移した。
-/

universe u v

/-! ## André A1-a：p 冪近似を持つ源の環射の分離性

## 概要

源の各元が b^p+p*c と書け、標的が p を含むイデアルで分離的なら、
そのイデアル商上で一致する二つの環射は等しい。
BS 著者版 Lemma 4.8（著者版 pp.38–39）、BS 著者版 Remark 7.15（p.62）の基底射の一意性への準備。

## 方針

冪差を幾何和と元の差の積に書く。幾何和は商で p 倍となるのでイデアルに入り、
二つの射の差を帰納的に全イデアル冪へ移す。原典の変形理論とは異なる直接計算。

## 規約

素数性・p 正則性・δ 構造はこの一般補題には不要。持上げの存在は結論しない。

## 使われ方

完全 prism から一般の有界 prism への射の一意性を、標的の p ねじれを許して証明する。
-/

@[expose] public noncomputable section PerfectSourceAdicRigidity

namespace SerrePositivity.BhattScholze
open scoped _root_.BigOperators
variable {B : Type v} [CommRing B]

/-- 概要：商で一致する二元の幾何和は、商で消える長さ p の倍数となる。
方針：商射で二元を同一視し、同じ元の幾何和の公式を使う。
規約：p は任意の自然数とし、p 自体がイデアルに入ることを要求する。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の環射の剛性の直接計算。 -/
theorem geomSum_mem_ideal_of_natCast_mem (p : ℕ) (I : Ideal B) (hp : (p : B) ∈ I)
    (x y : B) (hxy : x - y ∈ I) :
    (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) ∈ I := by
  let q := Ideal.Quotient.mk I
  have hq : q x = q y := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxy
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) = 0
  simp only [map_sum, map_mul, map_pow, hq]
  rw [geom_sum₂_self]
  have hpq : (p : B ⧸ I) = 0 := by
    exact (map_natCast q p).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  rw [hpq, zero_mul]

/-- 概要：p を含むイデアルで合同な二元の p 冪差は、差の所属冪より一段深く入る。
方針：幾何和のイデアル所属と元の差を乗算する。
規約：差の最初のイデアル所属と任意の n 冪所属を明示する。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の冪による一意性帰納。 -/
theorem pow_sub_pow_mem_ideal_succ (p : ℕ) (I : Ideal B) (hp : (p : B) ∈ I)
    (x y : B) (hxy : x - y ∈ I) (n : ℕ) (hn : x - y ∈ I ^ n) :
    x ^ p - y ^ p ∈ I ^ (n + 1) := by
  rw [← geom_sum₂_mul x y p, pow_succ']
  exact Ideal.mul_mem_mul (_root_.SerrePositivity.BhattScholze.geomSum_mem_ideal_of_natCast_mem p I hp x y hxy) hn

/-- 概要：p 冪近似を持つ源からの二つの環射は、標的の分離イデアル商で一致すれば等しい。
方針：源の表示 a=b^p+p*c と幾何和を使い、差を標的イデアルの全冪へ押し込む。
規約：源・標的の p 正則性や素数性は要求しない。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の一般有界試験 prism での一意性。 -/
theorem ringHom_ext_of_pow_add_natCast_mul (p : ℕ)
    {A : Type u} [CommRing A]
    (hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c)
    (I : Ideal B) (hp : (p : B) ∈ I) [IsHausdorff I B]
    (F G : A →+* B)
    (hFG : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp G) : F = G := by
  have hfirst (a : A) : F a - G a ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, sub_eq_zero]
    exact RingHom.congr_fun hFG a
  have hall (n : ℕ) : ∀ a : A, F a - G a ∈ I ^ n := by
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      obtain ⟨b, c, ha⟩ := hA a
      rw [ha, map_add, map_add, map_pow, map_pow, map_mul, map_mul,
        map_natCast, map_natCast]
      have he : F b ^ p + (p : B) * F c - (G b ^ p + (p : B) * G c) =
          (F b ^ p - G b ^ p) + (p : B) * (F c - G c) := by ring
      rw [he]
      apply Ideal.add_mem
      · exact _root_.SerrePositivity.BhattScholze.pow_sub_pow_mem_ideal_succ p I hp (F b) (G b) (hfirst b) n (ih b)
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hp (ih c)
  apply RingHom.ext
  intro a
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  apply SModEq.sub_mem.mpr
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hall n a

end SerrePositivity.BhattScholze

end PerfectSourceAdicRigidity

/-! ## André A1-a：完全な源から一般有界 prism への射の一意性

## 概要

完全 δ 環から有界 prism の台環への環射は、prism 商への合成で決まる。
完全 prism からの prism 射も商射で決まる。BS 著者版 Lemma 4.8（著者版 pp.38–39）の一意性。

## 方針

完全な源で a=b^p+p*δ(b) を供給し、標的の (p,d) 分離性と幾何和による剛性を使う。
原典の変形理論・逆極限による δ 判定とは異なる、差のイデアル冪による直接証明。

## 規約

標的の完全性・p 正則性は不要。持上げの存在はまだ結論しない。

## 使われ方

BS 著者版 Remark 7.15（著者版 p.62）の基底射の選択の一意性と入力圏の比較に使う。
-/

@[expose] public noncomputable section PerfectPrismBoundedTargetRigidity

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 概要：完全 δ 源から有界 prism への環射は、標準 prism 商への合成で決まる。
方針：完全 Frobenius による p 冪近似と標的の (p,d) 分離性で差を全冪に入れる。
規約：射の δ 保存性すらこの剛性には不要。標的の p 正則性を要求しない。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の一般有界標的での一意性。 -/
theorem ringHom_ext_to_boundedPrism_of_perfect_source
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (F G : A →+* B)
    (hFG : (Ideal.Quotient.mk Q.ideal).comp F = (Ideal.Quotient.mk Q.ideal).comp G) :
    F = G := by
  let Jp : Ideal B := Ideal.span {(p : B), Q.generator}
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete Q hB
  have hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c := by
    intro a
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨b, D.delta b, hb.symm.trans (D.frobeniusLift_apply b)⟩
  apply _root_.SerrePositivity.BhattScholze.ringHom_ext_of_pow_add_natCast_mul p hA Jp (Ideal.subset_span (by simp)) F G
  have hQI : Q.ideal ≤ Jp := by
    change Ideal.span {Q.generator} ≤ Jp
    apply Ideal.span_le.mpr
    intro x hx
    exact Ideal.subset_span (Set.mem_insert_of_mem _ hx)
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk Jp (F a) = Ideal.Quotient.mk Jp (G a)
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hQI
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, sub_eq_zero]
  exact RingHom.congr_fun hFG a

/-- 概要：完全 prism から有界 prism への射は、その誘導商射で一意に決まる（BS 著者版 Lemma 4.8 の標的が有界な向き付き prism の場合の一意性）。
方針：商射の合成公式で環射の剛性へ帰着する。
規約：標的を完全 prism に制限しない。持上げの存在は主張しない。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の基底持上げの一意性。 -/
theorem perfectPrismHom_ext_to_bounded_target
    (W : _root_.SerrePositivity.BhattScholze.OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (F G : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom W Q) (hFG : F.quotientMap = G.quotientMap) : F = G := by
  apply _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom.ext
  apply _root_.SerrePositivity.BhattScholze.ringHom_ext_to_boundedPrism_of_perfect_source W.deltaStructure hW Q hB
  rw [← _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom.quotientMap_comp_mk, ← _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom.quotientMap_comp_mk, hFG]

end SerrePositivity.BhattScholze

end PerfectPrismBoundedTargetRigidity

/-! ## André A1-a：完全な源からの環射の δ 保存性

## 概要

完全 δ 環から p 進分離な δ 環への環射は δ を自動的に保つ。
BS 著者版 Lemma 4.8（著者版 pp.38–39）の一般有界標的への持上げの δ 判定部分。

## 方針

まず環射の剛性で Frobenius 持上げとの可換性を得る。二つの W₂ 射の第1座標の差は
p で消える導分となり、完全な源の p 冪近似で消える。原典の逆 Frobenius 極限とは異なる経路。

## 規約

標的の p 正則性は不要。環射の存在は本ファイルでは主張しない。

## 使われ方

一般有界 prism への基底環射を構成した後、その δ 保存性を追加仮定なく供給する。
-/

@[expose] public noncomputable section PerfectSourceDeltaHom

namespace SerrePositivity.BhattScholze
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
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の δ 保存性の直接証明。 -/
theorem perfectSource_ringHom_map_frobenius
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (E : _root_.SerrePositivity.BhattScholze.DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B] (f : A →+* B) :
    E.frobeniusLift.comp f = f.comp D.frobeniusLift := by
  have hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c := by
    intro a
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨b, D.delta b, hb.symm.trans (D.frobeniusLift_apply b)⟩
  apply _root_.SerrePositivity.BhattScholze.ringHom_ext_of_pow_add_natCast_mul p hA (Ideal.span {(p : B)})
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
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の p ねじれを許す δ 判定。 -/
theorem wittTwoHom_ext_of_perfectSource_approximation
    (hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c)
    (f : A →+* B) (s t : A →+* _root_.SerrePositivity.BhattScholze.WittTwo p B)
    (hs : (_root_.SerrePositivity.BhattScholze.wittTwoProjection p B).comp s = f)
    (ht : (_root_.SerrePositivity.BhattScholze.wittTwoProjection p B).comp t = f)
    (hghost : (_root_.SerrePositivity.BhattScholze.wittTwoFrobenius p B).comp s = (_root_.SerrePositivity.BhattScholze.wittTwoFrobenius p B).comp t) :
    s = t := by
  let e : A →+ B := {
    toFun a := (s a).coeff 1 - (t a).coeff 1
    map_zero' := by simp
    map_add' := by
      intro a b
      have hs' := _root_.SerrePositivity.BhattScholze.wittTwoLift_delta_add f s hs a b
      have ht' := _root_.SerrePositivity.BhattScholze.wittTwoLift_delta_add f t ht a b
      dsimp only at hs' ht'
      rw [hs', ht']
      abel }
  have he (a : A) : (p : B) * e a = 0 := by
    have h := RingHom.congr_fun hghost a
    simp only [RingHom.comp_apply, _root_.SerrePositivity.BhattScholze.wittTwoFrobenius_apply,
      _root_.SerrePositivity.BhattScholze.wittTwoLift_coeff_zero f s hs, _root_.SerrePositivity.BhattScholze.wittTwoLift_coeff_zero f t ht] at h
    change (p : B) * ((s a).coeff 1 - (t a).coeff 1) = 0
    linear_combination h
  have hm (a b : A) : e (a * b) =
      ((_root_.SerrePositivity.BhattScholze.wittTwoFrobenius p B).comp s) a * e b +
        e a * ((_root_.SerrePositivity.BhattScholze.wittTwoFrobenius p B).comp s) b := by
    change (s (a * b)).coeff 1 - (t (a * b)).coeff 1 = _
    have hs' := _root_.SerrePositivity.BhattScholze.wittTwoLift_delta_mul f s hs a b
    have ht' := _root_.SerrePositivity.BhattScholze.wittTwoLift_delta_mul f t ht a b
    dsimp only at hs' ht'
    rw [hs', ht']
    simp only [RingHom.comp_apply, _root_.SerrePositivity.BhattScholze.wittTwoFrobenius_apply,
      _root_.SerrePositivity.BhattScholze.wittTwoLift_coeff_zero f s hs]
    change _ = (f a ^ p + (p : B) * (s a).coeff 1) *
      ((s b).coeff 1 - (t b).coeff 1) +
      ((s a).coeff 1 - (t a).coeff 1) * (f b ^ p + (p : B) * (s b).coeff 1)
    have h := he a
    change (p : B) * ((s a).coeff 1 - (t a).coeff 1) = 0 at h
    linear_combination -((s b).coeff 1 - (t b).coeff 1) * h
  have hz := _root_.SerrePositivity.BhattScholze.additive_twisted_derivation_eq_zero hA
    ((_root_.SerrePositivity.BhattScholze.wittTwoFrobenius p B).comp s) e hm he
  ext a i
  fin_cases i
  · exact (_root_.SerrePositivity.BhattScholze.wittTwoLift_coeff_zero f s hs a).trans (_root_.SerrePositivity.BhattScholze.wittTwoLift_coeff_zero f t ht a).symm
  · exact sub_eq_zero.mp (hz a)

/-- 概要：完全 δ 源から p 進分離な δ 標的への環射は δ を自動的に保つ。
方針：Frobenius 可換性を環射の剛性で得て、二つの W₂ 射を第1座標の導分で比較する。
規約：標的の p 正則性は不要。環射の存在は主張しない。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の一般有界 prism への基底射の δ 判定。 -/
theorem perfectSource_ringHom_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (E : _root_.SerrePositivity.BhattScholze.DeltaStructure p B)
    [IsHausdorff (Ideal.span {(p : B)}) B] (f : A →+* B) : D.IsDeltaHom E f := by
  apply (D.isDeltaHom_iff_sectionHom_comp E f).mpr
  apply _root_.SerrePositivity.BhattScholze.wittTwoHom_ext_of_perfectSource_approximation (f := f)
  · intro a
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨b, D.delta b, hb.symm.trans (D.frobeniusLift_apply b)⟩
  · ext a
    simp only [RingHom.comp_apply, _root_.SerrePositivity.BhattScholze.wittTwoProjection_apply, _root_.SerrePositivity.BhattScholze.wittTwoMap_coeff, D.coeff_zero]
  · ext a
    exact E.coeff_zero (f a)
  · have h := _root_.SerrePositivity.BhattScholze.perfectSource_ringHom_map_frobenius D hD E f
    ext a
    simp only [RingHom.comp_apply, _root_.SerrePositivity.BhattScholze.wittTwoFrobenius_apply, _root_.SerrePositivity.BhattScholze.wittTwoMap_coeff,
      D.coeff_zero, E.coeff_zero]
    have ha := RingHom.congr_fun h a
    simp only [RingHom.comp_apply, E.frobeniusLift_apply, D.frobeniusLift_apply,
      map_add, map_pow, map_mul, map_natCast] at ha
    exact ha.symm

/-- 概要：完全 δ 源から一般有界 prism への環射は δ を自動的に保つ。
方針：有界 prism の p 分離性を一般の δ 保存性定理へ渡す。
規約：標的の完全性・p 正則性は要求しない。環射は明示する。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の持上げた基底環射の δ 判定。 -/
theorem perfectSource_ringHom_isDeltaHom_to_boundedPrism
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (f : A →+* B) : D.IsDeltaHom Q.deltaStructure f := by
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_isHausdorff_prime Q hB
  exact _root_.SerrePositivity.BhattScholze.perfectSource_ringHom_isDeltaHom D hD Q.deltaStructure f

end SerrePositivity.BhattScholze

end PerfectSourceDeltaHom

/-! ## 完備distinguished Witt商への写像の忠実性

完全係数環からのWitt射は、商への射で決まる。
標準tilt比較射の単射性とPerfectionの普遍性を使う。
-/

@[expose] public noncomputable section WittQuotientHomFaithful

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime]
variable {k l : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
variable [CommRing l] [CharP l p] [PerfectRing l p]

private def residueMap (f : WittVector p k →+* WittVector p l) : k →+* l :=
  (WittVector.constantCoeff : WittVector p k →+* k).liftOfSurjective
    (WittVector.constantCoeff_surjective p) ⟨WittVector.constantCoeff.comp f, by
      rw [WittVector.ker_constantCoeff, Ideal.span_singleton_le_iff_mem]
      change (f (p : WittVector p k)).coeff 0 = 0
      rw [map_natCast, WittVector.coeff_p_zero]⟩

omit [PerfectRing l p] in
private theorem residueMap_coeff (f : WittVector p k →+* WittVector p l) (x : WittVector p k) :
    residueMap p f (x.coeff 0) = (f x).coeff 0 :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

private theorem residueMap_wittMap (f : WittVector p k →+* WittVector p l) :
    f = WittVector.map (residueMap p f) := by
  apply wittLift_unique
  apply RingHom.ext
  intro x
  apply (WittVector.quotientPEquiv (p := p) (k := l)).injective
  change (f x).coeff 0 = (WittVector.map (residueMap p f) x).coeff 0
  rw [WittVector.map_coeff, residueMap_coeff]

/-- 完備distinguished Witt商への射が一致すれば、元のWitt環への射が一致する。 -/
theorem wittQuotientHom_ext (d : WittVector p l)
    [IsAdicComplete (Ideal.span {d}) (WittVector p l)]
    [Fact (¬ IsUnit (p : WittVector p l ⧸ Ideal.span {d}))]
    (hd : (wittDeltaStructure p l).IsDistinguished d)
    (f g : WittVector p k →+* WittVector p l)
    (h : (Ideal.Quotient.mk (Ideal.span {d})).comp f =
      (Ideal.Quotient.mk (Ideal.span {d})).comp g) : f = g := by
  let : IsAdicComplete (Ideal.span {(p : WittVector p l ⧸ Ideal.span {d})})
      (WittVector p l ⧸ Ideal.span {d}) :=
    (wittDeltaStructure_isPerfect p l).distinguished_quotient_isAdicComplete hd
  let L := wittQuotientTiltMap p l d
  have he : L.comp (residueMap p f) = L.comp (residueMap p g) := by
    apply Perfection.hom_ext
    intro x
    change PreTilt.coeff 0 (L (residueMap p f x)) =
      PreTilt.coeff 0 (L (residueMap p g x))
    rw [wittQuotientTiltMap_coeff, wittQuotientTiltMap_coeff]
    simp only [Function.iterate_zero, id_eq, wittQuotientCoefficientMap_apply]
    have hx := RingHom.congr_fun h (WittVector.teichmuller p x)
    rw [residueMap_wittMap p f, residueMap_wittMap p g] at hx
    simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
      congrArg (Ideal.Quotient.mk (Ideal.span {(p : WittVector p l ⧸ Ideal.span {d})})) hx
  have hres : residueMap p f = residueMap p g := by
    apply RingHom.ext
    intro x
    apply wittQuotientTiltMap_injective p l d hd
    exact RingHom.congr_fun he x
  rw [residueMap_wittMap p f, residueMap_wittMap p g, hres]

end SerrePositivity.BhattScholze

end WittQuotientHomFaithful

/-! ## 一般の完備distinguished Witt商の射の唯一持上げ -/

@[expose] public noncomputable section WittQuotientHomLift

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime]
variable {k l : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
variable [CommRing l] [CharP l p] [PerfectRing l p]

/-- 完備distinguished Witt商間の環射は、唯一の標準δ射に持ち上がる。 -/
theorem existsUnique_wittQuotientHomLift (d : WittVector p k) (e : WittVector p l)
    [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
    [IsAdicComplete (Ideal.span {e}) (WittVector p l)]
    [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
    [Fact (¬ IsUnit (p : WittVector p l ⧸ Ideal.span {e}))]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (he : (wittDeltaStructure p l).IsDistinguished e)
    (g : WittVector p k ⧸ Ideal.span {d} →+* WittVector p l ⧸ Ideal.span {e}) :
    ∃! f : WittVector p k →+* WittVector p l,
      (wittDeltaStructure p k).IsDeltaHom (wittDeltaStructure p l) f ∧
      (Ideal.Quotient.mk (Ideal.span {e})).comp f =
        g.comp (Ideal.Quotient.mk (Ideal.span {d})) := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let T := WittVector p l ⧸ Ideal.span {e}
  let : IsAdicComplete (Ideal.span {(p : S)}) S :=
    (wittDeltaStructure_isPerfect p k).distinguished_quotient_isAdicComplete hd
  let : IsAdicComplete (Ideal.span {(p : T)}) T :=
    (wittDeltaStructure_isPerfect p l).distinguished_quotient_isAdicComplete he
  let es := RingEquiv.ofBijective (wittQuotientFontaineMap p k d)
    (wittCompleteQuotientFontaineMap_bijective p k d hd)
  let et := RingEquiv.ofBijective (wittQuotientFontaineMap p l e)
    (wittCompleteQuotientFontaineMap_bijective p l e he)
  let m : WittVector p (PreTilt S p) →+* WittVector p (PreTilt T p) :=
    WittVector.map (Perfection.map p (modPMap p g))
  let f := et.symm.toRingHom.comp (m.comp es.toRingHom)
  have het : (Ideal.Quotient.mk (Ideal.span {e})).comp et.symm.toRingHom =
      WittVector.fontaineTheta T p := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := et.surjective x
    change Ideal.Quotient.mk _ (et.symm (et y)) = WittVector.fontaineTheta T p (et y)
    rw [et.symm_apply_apply]
    exact (RingHom.congr_fun (wittQuotientFontaineMap_comp_fontaineTheta p l e) y).symm
  have hfg : (Ideal.Quotient.mk (Ideal.span {e})).comp f =
      g.comp (Ideal.Quotient.mk (Ideal.span {d})) := by
    change (Ideal.Quotient.mk _).comp (et.symm.toRingHom.comp (m.comp es.toRingHom)) = _
    rw [← RingHom.comp_assoc, het, ← RingHom.comp_assoc,
      fontaineTheta_natural p g, RingHom.comp_assoc]
    change g.comp ((WittVector.fontaineTheta S p).comp (wittQuotientFontaineMap p k d)) = _
    rw [wittQuotientFontaineMap_comp_fontaineTheta]
  refine ⟨f, ⟨?_, hfg⟩, ?_⟩
  · exact ((wittQuotientFontaineMap_isDeltaHom p l e).symm).comp
      ((wittDeltaStructure_map_isDeltaHom p (PreTilt S p)
        (Perfection.map p (modPMap p g))).comp (wittQuotientFontaineMap_isDeltaHom p k d))
  · intro h hh
    exact wittQuotientHom_ext p e he h f (hh.2.trans hfg.symm)

end SerrePositivity.BhattScholze

end WittQuotientHomLift

/-! ## 一般の完全prism商の射の一意持上げ

F4のWitt復元と一般Witt商の持上げを合成する。商のp正則性は要求しない。
-/

@[expose] public noncomputable section PerfectPrismHomLift

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- pが非可逆な商を持つ完全prism間では、任意の商射は唯一のprism射に持ち上がる（BS 著者版 Theorem 3.10 の完全 prism 間の射の持ち上げ）。 -/
theorem existsUnique_perfectPrismHomLift
    (P : OrientedPrism p A) (Q : OrientedPrism p B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    [Fact (¬ IsUnit (p : A ⧸ P.ideal))] [Fact (¬ IsUnit (p : B ⧸ Q.ideal))]
    (g : A ⧸ P.ideal →+* B ⧸ Q.ideal) :
    ∃! f : OrientedPrism.Hom P Q, f.quotientMap = g := by
  let : Fact (¬ IsUnit (p : A)) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : A ⧸ P.ideal))
    (by simpa only [map_natCast] using h.map (Ideal.Quotient.mk P.ideal))⟩
  let : Fact (¬ IsUnit (p : B)) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
    (by simpa only [map_natCast] using h.map (Ideal.Quotient.mk Q.ideal))⟩
  let := hP.perfectRing_mod_p
  let := hQ.perfectRing_mod_p
  let k := ModP A p
  let l := ModP B p
  let ea := perfectPrismWittRecoveryEquiv P hP
  let eb := perfectPrismWittRecoveryEquiv Q hQ
  let d := perfectPrismWittGenerator P hP
  let e := perfectPrismWittGenerator Q hQ
  have hd := perfectPrismWittGenerator_isDistinguished P hP
  have he := perfectPrismWittGenerator_isDistinguished Q hQ
  let : IsAdicComplete (Ideal.span {d}) (WittVector p k) :=
    perfectPrismWitt_isAdicComplete_generator P hP
  let : IsAdicComplete (Ideal.span {e}) (WittVector p l) :=
    perfectPrismWitt_isAdicComplete_generator Q hQ
  let qa : WittVector p k ⧸ Ideal.span {d} ≃+* A ⧸ P.ideal :=
    perfectPrismWittQuotientEquiv P hP
  let qb : WittVector p l ⧸ Ideal.span {e} ≃+* B ⧸ Q.ideal :=
    perfectPrismWittQuotientEquiv Q hQ
  let : Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d})) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : A ⧸ P.ideal))
    (by simpa only [map_natCast] using h.map qa.toRingHom)⟩
  let : Fact (¬ IsUnit (p : WittVector p l ⧸ Ideal.span {e})) :=
    ⟨fun h ↦ (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
    (by simpa only [map_natCast] using h.map qb.toRingHom)⟩
  let gg := qb.symm.toRingHom.comp (g.comp qa.toRingHom)
  obtain ⟨F, hF, _⟩ := existsUnique_wittQuotientHomLift p d e hd he gg
  let f := eb.toRingHom.comp (F.comp ea.symm.toRingHom)
  have hfg : (Ideal.Quotient.mk Q.ideal).comp f =
      g.comp (Ideal.Quotient.mk P.ideal) := by
    apply RingHom.ext
    intro a
    obtain ⟨x, rfl⟩ := ea.surjective a
    have hh := congrArg qb (RingHom.congr_fun hF.2 x)
    change qb (Ideal.Quotient.mk _ (F x)) =
      qb (qb.symm (g (qa (Ideal.Quotient.mk _ x)))) at hh
    rw [qb.apply_symm_apply] at hh
    change Ideal.Quotient.mk Q.ideal (eb (F (ea.symm (ea x)))) =
      g (Ideal.Quotient.mk P.ideal (ea x))
    rw [ea.symm_apply_apply]
    exact hh
  have hdelta : P.deltaStructure.IsDeltaHom Q.deltaStructure f :=
    (perfectPrismWittRecoveryEquiv_isDeltaHom Q hQ).comp
      (hF.1.comp (perfectPrismWittRecoveryEquiv_symm_isDeltaHom P hP))
  have hI : P.ideal ≤ Q.ideal.comap f := by
    intro x hx
    change f x ∈ Q.ideal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := RingHom.congr_fun hfg x
    change Ideal.Quotient.mk Q.ideal (f x) = g (Ideal.Quotient.mk P.ideal x) at hh
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at hh
    exact hh
  let H : OrientedPrism.Hom P Q := { f with map_delta := hdelta, ideal_le := hI }
  have hHg : H.quotientMap = g := by
    apply Ideal.Quotient.ringHom_ext
    exact hfg
  refine ⟨H, hHg, ?_⟩
  intro K hK
  apply OrientedPrism.Hom.ext
  have heq : (Ideal.Quotient.mk Q.ideal).comp K.toRingHom =
      (Ideal.Quotient.mk Q.ideal).comp H.toRingHom := by
    rw [← OrientedPrism.Hom.quotientMap_comp_mk, ← OrientedPrism.Hom.quotientMap_comp_mk,
      hK, hHg]
  have hw : eb.symm.toRingHom.comp (K.toRingHom.comp ea.toRingHom) =
      eb.symm.toRingHom.comp (H.toRingHom.comp ea.toRingHom) := by
    apply wittQuotientHom_ext p e he
    apply RingHom.ext
    intro x
    have hh := RingHom.congr_fun heq (ea x)
    have h := congrArg qb.symm hh
    change Ideal.Quotient.mk _ (eb.symm (K.toRingHom (ea x))) =
      Ideal.Quotient.mk _ (eb.symm (H.toRingHom (ea x)))
    exact (perfectPrismWittQuotientEquiv_symm_mk Q hQ (K.toRingHom (ea x))).symm.trans
      (h.trans (perfectPrismWittQuotientEquiv_symm_mk Q hQ (H.toRingHom (ea x))))
  apply RingHom.ext
  intro a
  obtain ⟨x, rfl⟩ := ea.surjective a
  apply eb.symm.injective
  exact RingHom.congr_fun hw x

end SerrePositivity.BhattScholze

end PerfectPrismHomLift

/-! ## André A1-a：完全 prism から一般有界 prism への商射の持上げ

## 概要

完全 prism の商から有界 prism の商への環射は、唯一の prism 射へ持ち上がる。
BS 著者版 Lemma 4.8（著者版 pp.38–39）の向き付き有界標的での証明。

## 方針

完全源を Witt 環として復元し、商での mod p 射を tilt へ持ち上げる。
標的とその prism 商の tilt 比較の逆と Fontaine 写像を合成する。
商図式は Witt 持上げの一意性で確認し、δ 保存性を完全源の剛性から得る。
原典の変形理論と逆 Frobenius 極限とは異なる経路。

## 規約

標的の完全性・p 正則性・非零性は要求しない。有界性を明示し、零商も含める。
一般 Cartier イデアルを持つ向きなし prism への比較は本ファイルには含まない。

## 使われ方

BS 著者版 Remark 7.15（著者版 p.62）の絶対入力対象に、完全基底からの一意な基底射を供給する。
-/

@[expose] public noncomputable section PerfectPrismBoundedTargetLift

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

omit [Fact p.Prime] in
private theorem prime_nonunit_of_complete {C : Type*} [CommRing C] [Nontrivial C]
    [IsAdicComplete (Ideal.span {(p : C)}) C] : ¬ IsUnit (p : C) := by
  intro h
  have ht : Ideal.span {(p : C)} = ⊤ := Ideal.span_singleton_eq_top.mpr h
  have hz : (1 : C) = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {(p : C)})
    intro n
    apply SModEq.sub_mem.mpr
    simp [ht, Ideal.top_pow]
  exact one_ne_zero hz

private theorem exists_perfectPrismRingHomLift_nonunit
    (W : _root_.SerrePositivity.BhattScholze.OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    [Fact (¬ IsUnit (p : B ⧸ Q.ideal))]
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃ F : A →+* B, (Ideal.Quotient.mk Q.ideal).comp F =
      g.comp (Ideal.Quotient.mk W.ideal) := by
  let qA := Ideal.Quotient.mk W.ideal
  let qB := Ideal.Quotient.mk Q.ideal
  let : Fact (¬ IsUnit (p : B)) := ⟨fun h =>
    (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
      (by simpa only [map_natCast] using h.map qB)⟩
  let : Fact (¬ IsUnit (p : A)) := ⟨fun h =>
    (Fact.out : ¬ IsUnit (p : B ⧸ Q.ideal))
      (by simpa only [map_natCast] using h.map (g.comp qA))⟩
  let := W.isAdicComplete_p_of_perfect hW
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_isAdicComplete_prime Q hB
  let := _root_.SerrePositivity.BhattScholze.boundedPrism_quotient_isAdicComplete_prime Q hB
  let := hW.perfectRing_mod_p
  let k := ModP A p
  let ea := _root_.SerrePositivity.BhattScholze.perfectPrismWittRecoveryEquiv W hW
  let eQ := _root_.SerrePositivity.BhattScholze.boundedPrism_preTiltQuotientEquiv Q hB
  let s : k →+* ModP (B ⧸ Q.ideal) p := _root_.SerrePositivity.modPMap p (g.comp qA)
  let l : k →+* PreTilt (B ⧸ Q.ideal) p := Perfection.lift p k _ s
  let t : k →+* PreTilt B p := eQ.symm.toRingHom.comp l
  let Fw : WittVector p k →+* B := (WittVector.fontaineTheta B p).comp (WittVector.map t)
  have hFw : qB.comp Fw = (g.comp qA).comp ea.toRingHom := by
    apply _root_.SerrePositivity.wittLift_unique
    ext x
    have hm := congrArg (_root_.SerrePositivity.modPMap p qB)
      (WittVector.mk_fontaineTheta (WittVector.map t x))
    rw [WittVector.map_coeff] at hm
    have ht : _root_.SerrePositivity.modPMap p qB (PreTilt.coeff 0 (t (x.coeff 0))) = s (x.coeff 0) := by
      change PreTilt.coeff 0 (eQ (eQ.symm (l (x.coeff 0)))) = s (x.coeff 0)
      rw [eQ.apply_symm_apply]
      rfl
    have hea : Ideal.Quotient.mk (Ideal.span {(p : A)}) (ea x) = x.coeff 0 :=
      RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.perfectDeltaWittRecoveryEquiv_mod_p W.deltaStructure hW) x
    change Ideal.Quotient.mk (Ideal.span {(p : B ⧸ Q.ideal)}) (qB (Fw x)) =
      Ideal.Quotient.mk (Ideal.span {(p : B ⧸ Q.ideal)}) (g (qA (ea x)))
    calc
      _ = _root_.SerrePositivity.modPMap p qB (PreTilt.coeff 0 (t (x.coeff 0))) := hm
      _ = s (x.coeff 0) := ht
      _ = _ := by rw [← hea]; rfl
  refine ⟨Fw.comp ea.symm.toRingHom, ?_⟩
  ext a
  exact (RingHom.congr_fun hFw (ea.symm a)).trans
    (congrArg (g.comp qA) (ea.apply_symm_apply a))

/-- 概要：完全 prism の商射は一般有界 prism の台環へ唯一の環射として持ち上がる（BS 著者版 Lemma 4.8 の標的が有界な向き付き prism の場合の環射表示）。
方針：非零商では tilt 比較と Fontaine 写像、零商では生成元完備性を使う。
規約：標的の完全性・p 正則性・非零性を仮定しない。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）の環射の存在と一意性。 -/
theorem existsUnique_perfectPrismRingHomLift_to_bounded
    (W : _root_.SerrePositivity.BhattScholze.OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃! F : A →+* B, (Ideal.Quotient.mk Q.ideal).comp F =
      g.comp (Ideal.Quotient.mk W.ideal) := by
  have hex : ∃ F : A →+* B, (Ideal.Quotient.mk Q.ideal).comp F =
      g.comp (Ideal.Quotient.mk W.ideal) := by
    rcases subsingleton_or_nontrivial (B ⧸ Q.ideal) with hs | hn
    · let : IsAdicComplete Q.ideal B := Q.isAdicComplete_generator
      let := hs
      have ht : Q.ideal = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
      have hz : (1 : B) = 0 := by
        apply IsHausdorff.haus' (I := Q.ideal)
        intro n
        apply SModEq.sub_mem.mpr
        simp [ht, Ideal.top_pow]
      let : Subsingleton B := subsingleton_of_zero_eq_one hz.symm
      exact ⟨{ toFun := fun _ => 0
               map_zero' := rfl
               map_one' := Subsingleton.elim _ _
               map_add' := fun _ _ => by simp
               map_mul' := fun _ _ => by simp }, by ext a; exact hs.elim _ _⟩
    · let := _root_.SerrePositivity.BhattScholze.boundedPrism_quotient_isAdicComplete_prime Q hB
      let : Fact (¬ IsUnit (p : B ⧸ Q.ideal)) := ⟨_root_.SerrePositivity.BhattScholze.prime_nonunit_of_complete⟩
      exact _root_.SerrePositivity.BhattScholze.exists_perfectPrismRingHomLift_nonunit W hW Q hB g
  obtain ⟨F, hF⟩ := hex
  refine ⟨F, hF, ?_⟩
  intro G hG
  exact _root_.SerrePositivity.BhattScholze.ringHom_ext_to_boundedPrism_of_perfect_source W.deltaStructure hW Q hB G F
    (hG.trans hF.symm)

/-- 概要：完全 prism の商射は一般有界 prism へ唯一の prism 射として持ち上がる（BS 著者版 Lemma 4.8 の標的が有界な向き付き prism の場合）。
方針：環射の一意持上げに自動的な δ 保存性と商図式からのイデアル保存性を付ける。
規約：向きは生成元の厳密な保存を要求せず、標的の完全性・p 正則性も不要。
使われ方：BS 著者版 Lemma 4.8（著者版 pp.38–39）と BS 著者版 Remark 7.15（p.62）の絶対入力圏。 -/
theorem existsUnique_perfectPrismHomLift_to_bounded
    (W : _root_.SerrePositivity.BhattScholze.OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (g : A ⧸ W.ideal →+* B ⧸ Q.ideal) :
    ∃! F : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom W Q, F.quotientMap = g := by
  obtain ⟨f, hf, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismRingHomLift_to_bounded W hW Q hB g
  let F : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom W Q := {
    toRingHom := f
    map_delta := _root_.SerrePositivity.BhattScholze.perfectSource_ringHom_isDeltaHom_to_boundedPrism W.deltaStructure hW Q hB f
    ideal_le := by
      intro a ha
      change f a ∈ Q.ideal
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have h := RingHom.congr_fun hf a
      change Ideal.Quotient.mk Q.ideal (f a) = g (Ideal.Quotient.mk W.ideal a) at h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at h
      exact h }
  have hF : F.quotientMap = g := by
    apply Ideal.Quotient.ringHom_ext
    exact hf
  exact ⟨F, hF, fun G hG => _root_.SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target W hW Q hB G F
    (hG.trans hF.symm)⟩

end SerrePositivity.BhattScholze

end PerfectPrismBoundedTargetLift

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 2.31" (partial := special) "圏同値ではなく対象ごと（A ≅ W(A/p)、W(R) の δ 構造の一意性、環準同型が δ 射）と本体 docstring に明記 ／ DOC1 照合：ok 4 件。完全 p 完備 δ 環からの環準同型が δ 射であることの強い形は Prism/PerfectPrismHomLift の perfectSource_ringHom_isDeltaHom（終域は p 進分離でよい） ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.perfectSource_ringHom_isDeltaHom
attribute [cite BS19 "Lemma 4.8" (partial := special) "標的が有界な向き付き prism の場合（site の対象は有界なので十分）。原典の任意の標的は不要。A5 の完全 site ≃ Perfd_{S/} に使う ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded
attribute [cite BS19 "Lemma 4.8" (partial := special) "標的が有界な向き付き prism の場合（site の対象は有界なので十分）。原典の任意の標的は不要。A5 の完全 site ≃ Perfd_{S/} に使う ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismRingHomLift_to_bounded
attribute [cite BS19 "Lemma 4.8" (partial := special) "標的が有界な向き付き prism の場合（site の対象は有界なので十分）。原典の任意の標的は不要。A5 の完全 site ≃ Perfd_{S/} に使う ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target
attribute [cite BS19 "Thm 3.10" (partial := special) "圏同値ではなく三つの事実（商の perfectoid 性・perfectoid 環の prism 表示・射の持ち上げ）で（D8）。絶対の圏同値は本体にも drafts にもない（drafts/A5 の perfectSiteEquivPerfectoidUnder は固定基底の上の相対版、Lemma 4.8 の系） ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift
