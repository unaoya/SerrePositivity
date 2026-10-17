module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# André A1-a：p 冪近似を持つ源の環射の分離性

## 概要

源の各元が b^p+p*c と書け、標的が p を含むイデアルで分離的なら、
そのイデアル商上で一致する二つの環射は等しい。
BS Lemma 4.8（著者版 pp.38–39）、Rem 7.15（p.62）の基底射の一意性への準備。

## 方針

冪差を幾何和と元の差の積に書く。幾何和は商で p 倍となるのでイデアルに入り、
二つの射の差を帰納的に全イデアル冪へ移す。原典の変形理論とは異なる直接計算。

## 規約

素数性・p 正則性・δ 構造はこの一般補題には不要。持上げの存在は結論しない。

## 使われ方

完全 prism から一般の有界 prism への射の一意性を、標的の p ねじれを許して証明する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
open scoped BigOperators
variable {B : Type v} [CommRing B]

/-- 概要：商で一致する二元の幾何和は、商で消える長さ p の倍数となる。
方針：商射で二元を同一視し、同じ元の幾何和の公式を使う。
規約：p は任意の自然数とし、p 自体がイデアルに入ることを要求する。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の環射の剛性の直接計算。 -/
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
使われ方：BS Lemma 4.8（著者版 pp.38–39）の冪による一意性帰納。 -/
theorem pow_sub_pow_mem_ideal_succ (p : ℕ) (I : Ideal B) (hp : (p : B) ∈ I)
    (x y : B) (hxy : x - y ∈ I) (n : ℕ) (hn : x - y ∈ I ^ n) :
    x ^ p - y ^ p ∈ I ^ (n + 1) := by
  rw [← geom_sum₂_mul x y p, pow_succ']
  exact Ideal.mul_mem_mul (geomSum_mem_ideal_of_natCast_mem p I hp x y hxy) hn

/-- 概要：p 冪近似を持つ源からの二つの環射は、標的の分離イデアル商で一致すれば等しい。
方針：源の表示 a=b^p+p*c と幾何和を使い、差を標的イデアルの全冪へ押し込む。
規約：源・標的の p 正則性や素数性は要求しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の一般有界試験 prism での一意性。 -/
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
      · exact pow_sub_pow_mem_ideal_succ p I hp (F b) (G b) (hfirst b) n (ih b)
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hp (ih c)
  apply RingHom.ext
  intro a
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  apply SModEq.sub_mem.mpr
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hall n a

end SerrePositivity.BhattScholze.Andre
