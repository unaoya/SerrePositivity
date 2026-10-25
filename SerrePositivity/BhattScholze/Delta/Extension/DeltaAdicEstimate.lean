module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps

/-!
# δ とイデアル冪の評価（BS 著者版 Lemma 2.17 の連続性）

## 概要
環射 f を第 0 座標とする W₂ への持ち上げの第 1 座標（相対 δ）の加法・乗法公式とイデアル冪の評価、
その特別な場合として p ∈ I なら δ(I^{n+1}) ⊂ Iⁿ。

## 方針
加法公式の補正項がイデアルに入ることと積公式から、冪の指数を一つずつ落とす。

## 規約
有限生成性・p 正則性・完備性は不要。

## 使われ方
古典的 I 進完備化への延長（Extension/DeltaAdicCompletion）、相対自由 δ 環の有限段の計算（Free/Finite）。
-/

@[expose] public noncomputable section
universe u v w

/-! ## 環射に沿うW₂持上げの相対δ評価（旧 Delta/Free/RelativeDeltaEstimate.lean）

環射fを第0座標とするW₂持上げsの第1座標を、相対δとして扱う。
通常δ構造や有限段の計算射を再定義せず、イデアル冪評価と通常剰余公式を共有する。
-/

section RelativeDeltaEstimate

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Witt加法繰上りは第2引数を含む任意のイデアルに属する。
商へのWitt射を使い、pを約分しない。 -/
theorem wittAdditionCarry_mem_of_right_mem (I : Ideal R) (x y : R) (hy : y ∈ I) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
    WittVector.map_teichmuller, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  simp

variable {S : Type v} [CommRing S]
variable (f : R →+* S) (s : R →+* WittTwo p S)
variable (hs : (wittTwoProjection p S).comp s = f)
local notation "δ" => fun x ↦ TruncatedWittVector.coeff (1 : Fin 2) (s x)
include hs

/-- 相対W₂持上げの第0座標は指定した環射。 -/
theorem wittTwoLift_coeff_zero (x : R) : (s x).coeff 0 = f x :=
  (wittTwoProjection_apply p S (s x)).symm.trans (RingHom.congr_fun hs x)

/-- 相対δの加法公式。補正項の二入力は指定した環射の像。 -/
theorem wittTwoLift_delta_add (x y : R) :
    δ (x + y) = δ x + δ y +
      (WittVector.teichmuller p (f x) + WittVector.teichmuller p (f y)).coeff 1 := by
  change (s (x + y)).coeff 1 = _
  rw [map_add]
  change ((s x).out + (s y).out).coeff 1 = _
  rw [witt_add_coeff_one]
  simp [TruncatedWittVector.out, wittTwoLift_coeff_zero f s hs]

/-- 相対δの積公式。終域でのp正則性を要求しない。 -/
theorem wittTwoLift_delta_mul (x y : R) :
    δ (x * y) = f x ^ p * δ y + δ x * f y ^ p + (p : S) * δ x * δ y := by
  change (s (x * y)).coeff 1 = _
  rw [map_mul]
  change ((s x).out * (s y).out).coeff 1 = _
  rw [witt_mul_coeff_one]
  simp [TruncatedWittVector.out, wittTwoLift_coeff_zero f s hs]

/-- pを含む終域イデアルの逆像のn+1乗は、相対δでそのイデアルのn乗に入る。
仮定は逆像イデアルの冪であり、冪イデアルへの像の所属ではない。 -/
theorem wittTwoLift_delta_mem_pow (J : Ideal S) (hp : (p : S) ∈ J)
    (n : ℕ) (x : R) (hx : x ∈ (J.comap f) ^ (n + 1)) : δ x ∈ J ^ n := by
  let I := J.comap f
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hmul : x ∈ (I ^ (n + 1)) * I := by simpa only [I, pow_succ] using hx
    have he : f x ∈ J ^ (n + 1) ∧ δ x ∈ J ^ (n + 1) := by
      refine Submodule.mul_induction_on (C := fun z ↦
        f z ∈ J ^ (n + 1) ∧ δ z ∈ J ^ (n + 1)) hmul ?_ ?_
      · intro a ha b hb
        have ha' : f a ∈ J ^ (n + 1) := Ideal.le_comap_pow f (n + 1) ha
        have hb' : f b ∈ J := hb
        constructor
        · rw [map_mul]
          exact (J ^ (n + 1)).mul_mem_right _ ha'
        · rw [wittTwoLift_delta_mul f s hs]
          apply (J ^ (n + 1)).add_mem
          · apply (J ^ (n + 1)).add_mem
            · exact (J ^ (n + 1)).mul_mem_right _
                ((J ^ (n + 1)).pow_mem_of_mem ha' p (Fact.out : p.Prime).pos)
            · have hprod := Ideal.mul_mem_mul (ih a ha)
                (J.pow_mem_of_mem hb' p (Fact.out : p.Prime).pos)
              simpa only [pow_succ] using hprod
          · have hprod := Ideal.mul_mem_mul (ih a ha) hp
            have hprod' : δ a * (p : S) ∈ J ^ (n + 1) := by
              simpa only [pow_succ] using hprod
            simpa only [mul_comm, mul_left_comm, mul_assoc] using
              (J ^ (n + 1)).mul_mem_right (δ b) hprod'
      · intro a b ha hb
        constructor
        · rw [map_add]
          exact (J ^ (n + 1)).add_mem ha.1 hb.1
        · rw [wittTwoLift_delta_add f s hs]
          exact (J ^ (n + 1)).add_mem ((J ^ (n + 1)).add_mem ha.2 hb.2)
            (wittAdditionCarry_mem_of_right_mem (J ^ (n + 1)) _ _ hb.1)
    exact he.2

/-- 逆像イデアルのn+1乗の摂動による相対δの変化は、終域イデアルのn乗に入る。 -/
theorem wittTwoLift_delta_add_sub_mem_pow (J : Ideal S) (hp : (p : S) ∈ J)
    (n : ℕ) (x y : R) (hy : y ∈ (J.comap f) ^ (n + 1)) : δ (x + y) - δ x ∈ J ^ n := by
  have hy' : f y ∈ J ^ (n + 1) := Ideal.le_comap_pow f (n + 1) hy
  have hc := wittAdditionCarry_mem_of_right_mem (p := p) (J ^ (n + 1)) (f x) (f y) hy'
  have he := (J ^ n).add_mem (wittTwoLift_delta_mem_pow f s hs J hp n y hy)
    (Ideal.pow_le_pow_right (by omega : n ≤ n + 1) hc)
  rw [wittTwoLift_delta_add f s hs]
  convert he using 1
  ring

/-- 二入力が逆像イデアルのn+1乗まで一致すれば、相対δは終域イデアルのn乗まで一致。 -/
theorem wittTwoLift_delta_sub_mem_pow (J : Ideal S) (hp : (p : S) ∈ J)
    (n : ℕ) (x y : R) (hxy : x - y ∈ (J.comap f) ^ (n + 1)) : δ x - δ y ∈ J ^ n := by
  have he := wittTwoLift_delta_add_sub_mem_pow f s hs J hp n y (x - y) hxy
  simpa only [add_sub_cancel] using he

variable {T : Type w} [CommRing T]

/-- 左入力の像を消す通常環射の下で、相対δの加法補正項は消える。 -/
theorem wittTwoLift_map_delta_add_of_left_zero (q : S →+* T)
    (x y : R) (hx : q (f x) = 0) : q (δ (x + y)) = q (δ x) + q (δ y) := by
  rw [wittTwoLift_delta_add f s hs, map_add, map_add]
  have hc : q ((WittVector.teichmuller p (f x) +
      WittVector.teichmuller p (f y)).coeff 1) = 0 := by
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hx, WittVector.teichmuller_zero, zero_add]
    exact WittVector.teichmuller_coeff_pos p (q (f y)) 1 (by decide)
  rw [hc, add_zero]

/-- 右入力の像を消す通常環射の下での相対δ加法公式。 -/
theorem wittTwoLift_map_delta_add_of_right_zero (q : S →+* T)
    (x y : R) (hy : q (f y) = 0) : q (δ (x + y)) = q (δ x) + q (δ y) := by
  rw [add_comm x y, wittTwoLift_map_delta_add_of_left_zero f s hs q y x hy, add_comm]

/-- pを消す通常環射の下での相対δ積公式。 -/
theorem wittTwoLift_map_delta_mul_of_prime_zero (q : S →+* T)
    (hp : q (p : S) = 0) (x y : R) :
    q (δ (x * y)) = (q (f x)) ^ p * q (δ y) + q (δ x) * (q (f y)) ^ p := by
  rw [wittTwoLift_delta_mul f s hs, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
    map_pow, map_pow, hp, zero_mul, zero_mul, add_zero]

end SerrePositivity.BhattScholze

end RelativeDeltaEstimate

/-! ## δ写像のイデアル冪に対する評価（旧 Delta/Extension/DeltaAdicEstimate.lean）

BS著者公開版Lemma 2.17の連続性に使う代数的評価。
p∈Iならδ(I^{n+1})⊂I^nを証明する。有限生成性・p正則性・完備性は不要。
完備化へのδ構造の延長はここでは構成しない。
-/

section DeltaAdicEstimate

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

namespace DeltaStructure

/-- pを含むイデアルのn+1乗の元のδは、そのn乗に属する。 -/
theorem delta_mem_pow (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (n : ℕ) (x : R) (hx : x ∈ I ^ (n + 1)) : D.delta x ∈ I ^ n := by
  exact wittTwoLift_delta_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x
    (by simpa only [Ideal.comap_id] using hx)

/-- I^{n+1}の摂動でδの値はI^nの範囲でしか変わらない。
Lemma 2.17の具体的な連続性評価m=n+1。 -/
theorem delta_add_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hy : y ∈ I ^ (n + 1)) :
    D.delta (x + y) - D.delta x ∈ I ^ n := by
  exact wittTwoLift_delta_add_sub_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x y
    (by simpa only [Ideal.comap_id] using hy)

/-- x,yがmod I^{n+1}で一致すればδx,δyはmod I^nで一致する。 -/
theorem delta_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hxy : x - y ∈ I ^ (n + 1)) :
    D.delta x - D.delta y ∈ I ^ n := by
  exact wittTwoLift_delta_sub_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x y
    (by simpa only [Ideal.comap_id] using hxy)

end DeltaStructure
end SerrePositivity.BhattScholze

end DeltaAdicEstimate
