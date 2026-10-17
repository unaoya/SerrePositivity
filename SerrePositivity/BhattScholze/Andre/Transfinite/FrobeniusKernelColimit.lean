module

public import Mathlib.Algebra.Colimit.Ring
public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusKernel
public import SerrePositivity.BhattScholze.Andre.Transfinite.ResidueFrobenius

/-! # Perfectoid 塔の未完備余極限の Frobenius 核

BS Thm 7.14（著者版 p.61）の極限段に必要な代数的条件を保存する。
原典で省略された極限操作の補助命題であり、Fontaine 核の単項性の判定を代用しない。
-/

@[expose] public noncomputable section
open SerrePositivity
universe u
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
local notation "L" => Ring.DirectLimit R (fun i j h ↦ f i j h)
local notation "ofL" => Ring.DirectLimit.of R (fun i j h ↦ f i j h)
/-- ## 概要
perfectoid 塔の一段で p=u*π^p を満たす π の像は、余極限でも p 乗がその像の p 乗で
割り切れる元を割り切る。BS Thm 7.14（著者版 p.61）の極限段の Frobenius 核計算。

## 方針
元と割り算の証人を共通の段へ降ろし、その等式が成立する後の段で
既存の perfectoid Frobenius 核定理を適用する。

## 規約
p ねじれと零環を許す。遷移写像の単射性・完全平坦性・完備性は不要。

## 使われ方
未完備余極限の mod π から mod π^p への Frobenius の単射性を検証する。
-/
theorem ringDirectLimit_frobenius_kernel_of_stage_root (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (i₀ : ι) (π : R i₀) (u : (R i₀)ˣ) (hp : (p : R i₀) = u * π ^ p)
    (x : L) (hx : x ^ p ∈ Ideal.span {(ofL i₀ π) ^ p}) : x ∈ Ideal.span {ofL i₀ π} := by
  obtain ⟨i, x₀, hx₀⟩ := Ring.DirectLimit.exists_of x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨j, c₀, hc₀⟩ := Ring.DirectLimit.exists_of c
  obtain ⟨k₀, h₀k₀, hik₀⟩ := exists_ge_ge i₀ i
  obtain ⟨k, hk₀k, hjk⟩ := exists_ge_ge k₀ j
  let h₀k := h₀k₀.trans hk₀k
  let hik := hik₀.trans hk₀k
  let y := f i k hik x₀
  let q := f i₀ k h₀k π
  let d := f j k hjk c₀
  have hzero : ofL k (y ^ p - q ^ p * d) = 0 := by
    simp only [map_sub, map_mul, map_pow]
    simp only [y, q, d, Ring.DirectLimit.of_f, hx₀, hc₀]
    exact sub_eq_zero.mpr hc
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact hzero
  let φ := (f k l hkl).comp (f i₀ k h₀k)
  have hp' : (p : R l) = (Units.map φ.toMonoidHom u : R l) * (φ π) ^ p := by
    change (p : R l) = φ (u : R i₀) * (φ π) ^ p
    simpa only [map_natCast, map_mul, map_pow] using congrArg φ hp
  have hpow : (f k l hkl y) ^ p ∈ Ideal.span {(φ π) ^ p} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨f k l hkl d, ?_⟩
    change (f k l hkl y) ^ p = (f k l hkl q) ^ p * f k l hkl d
    simpa only [map_sub, map_mul, map_pow, sub_eq_zero] using hl
  have hk := (hR l).frobenius_kernel_of_unit_root (R l) p (φ π)
    (Units.map φ.toMonoidHom u) hp' (f k l hkl y) hpow
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hk
  have hyl : ofL l (f k l hkl y) = x := by
    rw [Ring.DirectLimit.of_f]
    simpa only [y, Ring.DirectLimit.of_f] using hx₀
  have hql : ofL l (φ π) = ofL i₀ π := by
    change ofL l (f k l hkl (f i₀ k h₀k π)) = _
    rw [Ring.DirectLimit.of_f, Ring.DirectLimit.of_f]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨ofL l b, ?_⟩
  rw [← hyl, hb, map_mul, hql]


/-- ## 概要
perfectoid 塔の一段の π の像について、余極限で x^p が (π^p) に入ることと
x が (π) に入ることは同値。BS Thm 7.14（著者版 p.61）の極限段の補助命題。

## 方針
一方向は有限段の Frobenius 核の移送、逆方向は π 倍表示を p 乗する。

## 規約
π は一段で p=u*π^p を満たすもの。余極限自体を perfectoid と仮定しない。

## 使われ方
完備化の開イデアル商を介して、Frobenius の核表示を完備化側へ移す準備となる。
-/
theorem ringDirectLimit_pow_mem_span_iff_of_stage_root (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (i₀ : ι) (π : R i₀) (u : (R i₀)ˣ) (hp : (p : R i₀) = u * π ^ p) (x : L) :
    x ^ p ∈ Ideal.span {(ofL i₀ π) ^ p} ↔ x ∈ Ideal.span {ofL i₀ π} := by
  refine ⟨ringDirectLimit_frobenius_kernel_of_stage_root R f p hR i₀ π u hp x, ?_⟩
  intro hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
  apply Ideal.mem_span_singleton.mpr
  exact ⟨b ^ p, by rw [hb, mul_pow]⟩

/-- ## 概要
perfectoid 塔の未完備余極限には p=u*π^p を満たす π と単元 u が存在し、
mod p Frobenius は全射、かつ x^p∈(π^p) と x∈(π) は同値。
BS Thm 7.14（著者版 p.61）の極限段の代数的条件。

## 方針
任意の一段から π と単元を移し、剰余 Frobenius と核計算の余極限保存を合成する。

## 規約
零環を許す。余極限の p 進完備性と Fontaine 核の単項性は結論しない。

## 使われ方
完備化後の perfectoid 判定に必要な、完備化前の具体的根と Frobenius 条件を供給する。
-/
theorem ringDirectLimit_exists_frobenius_root_data (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    ∃ (π : L) (u : Lˣ), (p : L) = u * π ^ p ∧
      Function.Surjective (fun x : L ⧸ Ideal.span {(p : L)} ↦ x ^ p) ∧
      ∀ x : L, x ^ p ∈ Ideal.span {π ^ p} ↔ x ∈ Ideal.span {π} := by
  let i₀ : ι := Classical.arbitrary ι
  have hr : ∃ (π : R i₀) (u : (R i₀)ˣ), (p : R i₀) = u * π ^ p := by
    rcases hR i₀ with hsub | ⟨_, _, hr, _⟩
    · exact ⟨0, 1, hsub.elim _ _⟩
    · exact hr
  obtain ⟨π, u, hp⟩ := hr
  refine ⟨ofL i₀ π, Units.map (ofL i₀).toMonoidHom u, ?_,
    directLimit_mod_p_pow_surjective_of_perfectoid R f p hR, ?_⟩
  · change (p : L) = ofL i₀ (u : R i₀) * (ofL i₀ π) ^ p
    simpa only [map_natCast, map_mul, map_pow] using congrArg (ofL i₀) hp
  · exact ringDirectLimit_pow_mem_span_iff_of_stage_root R f p hR i₀ π u hp

end SerrePositivity.BhattScholze.Andre.Transfinite
