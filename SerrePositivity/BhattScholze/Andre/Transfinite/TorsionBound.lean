module

public import Mathlib.Algebra.Colimit.Ring
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionFrobenius
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Perfectoid 塔の未完備余極限と完備化の一様ねじれ境界

BS Thm 7.14（著者版 p.61）の極限段の補助命題を、被約性と逆極限の座標から証明する。
被約性・ねじれの境界と、完備化の perfectoid 性・完全忠実平坦性とは区別する。
-/

@[expose] public noncomputable section
open SerrePositivity
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
/-- ## 概要
被約可換環の有向余極限は被約。BS Thm 7.14（著者版 p.61）の極限段の補助命題。

## 方針
冪零元を一段へ降ろし、その冪が零になる関係を後の段に移して被約性を適用する。

## 規約
遷移写像の単射性は要求しない。

## 使われ方
perfectoid 塔の未完備余極限における p 冪ねじれの一様境界を得る。
-/
theorem isReduced_ringDirectLimit [∀ i, IsReduced (R i)] :
    IsReduced (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  refine ⟨fun z ⟨n, hn⟩ ↦ ?_⟩
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  have hz : Ring.DirectLimit.of R (fun i j h ↦ f i j h) i (x ^ n) = 0 := by
    simpa only [map_pow] using hn
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz
  have hzero : f i j hij x = 0 := IsReduced.eq_zero _ ⟨n, by simpa only [map_pow] using hj⟩
  rw [← Ring.DirectLimit.of_f hij x, hzero, map_zero]

/-- ## 概要
被約可換環で a の冪が x を消せば、a 自身が x を消す。
BS Thm 7.14（著者版 p.61）の極限段における一様ねじれ境界の補助命題。

## 方針
a*x の冪が零となることを掛け算の等式から示し、被約性を適用する。

## 規約
指数零と零環も許す。

## 使われ方
任意の p 冪ねじれに対し、共通指数 1 を与える。
-/
theorem mul_eq_zero_of_pow_mul_eq_zero_of_reduced {S : Type u}
    [CommRing S] [IsReduced S] (a x : S) (n : ℕ)
    (hx : a ^ n * x = 0) : a * x = 0 := by
  cases n with
  | zero => simpa only [pow_zero, one_mul, mul_zero] using congrArg (a * ·) hx
  | succ n =>
    apply IsReduced.eq_zero _
    refine ⟨n+1, ?_⟩
    calc
      (a*x)^(n+1) = (a^(n+1)*x)*x^n := by ring
      _ = 0 := by rw [hx, zero_mul]


/-- ## 概要
perfectoid 可換環の有向余極限は、完備化前の段階で被約。
BS Thm 7.14（著者版 p.61）の極限段の補助命題。

## 方針
各段の証明済みの perfectoid 被約性を、被約環の有向余極限定理へ渡す。

## 規約
p ねじれと零環を許し、余極限の perfectoid 性を仮定・結論しない。

## 使われ方
可算極限段の完備化で使う共通の p 冪ねじれ境界を得る。
-/
theorem isReduced_ringDirectLimit_of_perfectoid (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    IsReduced (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  have (i : ι) : IsReduced (R i) := (hR i).isReduced (R i) p
  exact isReduced_ringDirectLimit R f

/-- ## 概要
perfectoid 塔の未完備有向余極限の p 冪ねじれは p 自身で消える。
BS Thm 7.14（著者版 p.61）の極限段で、共通指数 1 を供給する。

## 方針
余極限の被約性から、一般の a 冪ねじれの境界を a=p に適用する。

## 規約
遷移写像の単射性や完全平坦性は不要。指数零も含む。

## 使われ方
p 進完備化の有界ねじれ比較の仮定を、具体的な指数で検証する。
-/
theorem ringDirectLimit_p_power_torsion_bound_of_perfectoid (p : ℕ) [Fact p.Prime]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) (n : ℕ)
    (x : Ring.DirectLimit R (fun i j h ↦ f i j h)) (hx : (p : _) ^ n * x = 0) :
    (p : Ring.DirectLimit R (fun i j h ↦ f i j h)) * x = 0 := by
  have := isReduced_ringDirectLimit_of_perfectoid R f p hR
  exact mul_eq_zero_of_pow_mul_eq_zero_of_reduced _ x n hx

/-- ## 概要
a 冪ねじれの共通境界 N は、主イデアル (a) による通常の完備化にも同じ N で保存される。
BS Thm 7.14（著者版 p.61）の可算極限段の補助命題。

## 方針
a^m で消える完備化の元を第 k+m 座標で調べる。元環のねじれ境界により、
a^N 倍した第 k 座標が零であることを示す。

## 規約
Noether 性、平坦性、a の非零因子性を要求しない。境界 N も指数 m も零を許す。

## 使われ方
perfectoid 塔の余極限における共通指数 1 を、通常の p 進完備化へ運ぶ。
-/
theorem adicCompletion_power_torsion_bound (R : Type u) [CommRing R] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (m : ℕ) (x : AdicCompletion (Ideal.span {a}) R)
    (hx : (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ m * x = 0) :
    (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ N * x = 0 := by
  obtain ⟨v, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {a}) R x
  apply AdicCompletion.ext_evalₐ
  intro k
  have hx' : a ^ m * v.val (k+m) ∈ (Ideal.span {a}) ^ (k+m) := by
    have he := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (k+m)) hx
    change Ideal.Quotient.mk ((Ideal.span {a}) ^ (k+m)) (a ^ m * v.val (k+m)) = 0 at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx'
  obtain ⟨z, hz⟩ := hx'
  have hdiff : a ^ m * (v.val (k+m) - a ^ k * z) = 0 := by
    rw [mul_sub, hz, pow_add]
    ring
  have hb := h m (v.val (k+m) - a ^ k * z) hdiff
  have hmem : a ^ N * v.val (k+m) ∈ (Ideal.span {a}) ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨a ^ N * z, ?_⟩
    rw [mul_sub] at hb
    calc
      a ^ N * v.val (k+m) = a ^ N * (a ^ k * z) := sub_eq_zero.mp hb
      _ = a ^ k * (a ^ N * z) := by ring
  have hdelta := v.property (Nat.le_add_right k m)
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hdelta
  have hn : a ^ N * v.val k ∈ (Ideal.span {a}) ^ k := by
    have he := ((Ideal.span {a}) ^ k).add_mem
      (((Ideal.span {a}) ^ k).mul_mem_left (a ^ N) hdelta) hmem
    simpa only [← mul_add, sub_add_cancel] using he
  change Ideal.Quotient.mk ((Ideal.span {a}) ^ k) (a ^ N * v.val k) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

/-- ## 概要
perfectoid 塔の有向余極限を p 進完備化しても、p 冪ねじれは p 自身で消える。
BS Thm 7.14（著者版 p.61）の可算極限段に必要な一様境界。

## 方針
未完備余極限の被約性から共通指数 1 を得て、通常の完備化による境界保存を適用する。

## 規約
完備化環の被約性や perfectoid 性、完全忠実平坦性はここでは結論しない。
環と添字は Type u。

## 使われ方
通常完備化と導来完備化の比較に必要な有界ねじれ条件を供給する。
-/
theorem adicCompletion_ringDirectLimit_p_power_torsion_bound_of_perfectoid
    (p : ℕ) [Fact p.Prime] (hR : ∀ i, IsIntegralPerfectoid (R i) p) (n : ℕ)
    (x : AdicCompletion
      (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
      (Ring.DirectLimit R (fun i j h ↦ f i j h)))
    (hx : (p : _) ^ n * x = 0) : (p : _) * x = 0 := by
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  have hb : ∀ m : ℕ, ∀ y : L, (p : L) ^ m * y = 0 → (p : L) ^ 1 * y = 0 := by
    simpa only [pow_one] using ringDirectLimit_p_power_torsion_bound_of_perfectoid R f p hR
  have he : algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L) (p : L) =
      (p : AdicCompletion (Ideal.span {(p : L)}) L) := map_natCast _ _
  have hx' : (algebraMap L (AdicCompletion (Ideal.span {(p : L)}) L) (p : L)) ^ n * x = 0 := by
    rw [he]
    exact hx
  simpa only [he, pow_one] using adicCompletion_power_torsion_bound L (p : L) 1 hb n x hx'

end SerrePositivity.BhattScholze.Andre.Transfinite
