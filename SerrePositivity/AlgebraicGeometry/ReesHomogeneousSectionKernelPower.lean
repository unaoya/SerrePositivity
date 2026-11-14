module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousThickeningProjection
public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionKernelBound

/-!
概要：閉厚化への切断の制限の核の Frobenius 冪は、基底イデアルの拡大に入る。
方針：厚化と射影の可換性で厚い核に送り、一様な Rees の核の評価を使う。
規約：切断代数自身の I 冪による消滅は使わない。
使われ方：F7 の B/IB から閉厚化の切断環への写像の核の冪零性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance reesSectionKernelPowerGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

include hp hR hA in
/-- 制限の核の一様な Frobenius 冪は、基底イデアルの拡大に入る。
BST13 Lemma 3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedHomogeneousSectionProjection_kernel_power
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A] :
    ∃ e : ℕ, ∀ a : projectiveHomogeneousSectionAlgebra (ι := ι) G,
      reesClosedHomogeneousSectionProjection G I 1 a = 0 →
        a ^ (p ^ e) ∈ I.map (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) := by
  obtain ⟨c, hc⟩ := reesClosedHomogeneousSectionProjection_kernel_ideal_bound (ι := ι) G I
  let e := c + 1
  have he : c + 1 ≤ p ^ e * 1 := by
    simpa only [mul_one] using
      (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt) : c + 1 ≤ p ^ (c + 1))
  refine ⟨e, ?_⟩
  intro a ha
  have hz : reesClosedHomogeneousSectionProjection G I (p ^ e * 1) (a ^ (p ^ e)) = 0 := by
    rw [← reesHomogeneousSectionThickening_projection I G p hp hR hA 1 e a, ha, map_zero]
  have hm := hc (p ^ e * 1) (by omega) (a ^ (p ^ e)) hz
  exact Ideal.map_mono (Ideal.pow_le_self (show p ^ e * 1 - c ≠ 0 by omega)) hm

end SerrePositivity.AlgebraicGeometry
