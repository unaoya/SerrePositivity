module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechIntBounds

/-!
概要：実際の Čech H の閉厚化への射影の核と像を、反復 Frobenius で制御する。
方針：厚化の因子分解・射影比較を、2e の核の評価・像の安定化に接続する。
規約：BST13 Lemma 3.9 の Hⁱ に対応する Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。
使われ方：F6 の順極限上の単射性・全射性に渡す二つの有限段の条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable [LinearOrder ι] [Fintype ι]
variable (I : Ideal R) (G : ℕ → Submodule R A) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedMonoid G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 実際の閉厚化への Čech 射影は、同じ厚さでの反復 Frobenius と可換。 -/
theorem reesClosedCechIntProjection_frobenius (n e q : ℕ)
    (x : ProjectiveCechIntHomology (ι := ι) G q) :
    projectiveCechIntFrobeniusHomology (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) e q
        (reesClosedCechIntProjection (ι := ι) I G n q x) =
    reesClosedCechIntProjection (ι := ι) I G n q
      (projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA e q x) := by
  have hf := congrArg (fun f ↦ f (reesClosedCechIntProjection (ι := ι) I G n q x))
    (reesClosedCechIntThickening_factor (ι := ι) I G p hp hR hA n e q)
  have hπ := congrArg (fun f ↦ f x)
    (reesClosedCechIntThickening_projection (ι := ι) I G p hp hR hA n e q)
  simp only [LinearMap.comp_apply] at hf hπ
  rw [← hf, hπ]
  exact reesClosedCechIntTransition_projection (ι := ι) I G _ n _ q _

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]

/-- 中心の冪で元の Čech H が零化されるなら、厚さ 1 の射影の核は反復 Frobenius で消える。 -/
theorem reesClosedCechIntProjection_kernel_eventually_zero (q : ℕ)
    (hkill : ∃ k : ℕ, I ^ k •
      (⊤ : Submodule R (reesAdicProjectiveCechTarget (ι := ι) G 0 q)) = ⊥)
    (x : ProjectiveCechIntHomology (ι := ι) G q)
    (hx : reesClosedCechIntProjection (ι := ι) I G 1 q x = 0) :
    ∃ e : ℕ, projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA e q x = 0 := by
  obtain ⟨N, hN⟩ := reesClosedCechIntProjection_eventually_injective (ι := ι) I G q hkill
  refine ⟨N, ?_⟩
  apply hN (p ^ N * 1) (by
    simpa only [mul_one] using (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt) : N ≤ p ^ N))
  rw [map_zero]
  have h := congrArg (fun f ↦ f x)
    (reesClosedCechIntThickening_projection (ι := ι) I G p hp hR hA 1 N q)
  simpa only [LinearMap.comp_apply, hx, map_zero] using h.symm

/-- 閉厚化の Čech H の各元の十分高い Frobenius 反復は、元の対象からの制限の像に入る。 -/
theorem reesClosedCechIntProjection_frobenius_eventually_lifts (q : ℕ)
    (x : ReesClosedCechIntHomology (ι := ι) I G 1 q) :
    ∃ e : ℕ, ∃ y : ProjectiveCechIntHomology (ι := ι) G q,
      reesClosedCechIntProjection (ι := ι) I G 1 q y =
      projectiveCechIntFrobeniusHomology (ι := ι)
        (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) e q x := by
  obtain ⟨c, hc⟩ := reesClosedCechIntTransition_eventually_lifts (ι := ι) I G q
  have hl : 1 + c ≤ p ^ (1 + c) * 1 := by
    simpa only [mul_one] using
      (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt) : 1 + c ≤ p ^ (1 + c))
  obtain ⟨y, hy⟩ := hc 1 (p ^ (1 + c) * 1) hl
    (reesClosedCechIntThickening (ι := ι) I G p hp hR hA 1 (1 + c) q x)
  refine ⟨1 + c, y, ?_⟩
  have hf := congrArg (fun f ↦ f x)
    (reesClosedCechIntThickening_factor (ι := ι) I G p hp hR hA 1 (1 + c) q)
  exact hy.trans hf

end SerrePositivity.AlgebraicGeometry
