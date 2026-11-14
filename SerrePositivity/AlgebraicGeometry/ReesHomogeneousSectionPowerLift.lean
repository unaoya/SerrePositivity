module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousThickeningDiagram
public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionImageStabilization

/-!
概要：閉厚化の切断の十分高い Frobenius 冪を元の切断へ持ち上げる。
方針：厚化への因子分解と、一様な像の安定化を合成する。
規約：持ち上げ先と制限は実際の斉次標準開の切断代数。
使われ方：F7 の B/IB と閉厚化の切断環の Frobenius 比較の全射性。
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
local instance reesSectionPowerLiftGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

include hp hR hA in
/-- 閉厚化の任意の切断の一様に高い Frobenius 冪は、元の切断の制限に持ち上がる。
BST13 Lemma 3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedHomogeneousSectionProjection_power_lifts
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A] :
    ∃ e : ℕ, ∀ a : projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G),
      ∃ b : projectiveHomogeneousSectionAlgebra (ι := ι) G,
        reesClosedHomogeneousSectionProjection G I 1 b = a ^ (p ^ e) := by
  obtain ⟨c, hc⟩ := reesClosedHomogeneousSectionTransition_range_stabilizes (ι := ι) I G
  let e := 1 + c
  have he : 1 + c ≤ p ^ e * 1 := by
    simpa only [mul_one] using (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt) : 1 + c ≤ p ^ (1 + c))
  refine ⟨e, ?_⟩
  intro a
  have hx : a ^ (p ^ e) ∈ LinearMap.range
      (reesClosedHomogeneousSectionTransition (ι := ι) I G (p ^ e * 1) 1
        ((Nat.le_add_right 1 c).trans he)).toLinearMap :=
    ⟨reesHomogeneousSectionThickening I G p hp hR hA 1 e a,
      reesHomogeneousSectionThickening_factor I G p hp hR hA 1 e a⟩
  rw [hc 1 (p ^ e * 1) he] at hx
  exact hx

end SerrePositivity.AlgebraicGeometry
