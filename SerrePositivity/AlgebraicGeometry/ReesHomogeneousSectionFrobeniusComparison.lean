module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionQuotient
public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionKernelPower
public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionPowerLift

/-!
概要：切断代数の商と閉厚化の切断代数を Frobenius 順極限で比較する。
方針：実際の比較写像の核の冪零性と、像への Frobenius 冪の持ち上げを使う。
規約：核と像の条件は Rees の評価から供給し、追加仮定にしない。
使われ方：F7 の有限環の四角形の右下を閉厚化の切断環へ移す。
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
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 基底環で p が零なら、斉次標準開の切断代数でも p は零。 -/
theorem projectiveHomogeneousSectionAlgebra_primeCast (p : ℕ) (hR : (p : R) = 0) :
    (p : projectiveHomogeneousSectionAlgebra (ι := ι) G) = 0 := by
  simpa using congrArg (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) hR

variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
local instance reesSectionFrobeniusComparisonGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

include hp hR hA in
/-- 切断代数の商から閉厚化への比較写像の核は nil。 -/
theorem reesClosedHomogeneousSectionQuotientMap_kernel_nil
    (x : projectiveHomogeneousSectionAlgebra (ι := ι) G ⧸
      (I ^ 1).map (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)))
    (hx : reesClosedHomogeneousSectionQuotientMap G I 1 x = 0) : IsNilpotent x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨e, he⟩ := reesClosedHomogeneousSectionProjection_kernel_power (ι := ι) I G p hp hR hA
  refine ⟨p ^ e, ?_⟩
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [pow_one] using he a hx

include hp hR hA in
/-- 閉厚化の任意の切断のある Frobenius 冪は、切断代数の商からの比較写像の像に入る。 -/
theorem reesClosedHomogeneousSectionQuotientMap_power_lifts
    (a : projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G)) :
    ∃ e : ℕ, ∃ b, reesClosedHomogeneousSectionQuotientMap G I 1 b = a ^ (p ^ e) := by
  obtain ⟨e, he⟩ := reesClosedHomogeneousSectionProjection_power_lifts (ι := ι) I G p hp hR hA
  obtain ⟨b, hb⟩ := he a
  exact ⟨e, Ideal.Quotient.mk _ b, hb⟩

include hA in
/-- 実際の切断代数の商から閉厚化への比較写像は Frobenius 順極限上で全単射。
BST13 Lemma 3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedHomogeneousSectionQuotientMap_frobenius_bijective :
    Function.Bijective (frobeniusDirectLimitMap p hp
      (frobeniusQuotientPrimeCast p (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
        ((I ^ 1).map (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G))))
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι)
        (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hR)
      (reesClosedHomogeneousSectionQuotientMap G I 1)) := by
  constructor
  · apply frobeniusDirectLimitMap_injective
    exact reesClosedHomogeneousSectionQuotientMap_kernel_nil G I p hp hR hA
  · apply frobeniusDirectLimitMap_surjective
    exact reesClosedHomogeneousSectionQuotientMap_power_lifts G I p hp hR hA

end SerrePositivity.AlgebraicGeometry
