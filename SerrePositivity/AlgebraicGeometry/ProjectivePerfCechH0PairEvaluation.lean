module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0Evaluation
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterAdd

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechH0PairEvalGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 基底の Frobenius 順極限から標準開の Čech H⁰ へ送るスカラーの類。 -/
def projectivePerfCechH0ScalarClass (a : FrobeniusDirectLimit R p hp hR) :
    projectivePerfCechH0 (ι := ι) G p hp hR hA :=
  (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom
    (frobeniusDirectLimitMap p hp hR
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) a)

/-- 左側の組の写像は、スカラーの H⁰ 類と基底の中心への実際の商写像の組。 -/
theorem projectivePerfCechH0Pair_apply (a : FrobeniusDirectLimit R p hp hR) :
    projectivePerfCechH0Pair (ι := ι) G I p hp hR hA a =
      (projectivePerfCechH0ScalarClass (ι := ι) G p hp hR hA a,
        frobeniusDirectLimitMap p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
          (Ideal.Quotient.mk (I ^ 1)) a) := rfl

/-- 有限段のスカラーは、同じ段の切断代数のスカラーの類へ送られる。 -/
theorem projectivePerfCechH0ScalarClass_of (n : ℕ) (r : R) :
    projectivePerfCechH0ScalarClass (ι := ι) G p hp hR hA
      (frobeniusDirectLimitOf R p hp hR n r) =
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom
      (frobeniusDirectLimitOf (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
        (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR) n
        (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G) r)) := rfl

/-- 組の写像の中心側の成分は、有限段で実際の商の元を取る。 -/
theorem projectivePerfCechH0Pair_snd_of (n : ℕ) (r : R) :
    (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA
      (frobeniusDirectLimitOf R p hp hR n r)).2 =
      frobeniusDirectLimitOf (R ⧸ (I ^ 1)) p hp
        (frobeniusQuotientPrimeCast p hR (I ^ 1)) n (Ideal.Quotient.mk (I ^ 1) r) := rfl

end SerrePositivity.AlgebraicGeometry
