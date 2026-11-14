module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0EquivLaws
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
local instance perfCechH0CenterClassGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 基底の中心の Frobenius 順極限から閉厚化の Čech H⁰ への写像。 -/
def projectivePerfCechH0CenterClass
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    projectivePerfCechH0 (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) :=
  (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))).inv.hom
      (frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))
        (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι)
          (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hR)
        (projectiveHomogeneousClosedCenterBaseMap (ι := ι) G I) c)

end SerrePositivity.AlgebraicGeometry
