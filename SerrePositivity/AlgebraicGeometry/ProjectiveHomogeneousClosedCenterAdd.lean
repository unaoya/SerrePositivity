module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterMaps

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
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
local instance closedCenterAddGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 切断環側の閉厚化の差写像は加法を保つ。 -/
theorem projectiveHomogeneousClosedCenterDifference_add
    (x y : FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G)
      p hp (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR) ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR (x + y) =
      projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR x +
        projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR y := by
  exact (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR).map_add x y

end SerrePositivity.AlgebraicGeometry
