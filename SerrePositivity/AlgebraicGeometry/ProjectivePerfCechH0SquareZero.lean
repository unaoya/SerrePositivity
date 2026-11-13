module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareData

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
local instance perfCechH0SquareLawsGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- H⁰ の差写像は零を保つ。 -/
theorem projectivePerfCechH0Difference_map_zero :
    projectivePerfCechH0Difference (ι := ι) G I p hp hR hA 0 = 0 := by
  unfold projectivePerfCechH0Difference
  rw [map_zero, map_zero, map_zero]

end SerrePositivity.AlgebraicGeometry
