module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareLaws

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
local instance perfCechH0SquareExactGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 独立に検証した零・加法保存で束ねた H⁰ の差の加法準同型。 -/
def projectivePerfCechH0DifferenceHom :
    projectivePerfCechH0 (ι := ι) G p hp hR hA ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1)) →+
    projectivePerfCechH0 (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) where
  toFun := projectivePerfCechH0Difference (ι := ι) G I p hp hR hA
  map_zero' := projectivePerfCechH0Difference_map_zero (ι := ι) G I p hp hR hA
  map_add' := projectivePerfCechH0Difference_map_add (ι := ι) G I p hp hR hA

/-- 束ねた差写像の台の関数は固定した差写像。 -/
theorem projectivePerfCechH0DifferenceHom_apply
    (b : projectivePerfCechH0 (ι := ι) G p hp hR hA ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    projectivePerfCechH0DifferenceHom (ι := ι) G I p hp hR hA b =
      projectivePerfCechH0Difference (ι := ι) G I p hp hR hA b := rfl

end SerrePositivity.AlgebraicGeometry
