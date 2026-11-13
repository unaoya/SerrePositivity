module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareZero
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterAdd
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0EquivLaws

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
local instance perfCechH0SquareApplyGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- H⁰ の差写像は加法を保つ。 -/
theorem projectivePerfCechH0Difference_map_add (x y : projectivePerfCechH0 (ι := ι) G p hp hR hA ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    projectivePerfCechH0Difference (ι := ι) G I p hp hR hA (x + y) =
      projectivePerfCechH0Difference (ι := ι) G I p hp hR hA x +
        projectivePerfCechH0Difference (ι := ι) G I p hp hR hA y := by
  unfold projectivePerfCechH0Difference
  rw [(projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA).map_add]
  simp only [projectivePerfCechH0Equiv_symm_apply]
  have hg := projectiveHomogeneousClosedCenterDifference_add (ι := ι) G I p hp hR
    (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA x)
    (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA y)
  have h := congrArg
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))).inv.hom hg
  have hd := projectivePerfCechH0Iso_inv_add (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))
    (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR
      (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA x))
    (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR
      (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA y))
  convert h.trans hd using 1

end SerrePositivity.AlgebraicGeometry
