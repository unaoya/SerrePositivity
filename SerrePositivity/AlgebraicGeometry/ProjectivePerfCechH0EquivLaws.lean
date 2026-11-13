module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareZero
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
local instance perfCechH0SquareAddGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 比較の逆加法同型は既存の逆線形写像そのもの。 -/
theorem projectivePerfCechH0Equiv_symm_apply
    (z : FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)) :
    (projectivePerfCechH0Equiv (ι := ι) G p hp hR hA).symm z =
      (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom z := rfl

/-- H⁰ 比較の逆線形写像は加法を保つ。 -/
theorem projectivePerfCechH0Iso_inv_add
    (z w : FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)) :
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom (z + w) =
      (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom z +
        (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom w :=
  (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom.map_add z w


end SerrePositivity.AlgebraicGeometry
