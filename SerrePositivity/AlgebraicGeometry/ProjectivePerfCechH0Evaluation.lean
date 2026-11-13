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
local instance perfCechH0EvalGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 中央項の比較の成分は既存の H⁰ 比較。 -/
theorem projectivePerfCechH0CenterEquiv_apply
    (b : projectivePerfCechH0 (ι := ι) G p hp hR hA)
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA (b, c) =
      ((projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).hom.hom b, c) := rfl

/-- 逆 H⁰ 比較は差を保つ。 -/
theorem projectivePerfCechH0Iso_inv_sub
    (z w : FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)) :
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom (z - w) =
      (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom z -
        (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom w :=
  map_sub _ z w

/-- H⁰ 比較の後にその逆を適用すると元のコホモロジー類に戻る。 -/
theorem projectivePerfCechH0Iso_inv_hom
    (b : projectivePerfCechH0 (ι := ι) G p hp hR hA) :
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom
      ((projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).hom.hom b) = b :=
  (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).toLinearEquiv.symm_apply_apply b

/-- 等しい切断の極限の元に逆 H⁰ 比較を適用しても等しい。 -/
theorem projectivePerfCechH0Iso_inv_congr
    (z w : FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)) (h : z = w) :
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom z =
      (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom w :=
  congrArg (fun z ↦ (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom z) h

/-- 比較した元との等式から逆比較の値を求める。 -/
theorem projectivePerfCechH0Iso_inv_eq
    (b : projectivePerfCechH0 (ι := ι) G p hp hR hA)
    (z : FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR))
    (h : (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).hom.hom b = z) :
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).inv.hom z = b := by
  rw [← h, projectivePerfCechH0Iso_inv_hom]

end SerrePositivity.AlgebraicGeometry
