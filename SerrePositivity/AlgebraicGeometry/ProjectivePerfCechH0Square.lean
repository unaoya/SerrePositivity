module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0DifferenceHom

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
local instance perfCechH0SquareTransferGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hspan in
/-- 射影中心の四角形の、F6 と同じ複体の Čech H⁰ における短完全性。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfCechH0_square_exact :
    Function.Injective (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA) ∧
    Function.Exact (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA)
      (projectivePerfCechH0Difference (ι := ι) G I p hp hR hA) ∧
    Function.Surjective (projectivePerfCechH0Difference (ι := ι) G I p hp hR hA) := by
  have he := projectiveHomogeneousClosedCenter_exact G I p hp hR hspan hA
  apply cechAdditiveShortExact_transport
    (frobeniusCenterPair p hp hR
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) (I ^ 1))
    (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR)
    (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA)
    (projectivePerfCechH0Equiv (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))
    (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA)
    (projectivePerfCechH0DifferenceHom (ι := ι) G I p hp hR hA)
    _ _ he.1 he.2.1 he.2.2
  · intro a
    exact (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA).apply_symm_apply _
  · intro b
    convert (projectivePerfCechH0Equiv (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))).apply_symm_apply
        (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR
          (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA b)) using 1
    simp only [projectivePerfCechH0DifferenceHom, projectivePerfCechH0Difference,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]

end SerrePositivity.AlgebraicGeometry
