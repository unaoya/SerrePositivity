module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusH0Stage
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0CenterClass

/-!
概要：基底の中心の Čech H⁰ 類を有限段のスカラーの像と照合する。
方針：基底の商の代表元を使い、中心の切断への因子化の公式を適用する。
規約：基底の商の元は任意の代表元を持つため、この表示は全ての有限段を扱う。
使われ方：閉厚化側の増大写像と H⁰ の短完全列の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechCenterStageGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 中心の有限段の代表元の H⁰ 類は、閉厚化上の同じスカラーの類である。 -/
theorem projectivePerfCechH0CenterClass_of_mk (n : ℕ) (r : R) :
    projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA
      (frobeniusDirectLimitOf (R ⧸ (I ^ 1)) p hp
        (frobeniusQuotientPrimeCast p hR (I ^ 1)) n (Ideal.Quotient.mk (I ^ 1) r)) =
    projectivePerfCechH0ScalarClass (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))
      (frobeniusDirectLimitOf R p hp hR n r) := by
  rw [projectivePerfCechH0ScalarClass_of]
  unfold projectivePerfCechH0CenterClass
  conv_lhs =>
    arg -1
    rw [frobeniusDirectLimitMap_of, projectiveHomogeneousClosedCenterBaseMap_mk]

end SerrePositivity.AlgebraicGeometry
