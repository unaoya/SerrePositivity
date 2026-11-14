module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousFrobeniusH0Comparison
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterMaps
public import SerrePositivity.AlgebraicGeometry.CechAdditiveExactTransport

/-!
概要：射影中心の四角形の短完全列を、F6 と同じ複体の Čech H⁰ に置く。
方針：切断環の完全列を明示した H⁰ 比較で移す。
規約：射の定義に使った比較を保持し、実際の制限との照合は別の成分補題で与える。
使われ方：F7 の次数零の完全性を F8 の全複体へ渡す。
-/

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
local instance perfCechH0SquareGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- F6 の実際の標準開環の Frobenius 複体の Čech H⁰。 -/
abbrev projectivePerfCechH0 :=
  (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).homology 0

/-- Čech H⁰ と切断の Frobenius 順極限の比較を、台の加法群の型を明示して読む。 -/
def projectivePerfCechH0Equiv :
    projectivePerfCechH0 (ι := ι) G p hp hR hA ≃+
      FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
        (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR) :=
  (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).toLinearEquiv.toAddEquiv

/-- 中央項の Čech H⁰ と基底の中心の積を、切断環側の中央項と同定する。 -/
def projectivePerfCechH0CenterEquiv :
    projectivePerfCechH0 (ι := ι) G p hp hR hA ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1)) ≃+
    FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR) ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1)) :=
  AddEquiv.prodCongr
    (projectivePerfCechH0Equiv (ι := ι) G p hp hR hA)
    (AddEquiv.refl _)

/-- 基底の Frobenius 順極限から Čech H⁰ と基底の中心への二つの写像の組。 -/
def projectivePerfCechH0Pair :=
  (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA).symm.toAddMonoidHom.comp
    (frobeniusCenterPair p hp hR
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) (I ^ 1))

set_option backward.isDefEq.respectTransparency true in
/-- 閉厚化の Čech H⁰ への差写像。切断の実際の差を指定した比較で移したもの。 -/
def projectivePerfCechH0Difference :
    projectivePerfCechH0 (ι := ι) G p hp hR hA ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1)) →
    projectivePerfCechH0 (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) :=
  fun x ↦ (projectivePerfCechH0Equiv (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))).symm
      (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR
        (projectivePerfCechH0CenterEquiv (ι := ι) G I p hp hR hA x))

end SerrePositivity.AlgebraicGeometry
