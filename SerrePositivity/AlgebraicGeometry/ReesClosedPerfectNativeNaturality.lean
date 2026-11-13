module

public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectChartMap
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechNaturality

/-!
概要：F8 の実際の閉厚化への制限を、native な Proj の実際の引き戻しへ移す。
方針：一般の次数付き射の自然性に商写像を代入し、既存の制限との一致を使う。
規約：全ての厚化の指数に対して同じ実際の環の射を使う。
使われ方：F8 の native な全複体の閉厚化の辺の検収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance closedPerfectNativeGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 実際の閉厚化の余鎖写像は、native な Proj の実際の引き戻しと比較を介して一致。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の閉厚化の射に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedPerfectNativeCechComplexIso_naturality (n : ℕ) :
    reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA n ≫
        (projectivePerfectNativeCechComplexIso (ι := ι)
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
          (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom =
      (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).hom ≫
        projectivePerfectNativeCechMap G
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
          (reesClosedGradedRingProjection I G n)
          (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A)))
          (fun _ ↦ rfl) (reesClosedGradedRingProjection_irrelevant I G n) p hp hR := by
  have h := projectivePerfectNativeCechComplexIso_naturality G
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
    (reesClosedGradedRingProjection I G n)
    (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A)))
    (fun _ ↦ rfl) (reesClosedGradedRingProjection_irrelevant I G n) p hp hR hA
    (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))
  rw [reesClosedPerfectChartMap_eq] at h
  exact h

end SerrePositivity.AlgebraicGeometry
