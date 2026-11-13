module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousThickeningDiagram

/-!
概要：厚化 Frobenius と元の切断からの射影の可換性。
方針：既存の整数係数図式の可換性を、標準開の比較で移す。
規約：比較の右辺は実際の環の p^e 乗を射影したもの。
使われ方：F7 の制限の核の Frobenius 冪を十分厚い制限の核へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance reesThickeningProjectionGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 元の標準開から射影した後の厚化写像は、冪乗した後の厚い閉厚化への射影。 -/
theorem reesHomogeneousThickeningDiagram_projection (n e : ℕ) (T : Finset ι)
    (x : HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T))) :
    ((reesHomogeneousThickeningDiagram I G p hp hR hA n e).app T).hom
      (((reesClosedHomogeneousModuleProjection I G n).app T).hom x) =
    ((reesClosedHomogeneousModuleProjection I G (p ^ e * n)).app T).hom (x ^ (p ^ e)) := by
  let eg := projectiveHomogeneousChartLinearEquiv G T
  let en := projectiveHomogeneousChartLinearEquiv
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) T
  let eb := projectiveHomogeneousChartLinearEquiv
    (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G) T
  obtain ⟨z, rfl⟩ := eg.surjective x
  have hs (m : ℕ) (w) :
      ((reesClosedHomogeneousModuleProjection I G m).app T).hom (eg w) =
      projectiveHomogeneousChartLinearEquiv
        (projectiveRingQuotientGrade ((I ^ m).map (algebraMap R A)) G) T
        (((reesClosedRingProjectionChartMap (ι := ι) I G m 0).app T).hom w) := by
    change projectiveHomogeneousChartLinearEquiv
      (projectiveRingQuotientGrade ((I ^ m).map (algebraMap R A)) G) T
      (((reesClosedRingProjectionChartMap (ι := ι) I G m 0).app T).hom
        (eg.symm (eg w))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [hs, reesHomogeneousThickeningDiagram_apply]
  have hf := congrArg (fun f ↦ (f.app T).hom z)
    (reesClosedCechIntThickeningDiagram_projection (ι := ι) I G p hp hR hA n e)
  have hpw := projectiveHomogeneousChartLinearEquiv_iteratedFrobenius G p hp hR hA T e z
  have hr : ((reesClosedHomogeneousModuleProjection I G (p ^ e * n)).app T).hom
      ((eg z) ^ (p ^ e)) = eb
      (((reesClosedRingProjectionChartMap (ι := ι) I G (p ^ e * n) 0).app T).hom
        (projectiveChartIteratedFrobenius G p hp hR hA T e z)) := by
    rw [← hpw]
    exact hs _ _
  change eb (((reesClosedCechIntThickeningDiagram (ι := ι) I G p hp hR hA n e).app T).hom
    (en.symm (en (((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (congrArg eb hf).trans hr.symm

/-- 射影後の切断の厚化 Frobenius は、元の切断の冪乗後の射影に一致する。 -/
theorem reesHomogeneousSectionThickening_projection (n e : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) :
    reesHomogeneousSectionThickening I G p hp hR hA n e
        (reesClosedHomogeneousSectionProjection G I n a) =
      reesClosedHomogeneousSectionProjection G I (p ^ e * n) (a ^ (p ^ e)) := by
  apply Subtype.ext
  funext t
  rw [reesHomogeneousSectionThickening_apply, reesClosedHomogeneousSectionProjection_apply,
    reesClosedHomogeneousSectionProjection_apply]
  have he := reesHomogeneousThickeningDiagram_projection I G p hp hR hA n e
    (cechTupleSupport t) (a.val t)
  simp only [reesClosedHomogeneousModuleProjection_apply] at he
  exact he

end SerrePositivity.AlgebraicGeometry
