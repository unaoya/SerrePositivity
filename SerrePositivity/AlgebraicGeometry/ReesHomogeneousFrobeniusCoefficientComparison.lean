module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusH0
public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusRingCech

/-!
概要：閉厚化への制限が二つの Frobenius 係数系の比較と可換であることを示す。
方針：各段・各標準開で、斉次チャートの同型とその逆を打ち消す。
規約：F6 の射影と実際の斉次代数の射影を同じ射として比較する。
使われ方：閉厚化の H⁰ の制限と切断環の Frobenius 写像の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance reesHomogeneousFrobeniusCoefficientComparisonGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 閉厚化への実際の射影は、多項式加群と斉次標準開の Frobenius 系の比較と可換。 -/
theorem projectiveHomogeneousFrobeniusCoefficientIso_projection (n : ℕ) :
    reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n ≫
      (projectiveHomogeneousFrobeniusCoefficientIso (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom =
    (projectiveHomogeneousFrobeniusCoefficientIso (ι := ι) G p hp hR hA).hom ≫
      algebraCechFrobeniusCoefficientNatTrans
        (reesClosedHomogeneousAlgebraProjection I G n) p hp hR := by
  apply NatTrans.ext
  funext i
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change projectiveHomogeneousChartLinearEquiv _ T
      (((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom x) =
    projectiveHomogeneousChartLinearEquiv _ T
      (((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom
        ((projectiveHomogeneousChartLinearEquiv G T).symm
          (projectiveHomogeneousChartLinearEquiv G T x)))
  rw [LinearEquiv.symm_apply_apply]

/-- 同じ閉厚化の可換性を係数図式の順極限へ送る。 -/
theorem projectiveHomogeneousFrobeniusCoefficientColimitIso_projection (n : ℕ) :
    colim.map (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n) ≫
      (colim.mapIso (projectiveHomogeneousFrobeniusCoefficientIso (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))))).hom =
    (colim.mapIso (projectiveHomogeneousFrobeniusCoefficientIso (ι := ι) G p hp hR hA)).hom ≫
      colim.map (algebraCechFrobeniusCoefficientNatTrans
        (reesClosedHomogeneousAlgebraProjection I G n) p hp hR) := by
  simp only [Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp,
    projectiveHomogeneousFrobeniusCoefficientIso_projection]

end SerrePositivity.AlgebraicGeometry
