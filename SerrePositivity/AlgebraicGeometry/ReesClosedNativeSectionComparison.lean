module

public import SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedCoefficient
public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousProjection
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison

/-!
概要：次数付き商の斉次局所化を、Cartesian な実際の閉厚化の切断へ移す。
方針：2e の同じ Rees 商の係数同型を通し、元の係数からの二つの射影を照合する。
規約：次数付き商の Proj と実際の pullback のスキームの同一視は仮定しない。
使われ方：F8 の閉厚化の係数を、canonical な基底変更の構造層へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (n : ℕ)
local instance closedNativeSectionGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 斉次局所化の商の係数と、実際の閉厚化の切断との R 線形同型。 -/
def reesClosedNativeSectionLinearEquiv (T : Finset ι) (hT : T.Nonempty) :
    (projectiveHomogeneousChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).obj T ≃ₗ[R]
      (openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
        (projectiveProjCechOpen (ι := ι) G)).obj T :=
  (projectiveHomogeneousChartLinearEquiv
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) T).symm.trans
    ((Iso.app (reesClosedRingChartIso (ι := ι) I G n 0) T).toLinearEquiv.symm.trans
      (reesAdicNativeClosedCoefficientIso I G n iY g H T hT).toLinearEquiv)

/-- 線形同型は、斉次局所化の実際の射影を閉厚化の構造層の引き戻しへ送る。 -/
theorem reesClosedNativeSectionLinearEquiv_projection (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveHomogeneousChartDiagram G).obj T) :
    reesClosedNativeSectionLinearEquiv I G n iY g H T hT
        (reesClosedHomogeneousChartProjection I G n T x) =
      (g.app (cechOpenIntersection (projectiveProjCechOpen G) T)).hom
        ((projectiveProjCechSectionRingIso G T hT).hom.hom x) := by
  let z := (projectiveHomogeneousChartLinearEquiv G T).symm x
  have hq := reesClosedHomogeneousChartProjection_compare I G n T z
  have hz : projectiveHomogeneousChartLinearEquiv G T z = x := LinearEquiv.apply_symm_apply _ x
  rw [hz] at hq
  have hr := congrArg (fun η ↦ (η.app T).hom z) (reesClosedRingChartIso_projection (ι := ι) I G n 0)
  change (Iso.app (reesClosedRingChartIso (ι := ι) I G n 0) T).toLinearEquiv
    (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0).app T).hom z) =
      ((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom z at hr
  let eQ := projectiveHomogeneousChartLinearEquiv
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) T
  let eR := (Iso.app (reesClosedRingChartIso (ι := ι) I G n 0) T).toLinearEquiv
  let eN := (reesAdicNativeClosedCoefficientIso I G n iY g H T hT).toLinearEquiv
  have hq' := congrArg eQ.symm hq
  have hqi : eQ.symm (reesClosedHomogeneousChartProjection I G n T x) =
      ((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom z :=
    hq'.symm.trans (eQ.symm_apply_apply _)
  have hr' := congrArg eR.symm hr
  have hri : eR.symm (((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom z) =
      ((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0).app T).hom z :=
    hr'.symm.trans (eR.symm_apply_apply _)
  have hv := reesAdicNativeClosedCoefficientIso_projection_apply I G n iY g H T hT z
  change _ = (g.app (cechOpenIntersection (projectiveProjCechOpen G) T)).hom
    ((projectiveProjCechSectionRingIso G T hT).hom.hom
      (projectiveHomogeneousChartLinearEquiv G T z)) at hv
  rw [hz] at hv
  exact (congrArg (fun y ↦ eN (eR.symm y)) hqi).trans ((congrArg eN hri).trans hv)

end SerrePositivity.AlgebraicGeometry
