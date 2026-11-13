module

public import SerrePositivity.AlgebraicGeometry.ReesClosedRingGrading

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousRingChartMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRestriction
public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusFunctor

/-!
概要：閉厚化の標準開への制限を、実際の斉次局所化の環の射として比較する。
方針：次数付き商の射影に既存の斉次局所化の比較を適用する。
規約：商イデアルは I^n の構造環への像で、任意の加法写像に置き換えない。
使われ方：F6 の閉厚化の制限を環の Frobenius 順極限へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化の構造環への実際の次数付き射影。 -/
def reesClosedGradedRingProjection (n : ℕ) :
    G →+*ᵍ projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G where
  __ := Ideal.Quotient.mk ((I ^ n).map (algebraMap R A))
  map_mem {i x} hx := ⟨x, hx, rfl⟩

/-- 各標準開で閉厚化への制限を与える、斉次局所化の実際の環準同型。 -/
def reesClosedHomogeneousChartProjection (n : ℕ) (T : Finset ι) :=
  HomogeneousLocalization.map (reesClosedGradedRingProjection I G n)
    (projectiveHomogeneousRingChartMap_powers G
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (reesClosedGradedRingProjection I G n)
      (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A)))
      (fun _ ↦ rfl) T)

/-- 商への加群の制限は、同じ標準開の斉次局所化の環の射影に一致する。 -/
theorem reesClosedHomogeneousChartProjection_compare (n : ℕ) (T : Finset ι)
    (x : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    projectiveHomogeneousChartLinearEquiv
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) T
        (((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom x) =
      reesClosedHomogeneousChartProjection I G n T (projectiveHomogeneousChartLinearEquiv G T x) :=
  projectiveHomogeneousChartLinearEquiv_map G
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
    (reesClosedGradedRingProjection I G n)
    (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A))) (fun _ ↦ rfl) T x

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 閉厚化への標準開環の射影が誘導する Frobenius 系の自然変換。 -/
abbrev reesClosedChartRingFrobeniusNatTrans (n : ℕ) (T : Finset ι) :=
  frobeniusIntDirectSystemNatTrans p hp
    (projectiveHomogeneousChart_primeCast G p hR T)
    (projectiveHomogeneousChart_primeCast
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hR T)
    (reesClosedHomogeneousChartProjection I G n T)

/-- 係数系と環の Frobenius 系の比較は、閉厚化への実際の射影に自然。 -/
theorem reesClosedChartFrobeniusRingSystemIso_projection (n : ℕ) (T : Finset ι) :
    whiskerRight (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n)
        ((evaluation (Finset ι) (ModuleCat.{u} ℤ)).obj T) ≫
        (projectiveChartFrobeniusRingSystemIso
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
          (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) T).hom =
      (projectiveChartFrobeniusRingSystemIso G p hp hR hA T).hom ≫
        reesClosedChartRingFrobeniusNatTrans I G p hp hR n T := by
  apply NatTrans.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact reesClosedHomogeneousChartProjection_compare I G n T x

end SerrePositivity.AlgebraicGeometry
