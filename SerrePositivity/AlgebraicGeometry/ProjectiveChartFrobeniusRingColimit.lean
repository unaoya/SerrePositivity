module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousIteratedFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusFunctor
public import SerrePositivity.AlgebraicGeometry.RingDirectLimitIntColimit
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：各標準開の Frobenius 係数順極限を、次数零局所化の環の順極限と比較する。
方針：各有限段の線形同型と p^e 乗の比較から有向系の自然同型を作る。
規約：標準開の環の FrobeniusDirectLimit を使い、零環も許す。
使われ方：F6 の係数表示と F7 の H⁰ の環の比較を結ぶ。
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
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

local instance (f : A) : Module R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayModule G f

include hR in
omit [LinearOrder ι] [Fintype ι] [IsScalarTower R (MvPolynomial ι R) A]
  [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G] in
/-- 基底で零となる p は、次数零局所化の環でも零。 -/
theorem projectiveHomogeneousChart_primeCast (T : Finset ι) :
    (p : HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T))) = 0 := by
  let f := (HomogeneousLocalization.fromZeroRingHom G
    (Submonoid.powers (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))).comp
      (projectiveScalarToZero G)
  simpa only [map_natCast, map_zero] using congrArg f hR

/-- 標準開の環の反復 Frobenius の整数加群の系。 -/
abbrev projectiveChartRingFrobeniusFunctor (T : Finset ι) : ℕ ⥤ ModuleCat.{u} ℤ :=
  linearDirectSystemFunctor (ringDirectSystemIntMap
    (frobeniusDirectSystemMap
      (HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))
      p hp (projectiveHomogeneousChart_primeCast G p hR T)))

/-- 同じ標準開の加群の Frobenius 系と、実際の環の Frobenius 系の自然同型。 -/
def projectiveChartFrobeniusRingSystemIso (T : Finset ι) :
    projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA ⋙
        (evaluation (Finset ι) (ModuleCat.{u} ℤ)).obj T ≅
      projectiveChartRingFrobeniusFunctor (ι := ι) G p hp hR T :=
  NatIso.ofComponents
    (fun _ ↦ LinearEquiv.toModuleIso
      (show ((projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA).obj 0).obj T ≃ₗ[ℤ]
        (projectiveChartRingFrobeniusFunctor (ι := ι) G p hp hR T).obj 0 from
          (projectiveHomogeneousChartLinearEquiv G T).toAddEquiv.toIntLinearEquiv))
    (by
      intro i j h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change projectiveHomogeneousChartLinearEquiv G T
          (projectiveChartIteratedFrobenius G p hp hR hA T (j - i) z) =
        frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T)
          i j (leOfHom h) (projectiveHomogeneousChartLinearEquiv G T z)
      rw [frobeniusDirectSystemMap_apply]
      exact projectiveHomogeneousChartLinearEquiv_iteratedFrobenius G p hp hR hA T (j - i) z)

/-- 係数図式の順極限の各標準開は、同じ標準開環の Frobenius 順極限と同型。 -/
def projectiveChartFrobeniusRingColimitIso (T : Finset ι) :
    (colimit (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA)).obj T ≅
      ModuleCat.of ℤ (FrobeniusDirectLimit
        (HomogeneousLocalization.Away G
          (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))
        p hp (projectiveHomogeneousChart_primeCast G p hR T)) :=
  preservesColimitIso ((evaluation (Finset ι) (ModuleCat.{u} ℤ)).obj T)
      (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA) ≪≫
    colim.mapIso (projectiveChartFrobeniusRingSystemIso G p hp hR hA T) ≪≫
      (ringDirectLimitIntColimitIso
        (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T))).symm

end SerrePositivity.AlgebraicGeometry
