module

public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSections

/-!
概要：閉厚化への切断代数の制限を基底イデアルの拡大による商から因子化する。
方針：構造環で零になる基底スカラーは標準開と適合切断でも零になる。
規約：右辺は実際の閉厚化の斉次標準開の切断代数。
使われ方：F7 の B/IB から閉厚化の切断環への比較写像。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G]
local instance homogeneousSectionQuotientAwayAlgebra (f : A) :
    Algebra R (HomogeneousLocalization.Away G f) := projectiveHomogeneousAwayAlgebra G f

/-- 構造環で零になる基底スカラーは斉次局所化でも零になる。 -/
theorem projectiveHomogeneousAway_scalar_eq_zero (f : A) (r : R)
    (hr : algebraMap R A r = 0) :
    algebraMap R (HomogeneousLocalization.Away G f) r = 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.val_zero, Algebra.smul_def]
  rw [IsScalarTower.algebraMap_apply R A (Localization.Away f), hr, map_zero, zero_mul]

variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 構造環で零になる基底スカラーは適合切断代数でも零になる。 -/
theorem projectiveHomogeneousSectionAlgebra_scalar_eq_zero (r : R)
    (hr : algebraMap R A r = 0) :
    algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G) r = 0 := by
  apply Subtype.ext
  funext t
  exact projectiveHomogeneousAway_scalar_eq_zero G
    (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R (cechTupleSupport t))) r hr

variable (I : Ideal R)
local instance reesSectionQuotientGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化への制限は、基底の I^n を切断代数へ拡大したイデアルを消す。 -/
theorem reesClosedHomogeneousSectionProjection_ideal_le_ker (n : ℕ) :
    (I ^ n).map (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) ≤
      RingHom.ker (reesClosedHomogeneousSectionProjection G I n).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change reesClosedHomogeneousSectionProjection G I n (algebraMap R _ r) = 0
  rw [AlgHom.commutes]
  apply projectiveHomogeneousSectionAlgebra_scalar_eq_zero
  change Ideal.Quotient.mk _ (algebraMap R A r) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)

/-- 切断代数の商から、実際の閉厚化の切断代数への環準同型。 -/
def reesClosedHomogeneousSectionQuotientMap (n : ℕ) :
    projectiveHomogeneousSectionAlgebra (ι := ι) G ⧸
      (I ^ n).map (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) →+*
    projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  Ideal.Quotient.lift _ (reesClosedHomogeneousSectionProjection G I n).toRingHom
    (reesClosedHomogeneousSectionProjection_ideal_le_ker G I n)

/-- 商からの比較写像は、代表元上で元の切断の制限に一致する。 -/
theorem reesClosedHomogeneousSectionQuotientMap_mk (n : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) :
    reesClosedHomogeneousSectionQuotientMap G I n (Ideal.Quotient.mk _ a) =
      reesClosedHomogeneousSectionProjection G I n a := rfl

end SerrePositivity.AlgebraicGeometry
