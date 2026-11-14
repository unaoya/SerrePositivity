module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartAlgebra
public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousProjection

/-!
概要：閉厚化への実際の環の射影を斉次局所化の代数図式の射にまとめる。
方針：既存の線形な係数の射をチャート比較で移し、環の射影と一致することを使う。
規約：各成分の写像は元の次数付き環の商から誘導される。
使われ方：閉厚化の適合切断環の射に Čech H⁰ の自然性を適用する。
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

local instance reesHomogeneousAlgebraProjectionGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化への線形な係数の射を斉次局所化の図式に移したもの。 -/
def reesClosedHomogeneousModuleProjection (n : ℕ) :
    projectiveHomogeneousChartDiagram (ι := ι) G ⟶
      projectiveHomogeneousChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  (projectiveHomogeneousChartDiagramIso G).inv ≫
    reesClosedRingProjectionChartMap (ι := ι) I G n 0 ≫
      (projectiveHomogeneousChartDiagramIso
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).hom

/-- 移した線形写像の各成分は、実際の斉次局所化の環の射影。 -/
theorem reesClosedHomogeneousModuleProjection_apply (n : ℕ) (T : Finset ι)
    (x : HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T))) :
    ((reesClosedHomogeneousModuleProjection I G n).app T).hom x =
      reesClosedHomogeneousChartProjection I G n T x := by
  change projectiveHomogeneousChartLinearEquiv _ T
    (((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom
      ((projectiveHomogeneousChartLinearEquiv G T).symm x)) = _
  rw [reesClosedHomogeneousChartProjection_compare, LinearEquiv.apply_symm_apply]

local instance reesHomogeneousAlgebraProjectionSourceAlgebra (f : A) : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f
local instance reesHomogeneousAlgebraProjectionTargetAlgebra (n : ℕ) (f : A ⧸ (I ^ n).map (algebraMap R A)) :
    Algebra R (HomogeneousLocalization.Away
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) f) :=
  projectiveHomogeneousAwayAlgebra _ f

/-- 閉厚化への斉次局所化の射影を、同じ線形写像を持つ代数写像にする。 -/
def reesClosedHomogeneousChartAlgProjection (n : ℕ) (T : Finset ι) :
    HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)) →ₐ[R]
    HomogeneousLocalization.Away
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ n).map (algebraMap R A))
        (projectiveLaurentDenominator R T)) :=
  AlgHom.ofLinearMap ((reesClosedHomogeneousModuleProjection I G n).app T).hom
    (by
      exact (reesClosedHomogeneousModuleProjection_apply I G n T
        (1 : HomogeneousLocalization.Away G
          (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))).trans
            (map_one (reesClosedHomogeneousChartProjection I G n T)))
    (by
      intro x y
      exact (reesClosedHomogeneousModuleProjection_apply I G n T (x * y)).trans
        ((map_mul (reesClosedHomogeneousChartProjection I G n T) x y).trans
          (congrArg₂ (fun (x y : HomogeneousLocalization.Away
            (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
            (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ n).map (algebraMap R A))
              (projectiveLaurentDenominator R T))) ↦ x * y)
            (reesClosedHomogeneousModuleProjection_apply I G n T x).symm
            (reesClosedHomogeneousModuleProjection_apply I G n T y).symm)))

/-- 閉厚化への実際の制限は、斉次標準開の代数図式の自然変換。 -/
def reesClosedHomogeneousAlgebraProjection (n : ℕ) :
    projectiveHomogeneousChartAlgebraDiagram (ι := ι) G ⟶
      projectiveHomogeneousChartAlgebraDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) where
  app T := CommAlgCat.ofHom (reesClosedHomogeneousChartAlgProjection I G n T)
  naturality {T U} h := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun f ↦ f.hom x)
      ((reesClosedHomogeneousModuleProjection I G n).naturality h)

end SerrePositivity.AlgebraicGeometry
