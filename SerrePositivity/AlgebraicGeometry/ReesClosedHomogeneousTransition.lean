module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionH0Comparison

/-!
概要：閉厚化の間の遷移を、斉次標準開の実際の代数図式の射にする。
方針：商環の因子写像を局所化し、既存の線形な遷移と照合する。
規約：遷移は大きな指数から小さな指数へ向かう。
使われ方：Rees の像の安定化を切断代数へ移す。
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
local instance reesHomogeneousTransitionGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化の間の実際の次数付き環の因子写像。 -/
def reesClosedGradedRingTransition (i j : ℕ) (h : j ≤ i) : (projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G) →+*ᵍ (projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G) where
  __ := (reesClosedRingTransition (ι := ι) I i j h).toRingHom
  map_mem hx := reesClosedRingTransition_preservesPiece (ι := ι) I G i j h _ _ hx

/-- 閉厚化間の遷移が標準開の斉次局所化に誘導する環準同型。 -/
def reesClosedHomogeneousChartTransition (i j : ℕ) (h : j ≤ i) (T : Finset ι) :=
  HomogeneousLocalization.map (reesClosedGradedRingTransition (ι := ι) I G i j h)
    (projectiveHomogeneousRingChartMap_powers ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G))
      (reesClosedGradedRingTransition (ι := ι) I G i j h)
      (reesClosedRingTransition (ι := ι) I i j h) (fun _ ↦ rfl) T)

/-- 閉厚化間の既存の線形な遷移を斉次局所化の図式に移した射。 -/
def reesClosedHomogeneousModuleTransition (i j : ℕ) (h : j ≤ i) :
    projectiveHomogeneousChartDiagram (ι := ι) ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) ⟶
      projectiveHomogeneousChartDiagram (ι := ι) ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G)) :=
  (projectiveHomogeneousChartDiagramIso ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))).inv ≫
    reesClosedRingTransitionChartMap (ι := ι) I G i j h 0 ≫
      (projectiveHomogeneousChartDiagramIso ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G))).hom

/-- 移した線形な遷移は、実際の斉次局所化の環準同型と一致する。 -/
theorem reesClosedHomogeneousModuleTransition_apply (i j : ℕ) (h : j ≤ i) (T : Finset ι)
    (x : HomogeneousLocalization.Away ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ i).map (algebraMap R A))
        (projectiveLaurentDenominator R T))) :
    ((reesClosedHomogeneousModuleTransition I G i j h).app T).hom x =
      reesClosedHomogeneousChartTransition I G i j h T x := by
  have he := projectiveHomogeneousChartLinearEquiv_map ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G))
    (reesClosedGradedRingTransition (ι := ι) I G i j h)
    (reesClosedRingTransition (ι := ι) I i j h) (fun _ ↦ rfl) T
      ((projectiveHomogeneousChartLinearEquiv ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) T).symm x)
  exact he.trans (congrArg (reesClosedHomogeneousChartTransition I G i j h T)
    ((projectiveHomogeneousChartLinearEquiv
      (projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G) T).apply_symm_apply x))

local instance reesHomogeneousTransitionAlgebra (n : ℕ)
    (f : A ⧸ (I ^ n).map (algebraMap R A)) :
    Algebra R (HomogeneousLocalization.Away ((projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) f) :=
  projectiveHomogeneousAwayAlgebra ((projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) f

/-- 閉厚化間の斉次局所化の遷移を代数写像として扱う。 -/
def reesClosedHomogeneousChartAlgTransition (i j : ℕ) (h : j ≤ i) (T : Finset ι) :
    HomogeneousLocalization.Away ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ i).map (algebraMap R A))
        (projectiveLaurentDenominator R T)) →ₐ[R]
    HomogeneousLocalization.Away ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G))
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ j).map (algebraMap R A))
        (projectiveLaurentDenominator R T)) :=
  AlgHom.ofLinearMap ((reesClosedHomogeneousModuleTransition I G i j h).app T).hom
    (by
      exact (reesClosedHomogeneousModuleTransition_apply I G i j h T
        (1 : HomogeneousLocalization.Away ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))
          (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ i).map (algebraMap R A))
            (projectiveLaurentDenominator R T)))).trans
              (map_one (reesClosedHomogeneousChartTransition I G i j h T)))
    (by
      intro x y
      exact (reesClosedHomogeneousModuleTransition_apply I G i j h T (x * y)).trans
        ((map_mul (reesClosedHomogeneousChartTransition I G i j h T) x y).trans
          (congrArg₂ (fun (x y : HomogeneousLocalization.Away ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G))
            (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ j).map (algebraMap R A))
              (projectiveLaurentDenominator R T))) ↦ x * y)
            (reesClosedHomogeneousModuleTransition_apply I G i j h T x).symm
            (reesClosedHomogeneousModuleTransition_apply I G i j h T y).symm)))

/-- 閉厚化の遷移は斉次標準開の代数図式の自然変換をなす。 -/
def reesClosedHomogeneousAlgebraTransition (i j : ℕ) (h : j ≤ i) :
    projectiveHomogeneousChartAlgebraDiagram (ι := ι) ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) ⟶
      projectiveHomogeneousChartAlgebraDiagram (ι := ι) ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G)) where
  app T := CommAlgCat.ofHom (reesClosedHomogeneousChartAlgTransition I G i j h T)
  naturality {T U} f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun f ↦ f.hom x)
      ((reesClosedHomogeneousModuleTransition I G i j h).naturality f)

end SerrePositivity.AlgebraicGeometry
