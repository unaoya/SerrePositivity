module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerAddMap
public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSectionTransition
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechIntThickening

/-!
概要：厚化を経由する Frobenius を斉次局所化の整数加群の係数図式へ送る。
方針：既存の指定次数の写像を、同じ標準開の比較で移す。
規約：Frobenius は基底環上線形とは仮定しない。
使われ方：切断環上の冪乗を厚化の制限と比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance reesHomogeneousThickeningGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 厚化を経由する Frobenius の、実際の斉次標準開の整数加群図式の射。 -/
def reesHomogeneousThickeningDiagram (n e : ℕ) :
    algebraCechIntDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) ⟶
    algebraCechIntDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)) :=
  whiskerRight (projectiveHomogeneousChartDiagramIso
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).inv
      (ModuleCat.restrictScalars (Int.castRingHom R)) ≫
  reesClosedCechIntThickeningDiagram (ι := ι) I G p hp hR hA n e ≫
  whiskerRight (projectiveHomogeneousChartDiagramIso
    (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)).hom
      (ModuleCat.restrictScalars (Int.castRingHom R))

/-- 厚化の図式の各成分は、既存の整数線形写像を標準開の比較で移したもの。 -/
theorem reesHomogeneousThickeningDiagram_apply (n e : ℕ) (T : Finset ι)
    (x : HomogeneousLocalization.Away
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ n).map (algebraMap R A))
        (projectiveLaurentDenominator R T))) :
    ((reesHomogeneousThickeningDiagram I G p hp hR hA n e).app T).hom x =
      projectiveHomogeneousChartLinearEquiv
        (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G) T
        (((reesClosedCechIntThickeningDiagram (ι := ι) I G p hp hR hA n e).app T).hom
          ((projectiveHomogeneousChartLinearEquiv
            (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) T).symm x)) := rfl

/-- 厚化への加法写像を元の厚さへ戻すと、標準開の環の実際の p^e 乗になる。 -/
theorem reesHomogeneousThickeningDiagram_factor (n e : ℕ) (T : Finset ι)
    (x : HomogeneousLocalization.Away
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ n).map (algebraMap R A))
        (projectiveLaurentDenominator R T))) :
    ((reesClosedHomogeneousModuleTransition I G (p ^ e * n) n
        (Nat.le_mul_of_pos_left n (pow_pos hp.pos e))).app T).hom
      (((reesHomogeneousThickeningDiagram I G p hp hR hA n e).app T).hom x) =
        x ^ (p ^ e) := by
  let en := projectiveHomogeneousChartLinearEquiv
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) T
  let eb := projectiveHomogeneousChartLinearEquiv
    (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G) T
  have hf := congrArg (fun f ↦ (f.app T).hom (en.symm x))
    (reesClosedCechIntThickeningDiagram_factor (ι := ι) I G p hp hR hA n e)
  rw [reesHomogeneousThickeningDiagram_apply]
  have ht (z) : ((reesClosedHomogeneousModuleTransition I G (p ^ e * n) n
      (Nat.le_mul_of_pos_left n (pow_pos hp.pos e))).app T).hom (eb z) =
      en (((reesClosedRingTransitionChartMap (ι := ι) I G (p ^ e * n) n
        (Nat.le_mul_of_pos_left n (pow_pos hp.pos e)) 0).app T).hom z) := by
    change en (((reesClosedRingTransitionChartMap (ι := ι) I G (p ^ e * n) n
      (Nat.le_mul_of_pos_left n (pow_pos hp.pos e)) 0).app T).hom (eb.symm (eb z))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [ht]
  have hpw := projectiveHomogeneousChartLinearEquiv_iteratedFrobenius
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) T e (en.symm x)
  exact (congrArg en hf).trans (hpw.trans (congrArg (fun z ↦ z ^ (p ^ e))
    (en.apply_symm_apply x)))

/-- 厚化を経由する Frobenius が適合切断の加法群に誘導する写像。 -/
def reesHomogeneousSectionThickening (n e : ℕ) :
    projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) →+
    projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G) :=
  fullAlgebraCechEqualizerAddMap (reesHomogeneousThickeningDiagram I G p hp hR hA n e)

/-- 切断の厚化写像の各成分は整数線形な標準開の写像。 -/
theorem reesHomogeneousSectionThickening_apply (n e : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) (t : Fin 1 → ι) :
    (reesHomogeneousSectionThickening I G p hp hR hA n e a).val t =
      ((reesHomogeneousThickeningDiagram I G p hp hR hA n e).app (cechTupleSupport t)).hom
        (a.val t) := rfl

/-- 切断の厚化 Frobenius を制限で戻すと、実際の切断環の p^e 乗になる。 -/
theorem reesHomogeneousSectionThickening_factor (n e : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) :
    reesClosedHomogeneousSectionTransition I G (p ^ e * n) n
      (Nat.le_mul_of_pos_left n (pow_pos hp.pos e))
      (reesHomogeneousSectionThickening I G p hp hR hA n e a) = a ^ (p ^ e) := by
  apply Subtype.ext
  funext t
  rw [reesClosedHomogeneousSectionTransition_apply, reesHomogeneousSectionThickening_apply]
  exact (reesClosedHomogeneousModuleTransition_apply I G (p ^ e * n) n
    (Nat.le_mul_of_pos_left n (pow_pos hp.pos e)) (cechTupleSupport t) _).symm.trans
      (reesHomogeneousThickeningDiagram_factor I G p hp hR hA n e (cechTupleSupport t) (a.val t))

end SerrePositivity.AlgebraicGeometry
