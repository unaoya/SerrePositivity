module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusFunctor
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechIntThickening

/-!
概要：閉厚化への制限を、実際の標準開の Frobenius 系の自然変換にする。
方針：厚化を経由する式と元の厚さへの遷移を合成する。
規約：各段の写像は構造環の実際の商への射影。
使われ方：perfection の係数図式上で F6 の制限を定める。
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
variable (I : Ideal R) (G : ℕ → Submodule R A) [DirectSum.Decomposition G]
variable [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 環の商への射影は、閉厚化の厚さを下げる遷移と可換。 -/
theorem reesClosedRingProjectionChartMap_transition (n m : ℕ) (h : m ≤ n) (d : ℤ) :
    reesClosedRingProjectionChartMap (ι := ι) I G n d ≫
        reesClosedRingTransitionChartMap (ι := ι) I G n m h d =
      reesClosedRingProjectionChartMap (ι := ι) I G m d := by
  simp only [reesClosedRingProjectionChartMap, reesClosedRingTransitionChartMap]
  rw [projectiveNatGradedModuleChartMap_comp]
  congr 1

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 閉厚化への実際の制限は、標準開の反復 Frobenius と可換。 -/
theorem reesClosedCechIntProjectionDiagram_frobenius (n e : ℕ) :
    Functor.whiskerRight (reesClosedRingProjectionChartMap (ι := ι) I G n 0)
        (ModuleCat.restrictScalars (Int.castRingHom R)) ≫
      projectiveCechIntFrobeniusDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) e =
    projectiveCechIntFrobeniusDiagram (ι := ι) G p hp hR hA e ≫
      Functor.whiskerRight (reesClosedRingProjectionChartMap (ι := ι) I G n 0)
        (ModuleCat.restrictScalars (Int.castRingHom R)) := by
  rw [← reesClosedCechIntThickeningDiagram_factor I G p hp hR hA n e,
    ← Category.assoc, reesClosedCechIntThickeningDiagram_projection,
    Category.assoc, ← Functor.whiskerRight_comp, reesClosedRingProjectionChartMap_transition]

/-- 実際の商への制限は Frobenius の係数系の自然変換を与える。 -/
def reesClosedFrobeniusCoefficientNatTrans (n : ℕ) :
    projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA ⟶
      projectiveCechFrobeniusCoefficientFunctor (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) where
  app _ := Functor.whiskerRight (reesClosedRingProjectionChartMap (ι := ι) I G n 0)
    (ModuleCat.restrictScalars (Int.castRingHom R))
  naturality {i j} _ :=
    (reesClosedCechIntProjectionDiagram_frobenius I G p hp hR hA n (j - i)).symm

end SerrePositivity.AlgebraicGeometry
