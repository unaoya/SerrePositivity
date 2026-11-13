module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusCanonicalDiagram
public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusRingCech
public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousAlgebraProjection

/-!
概要：実際の閉厚化の制限と、環の図式から直接作る Frobenius の射を同定する。
方針：有限段で斉次局所化の環の射影との既存の比較を適用する。
規約：F8 の制限の余鎖写像そのものを比較する。
使われ方：R/J 表示・閉厚化の自然性を全複体へ渡す。
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
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance frobeniusCanonicalProjectionGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化への制限は、実際の代数係数の環の射影に Frobenius を適用した自然変換。 -/
theorem reesClosedFrobeniusRingChartMap_canonical (n : ℕ) :
    reesClosedFrobeniusRingChartMap (ι := ι) I G p hp hR hA n ≫
      (projectiveFrobeniusRingChartDiagram_isoCanonical (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom =
    (projectiveFrobeniusRingChartDiagram_isoCanonical (ι := ι) G p hp hR hA).hom ≫
      frobeniusRingDiagramMap p hp
        (fun T ↦ projectiveHomogeneousChart_primeCast G p hR T)
        (hE := fun T ↦ projectiveHomogeneousChart_primeCast
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hR T)
        (whiskerRight (reesClosedHomogeneousAlgebraProjection (ι := ι) I G n)
          (forget₂ (CommAlgCat R) CommRingCat)) := by
  ext T x
  simp only [NatTrans.comp_app, projectiveFrobeniusRingChartDiagram_isoCanonical,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rw [reesClosedFrobeniusRingChartMap_app]
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T)) x
  exact congrArg (frobeniusDirectLimitOf _ p hp
    (projectiveHomogeneousChart_primeCast
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hR T) i)
    (reesClosedHomogeneousModuleProjection_apply I G n T x).symm

end SerrePositivity.AlgebraicGeometry
