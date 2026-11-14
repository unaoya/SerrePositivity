module

public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusRingColimit
public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusRingChartDiagram

/-!
概要：標準開の環の Frobenius 順極限の Čech 複体上で、閉厚化への制限を構成する。
方針：係数図式の同型で射を移し、各成分が実際の環の射影であることを示す。
規約：同じ閉厚化への制限の射を全複体への入力に用いる。
使われ方：F6 の正次数の計算と F7 の次数零を同じ環の係数で扱う。
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

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 標準開の環の順極限の係数図式上の、閉厚化への実際の制限。 -/
def reesClosedFrobeniusRingChartMap (n : ℕ) :
    projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA ⟶
      projectiveFrobeniusRingChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) :=
  (projectiveFrobeniusRingChartDiagramIso G p hp hR hA).inv ≫
    colim.map (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n) ≫
      (projectiveFrobeniusRingChartDiagramIso
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom

/-- 閉厚化の図式の射の各成分は、標準開の実際の環の射影が誘導する射。 -/
theorem reesClosedFrobeniusRingChartMap_app (n : ℕ) (T : Finset ι) :
    (reesClosedFrobeniusRingChartMap I G p hp hR hA n).app T =
      ModuleCat.ofHom (frobeniusDirectLimitMap p hp
        (projectiveHomogeneousChart_primeCast G p hR T)
        (projectiveHomogeneousChart_primeCast
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hR T)
        (reesClosedHomogeneousChartProjection I G n T)).toAddMonoidHom.toIntLinearMap := by
  change (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).inv ≫
    (colim.map (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n)).app T ≫
      (projectiveChartFrobeniusRingColimitIso
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) T).hom = _
  rw [reesClosedChartFrobeniusRingColimitIso_projection]
  simp only [Iso.inv_hom_id_assoc]

/-- 同じ環の係数図式の制限が誘導する、Čech 複体の射。 -/
def reesClosedFrobeniusRingCechMap (n : ℕ) :=
  fullCechComplexMap (reesClosedFrobeniusRingChartMap (ι := ι) I G p hp hR hA n)

/-- Čech 複体の二つの表示の同型は、閉厚化への実際の射と可換。 -/
theorem reesClosedFrobeniusRingCechIso_projection (n : ℕ) :
    reesClosedFrobeniusColimitCechMap G p hp hR hA I n ≫
        (projectiveFrobeniusRingChartCechIso (ι := ι)
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
          (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom =
      (projectiveFrobeniusRingChartCechIso (ι := ι) G p hp hR hA).hom ≫
        reesClosedFrobeniusRingCechMap I G p hp hR hA n := by
  change (fullCechComplexFunctor (R := ℤ) (ι := ι)).map _ ≫
      (fullCechComplexFunctor (R := ℤ) (ι := ι)).map _ =
    (fullCechComplexFunctor (R := ℤ) (ι := ι)).map _ ≫
      (fullCechComplexFunctor (R := ℤ) (ι := ι)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [reesClosedFrobeniusRingChartMap, Iso.hom_inv_id_assoc]

end SerrePositivity.AlgebraicGeometry
