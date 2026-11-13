module

public import SerrePositivity.AlgebraicGeometry.ReesHomogeneousFrobeniusCoefficientComparison

/-!
概要：F6 の閉厚化の複体の射と、切断の Frobenius 順極限の射を H⁰ で照合する。
方針：係数系の可換性を全タプル複体と H⁰ に送り、自然な切断比較を合成する。
規約：制限の射は F6 の reesClosedFrobeniusRingCechMap そのもの。
使われ方：F7 の短完全列と F8 の正次数の計算を同じ射について使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance reesHomogeneousFrobeniusH0ComparisonGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 標準開環の複体と斉次代数係数の複体の比較は、閉厚化の実際の射と可換。 -/
theorem projectiveHomogeneousFrobeniusRingCechIso_projection (n : ℕ) :
    reesClosedFrobeniusRingCechMap I G p hp hR hA n ≫
      (projectiveHomogeneousFrobeniusRingCechIso (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom =
    (projectiveHomogeneousFrobeniusRingCechIso (ι := ι) G p hp hR hA).hom ≫
      fullCechComplexMap (colim.map (algebraCechFrobeniusCoefficientNatTrans
        (reesClosedHomogeneousAlgebraProjection I G n) p hp hR)) := by
  let F := fullCechComplexFunctor (R := ℤ) (ι := ι)
  change F.map _ ≫ (F.map _ ≫ F.map _) = (F.map _ ≫ F.map _) ≫ F.map _
  simp only [← Functor.map_comp]
  congr 1
  simp only [reesClosedFrobeniusRingChartMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [projectiveHomogeneousFrobeniusCoefficientColimitIso_projection]

/-- 閉厚化の Čech H⁰ の射は、切断の実際の制限が誘導する Frobenius 順極限の射。 -/
theorem projectiveHomogeneousFrobeniusRingCechH0Iso_projection (n : ℕ) :
    HomologicalComplex.homologyMap (reesClosedFrobeniusRingCechMap I G p hp hR hA n) 0 ≫
      (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom =
    (projectiveHomogeneousFrobeniusRingCechH0Iso (ι := ι) G p hp hR hA).hom ≫
      ModuleCat.ofHom (frobeniusDirectLimitMap p hp
        (algebraCechEqualizer_primeCast (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hR)
        (algebraCechEqualizer_primeCast (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) p hR)
        (reesClosedHomogeneousSectionProjection (ι := ι) G I n).toRingHom).toAddMonoidHom.toIntLinearMap := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0
  have hc := congrArg H.map
    (projectiveHomogeneousFrobeniusRingCechIso_projection (ι := ι) I G p hp hR hA n)
  simp only [Functor.map_comp] at hc
  let eQ := algebraCechFrobeniusH0ColimitIso
    (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) p hp hR
  have hc' := congrArg (fun f ↦ f ≫ eQ.hom) hc
  have hn := algebraCechFrobeniusH0ColimitIso_naturality
    (reesClosedHomogeneousAlgebraProjection (ι := ι) I G n) p hp hR
  have hn' := congrArg (fun f ↦ H.map
    (projectiveHomogeneousFrobeniusRingCechIso (ι := ι) G p hp hR hA).hom ≫ f) hn
  exact ((Category.assoc _ _ _).symm.trans hc').trans
    ((Category.assoc _ _ _).trans hn')

end SerrePositivity.AlgebraicGeometry
