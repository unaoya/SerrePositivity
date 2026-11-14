module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraSectionEvaluation
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0CenterStage
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechScalarAugmentation

/-!
概要：基底の中心の Frobenius 順極限から閉厚化の零次コチェインへの実際の増大写像。
方針：中心の切断への因子化を各標準開で評価し、代表元の公式で H⁰ と照合する。
規約：増大写像の定義に H⁰ 比較やその逆を含めない。
使われ方：F8 の四角形の中心側の辺。
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
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechCenterAugmentationGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 中心の環から閉厚化の各標準開へ入る実際の環準同型。 -/
def projectiveClosedCenterChartMap (t : Fin 1 → ι) :
    R ⧸ (I ^ 1) →+* (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G)).obj
        (cechTupleSupport t) :=
  (fullAlgebraCechSectionEvaluation
    (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G)) t).toRingHom.comp
      (projectiveHomogeneousClosedCenterBaseMap (ι := ι) G I)

/-- 中心の代表元は各標準開で同じ基底スカラーとなる。 -/
theorem projectiveClosedCenterChartMap_mk (t : Fin 1 → ι) (r : R) :
    projectiveClosedCenterChartMap (ι := ι) G I t (Ideal.Quotient.mk (I ^ 1) r) =
      algebraMap R _ r :=
  congrArg (fun s ↦ s.val t) (projectiveHomogeneousClosedCenterBaseMap_mk (ι := ι) G I r)

/-- 中心の環から各標準開への写像で作る、零次の増大写像。 -/
def projectivePerfCechCenterAugmentation :
    FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1)) →ₗ[ℤ]
    FullCechCochains (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))) 1 :=
  LinearMap.pi fun t ↦ (frobeniusDirectLimitMap p hp
    (frobeniusQuotientPrimeCast p hR (I ^ 1))
    (projectiveHomogeneousChart_primeCast
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hR
      (cechTupleSupport t)) (projectiveClosedCenterChartMap (ι := ι) G I t)).toAddMonoidHom.toIntLinearMap

end SerrePositivity.AlgebraicGeometry
