module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechCenterCocycle
public import SerrePositivity.AlgebraicGeometry.CechZeroTermDifference
public import SerrePositivity.AlgebraicGeometry.FullCechH0ZeroTermCochains
public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusRingCech

/-!
概要：実際の標準開の環の Čech 複体と中心の零次項から、ブローアップ四角形の差の射を作る。
方針：零次項への直積の追加と、実際の中心の増大写像を使う。
規約：係数の写像は実際の環準同型で、H⁰ 比較を定義に含めない。
使われ方：F8 の明示的な増大全複体の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechSquareComplexDataGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 中心の増大写像は閉厚化の実際の Čech 複体の微分で零になる。 -/
theorem projectivePerfCechCenterAugmentation_d
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    ((fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))).d 0 1).hom
        (projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA c) = 0 := by
  rw [fullCechComplex_d]
  exact projectivePerfCechCenterAugmentation_cycle (ι := ι) G I p hp hR hA c

/-- 射影側の Čech 複体の零次項に、基底の中心の Frobenius 順極限を加える。 -/
def projectivePerfCechSquareSource : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  cechZeroTermExtension
    (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA))
    (ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))))

/-- 実際の閉厚化への制限と中心からの増大写像の差の余鎖写像。 -/
def projectivePerfCechSquareDifferenceMap :
    projectivePerfCechSquareSource (ι := ι) G I p hp hR hA ⟶
      fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))) :=
  cechZeroTermDifference _ _ (reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1)
    _ (projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA)
    (projectivePerfCechCenterAugmentation_d (ι := ι) G I p hp hR hA)

/-- 基底から、射影側のスカラーコチェインと基底の中心の元の組への実際の増大写像。 -/
def projectivePerfCechSquareAugmentation :
    FrobeniusDirectLimit R p hp hR →ₗ[ℤ]
      (projectivePerfCechSquareSource (ι := ι) G I p hp hR hA).X 0 :=
  (projectivePerfCechScalarAugmentation (ι := ι) G p hp hR hA).prod
    (frobeniusDirectLimitMap p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
      (Ideal.Quotient.mk (I ^ 1))).toAddMonoidHom.toIntLinearMap

end SerrePositivity.AlgebraicGeometry
