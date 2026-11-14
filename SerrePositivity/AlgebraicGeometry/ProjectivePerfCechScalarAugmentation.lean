module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0ScalarCocycle

/-!
概要：基底の Frobenius 順極限から標準開の零次コチェインへの実際の増大写像。
方針：各標準開への環準同型の Frobenius 順極限を成分とし、H⁰ との照合で閉性を示す。
規約：増大写像の定義には H⁰ 比較やその逆を含めない。
使われ方：F8 の明示的な増大全複体の最初の微分。
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
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 各標準開への実際のスカラー環準同型から作る零次の増大写像。 -/
def projectivePerfCechScalarAugmentation :
    FrobeniusDirectLimit R p hp hR →ₗ[ℤ]
      FullCechCochains (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA) 1 :=
  LinearMap.pi fun t ↦ (frobeniusDirectLimitMap p hp hR
    (projectiveHomogeneousChart_primeCast G p hR (cechTupleSupport t))
    (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj
      (cechTupleSupport t)))).toAddMonoidHom.toIntLinearMap

/-- H⁰ のスカラー類の零次コサイクルは実際の増大写像に一致する。 -/
theorem projectivePerfCechH0ScalarClass_augmentation
    (a : FrobeniusDirectLimit R p hp hR) :
    ((fullCechH0KernelIso
      (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).hom.hom
        (projectivePerfCechH0ScalarClass (ι := ι) G p hp hR hA a)).val =
      projectivePerfCechScalarAugmentation (ι := ι) G p hp hR hA a := by
  funext t
  exact projectivePerfCechH0ScalarClass_cocycle G p hp hR hA a t

/-- 実際の増大写像の像は零次コサイクルである。 -/
theorem projectivePerfCechScalarAugmentation_cycle
    (a : FrobeniusDirectLimit R p hp hR) :
    fullCechDifferential
      (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA) 1
      (projectivePerfCechScalarAugmentation (ι := ι) G p hp hR hA a) = 0 := by
  rw [← projectivePerfCechH0ScalarClass_augmentation]
  exact ((fullCechH0KernelIso
    (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).hom.hom
      (projectivePerfCechH0ScalarClass (ι := ι) G p hp hR hA a)).property

end SerrePositivity.AlgebraicGeometry
