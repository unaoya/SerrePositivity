module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechCenterAugmentation

/-!
概要：中心の H⁰ 類の零次コサイクルと実際の増大写像の一致。
方針：有限段の元と商の代表元へ戻し、閉厚化上のスカラーの公式を使う。
規約：増大写像自体は各標準開の環準同型だけで定義済み。
使われ方：F7 の中心の辺を F8 の実際の余鎖写像へ移す。
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
local instance perfCechCenterCocycleGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 有限段の中心の代表元に対する H⁰ 類のコサイクルは実際の増大写像の値。 -/
theorem projectivePerfCechH0CenterClass_of_mk_cocycle
    (n : ℕ) (r : R) (t : Fin 1 → ι) :
    ((fullCechH0KernelIso (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))).hom.hom
        (projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA
          (frobeniusDirectLimitOf (R ⧸ (I ^ 1)) p hp
            (frobeniusQuotientPrimeCast p hR (I ^ 1)) n
            (Ideal.Quotient.mk (I ^ 1) r)))).val t =
      projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA
        (frobeniusDirectLimitOf (R ⧸ (I ^ 1)) p hp
          (frobeniusQuotientPrimeCast p hR (I ^ 1)) n
          (Ideal.Quotient.mk (I ^ 1) r)) t := by
  have hc := congrArg (fun b ↦
    ((fullCechH0KernelIso (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))).hom.hom b).val t)
    (projectivePerfCechH0CenterClass_of_mk (ι := ι) G I p hp hR hA n r)
  have hs := projectivePerfCechH0ScalarClass_of_cocycle (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) n r t
  have hm := congrArg (frobeniusDirectLimitOf _ p hp
    (projectiveHomogeneousChart_primeCast
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hR
      (cechTupleSupport t)) n)
    (projectiveClosedCenterChartMap_mk (ι := ι) G I t r).symm
  exact hc.trans (hs.trans hm)

/-- 中心の H⁰ 類の零次コサイクルは、任意の元で実際の増大写像に一致する。 -/
theorem projectivePerfCechH0CenterClass_augmentation
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    ((fullCechH0KernelIso (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))).hom.hom
        (projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA c)).val =
      projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA c := by
  obtain ⟨n, c, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) c
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  funext t
  exact projectivePerfCechH0CenterClass_of_mk_cocycle G I p hp hR hA n r t

/-- 中心の実際の増大写像の像は零次コサイクル。 -/
theorem projectivePerfCechCenterAugmentation_cycle
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    fullCechDifferential (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))) 1
        (projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA c) = 0 := by
  rw [← projectivePerfCechH0CenterClass_augmentation]
  exact ((fullCechH0KernelIso (projectiveFrobeniusRingChartDiagram (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))).hom.hom
      (projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA c)).property

end SerrePositivity.AlgebraicGeometry
