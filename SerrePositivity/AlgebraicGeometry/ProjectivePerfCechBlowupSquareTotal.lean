module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareH0Surjective
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquarePositive

/-!
概要：射影中心の実際の四角形の明示的な増大全複体を構成し、その acyclicity を証明する。
方針：F7 の低次数の短完全性と F6 の正次数の同型性を既存の cone の判定へ渡す。
規約：完全性や同型性を追加仮定にせず、射影・Noether・中心外の同型・全射から供給する。
使われ方：2g の射影的細分で用いる BST13 Lemma 3.9 の Čech 版。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u v
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechBlowupSquareTotalGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hspan in
/-- 実際の基底の増大写像は cone の零次サイクルへ入る。 -/
theorem projectivePerfCechSquareAugmentation_cone_cycle :
    (cechRefinementConeDifferential
      (projectivePerfCechSquareSource (ι := ι) G I p hp hR hA)
      (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
        (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))))
      (projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA) 0).comp
        (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA) = 0 :=
  (projectivePerfCechSquareAugmentation_exact (ι := ι) G I p hp hR hA hspan).linearMap_comp_eq_zero

/-- 実際の射影中心の四角形の増大全複体。
零次は Perf(R)、一次は C(Y)⁰ × Perf(R/I)、以後は C(E) と C(Y) の項の直積。
微分は実際のスカラー・商・閉厚化の制限から作る。 -/
def projectivePerfCechBlowupSquareTotalComplex : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  augmentedCechCone
    (projectivePerfCechSquareSource (ι := ι) G I p hp hR hA)
    (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))))
    (projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA)
    (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))
    (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA)
    (projectivePerfCechSquareAugmentation_cone_cycle (ι := ι) G I p hp hR hA hspan)

include hspan in
/-- 射影中心の実際の四角形の増大全複体は acyclic。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。一般の導来層コホモロジーは構成しない。 -/
theorem projectivePerfCech_blowupSquare_acyclic :
    (projectivePerfCechBlowupSquareTotalComplex (ι := ι) G I p hp hR hA hspan).Acyclic := by
  let C := projectivePerfCechSquareSource (ι := ι) G I p hp hR hA
  let E := fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))
  let g := projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA
  let Z := ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)
  let a := projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA
  exact augmentedCechCone_acyclic C E g Z a
    (projectivePerfCechSquareAugmentation_cone_cycle (ι := ι) G I p hp hR hA hspan)
    (projectivePerfCechSquareAugmentation_injective (ι := ι) G I p hp hR hA hspan)
    (projectivePerfCechSquareAugmentation_exact (ι := ι) G I p hp hR hA hspan)
    (projectivePerfCechSquareDifferenceMap_homology_zero_surjective (ι := ι) G I p hp hR hA hspan)
    (fun n ↦ projectivePerfCechSquareDifferenceMap_positive_homology_bijective (ι := ι)
      G hspan I p hp hR hA n)

end SerrePositivity.AlgebraicGeometry
