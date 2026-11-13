module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechBlowupSquareTotal
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap

/-!
概要：F8 の実際の四角形を、自然な全複体の構成のデータとして表す。
方針：検証済みの実際の三つの辺と可換性を保持し、元の全複体との等式を示す。
規約：元の acyclicity の定理や複体を別のものに置き換えない。
使われ方：共通細分・底変換等に沿う全複体の射を入れる入口。
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
local instance perfCechAugmentedSquareGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

/-- F8 の実際のスカラー・中心・閉厚化の射を、可換四角形のデータにまとめる。 -/
def projectivePerfCechAugmentedSquare : CechAugmentedSquare.{u} ℤ where
  C := fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)
  E := fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))
  restriction := reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1
  base := ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)
  centerBase := ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
    (frobeniusQuotientPrimeCast p hR (I ^ 1)))
  scalar := projectivePerfCechScalarAugmentation (ι := ι) G p hp hR hA
  quotient := (frobeniusDirectLimitMap p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
    (Ideal.Quotient.mk (I ^ 1))).toAddMonoidHom.toIntLinearMap
  center := projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA
  scalar_cycle := by
    intro x
    rw [fullCechComplex_d]
    exact projectivePerfCechScalarAugmentation_cycle (ι := ι) G p hp hR hA x
  center_cycle := projectivePerfCechCenterAugmentation_d (ι := ι) G I p hp hR hA
  commutes := by
    apply LinearMap.ext
    intro x
    have h := projectivePerfCechSquareDifference_augmentation_zero (ι := ι) G I p hp hR hA hspan x
    exact sub_eq_zero.mp h

/-- データから作る全複体は、F8 で検証した既存の実際の全複体そのもの。 -/
theorem projectivePerfCechAugmentedSquare_totalComplex :
    (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).totalComplex =
      projectivePerfCechBlowupSquareTotalComplex (ι := ι) G I p hp hR hA hspan := rfl

include hspan in
/-- 自然な四角形のデータとして表した F8 の全複体の acyclicity。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfCechAugmentedSquare_acyclic :
    (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).totalComplex.Acyclic := by
  rw [projectivePerfCechAugmentedSquare_totalComplex]
  exact projectivePerfCech_blowupSquare_acyclic (ι := ι) G I p hp hR hA hspan

end SerrePositivity.AlgebraicGeometry
