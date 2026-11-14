module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareKernelComparison
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0Square

/-!
概要：F7 の左辺を実際の四角形の増大写像と同定し、その単射性を移す。
方針：H⁰ と中心の項から零次コサイクルへの単射を合成する。
規約：実際の増大写像の定義は各標準開のスカラーと基底の商の写像。
使われ方：F8 の全複体の最初の項の完全性。
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
local instance perfCechSquareAugmentationComparisonGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- H⁰ と基底の中心の組を、実際の四角形の零次コチェインへ写す加法準同型。 -/
def projectivePerfCechH0ToSquareCochains :
    (projectivePerfCechH0 (ι := ι) G p hp hR hA ×
      FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) →+
      (projectivePerfCechSquareSource (ι := ι) G I p hp hR hA).X 0 :=
  (fullCechH0ZeroTermCochainMap
    (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)
    (ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))))).toAddMonoidHom

/-- F7 の組の写像をコサイクルへ移すと、実際の基底の増大写像となる。 -/
theorem projectivePerfCechH0Pair_cochains (a : FrobeniusDirectLimit R p hp hR) :
    projectivePerfCechH0ToSquareCochains (ι := ι) G I p hp hR hA
      (projectivePerfCechH0Pair (ι := ι) G I p hp hR hA a) =
    projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA a := by
  rw [projectivePerfCechH0Pair_apply]
  apply Prod.ext
  · exact projectivePerfCechH0ScalarClass_augmentation (ι := ι) G p hp hR hA a
  · rfl

/-- 実際の基底の増大写像の像は、中心の項を加えた複体のコサイクル。 -/
theorem projectivePerfCechSquareAugmentation_cycle (a : FrobeniusDirectLimit R p hp hR) :
    ((projectivePerfCechSquareSource (ι := ι) G I p hp hR hA).d 0 1).hom
      (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA a) = 0 := by
  rw [← projectivePerfCechH0Pair_cochains]
  exact fullCechH0ZeroTermCochainMap_cycle
    (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)
    (ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1)))) _

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hspan in
/-- 実際の四角形の基底の増大写像は単射。 -/
theorem projectivePerfCechSquareAugmentation_injective :
    Function.Injective (projectivePerfCechSquareAugmentation (ι := ι) G I p hp hR hA) := by
  have h := projectivePerfCechH0_square_exact (ι := ι) G I p hp hR hA hspan
  intro a b hab
  apply h.1
  apply fullCechH0ZeroTermCochainMap_injective
    (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)
    (ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))))
  change projectivePerfCechH0ToSquareCochains (ι := ι) G I p hp hR hA _ =
    projectivePerfCechH0ToSquareCochains (ι := ι) G I p hp hR hA _
  rw [projectivePerfCechH0Pair_cochains, projectivePerfCechH0Pair_cochains]
  exact hab

end SerrePositivity.AlgebraicGeometry
