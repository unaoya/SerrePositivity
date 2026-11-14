module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechAugmentedSquare
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareTransport
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison

/-!
概要：F8 の増大全複体を、実際の Proj の構造層の Frobenius 係数へ移す。
方針：二つの Čech 複体の検証済みの同型を四角形ごと移し、全複体の同型を使う。
規約：完全性を仮定に追加せず、F8 の既存の acyclicity から証明する。
使われ方：native な被覆比較と F8 の全複体の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfectNativeSquareGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G 1
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

/-- F8 の四角形を、実際の Proj と次数付き商の Proj の構造層の係数へ移したもの。 -/
def projectivePerfectNativeAugmentedSquare : CechAugmentedSquare.{u} ℤ :=
  (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).transport
    (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA)
    (projectivePerfectNativeCechComplexIso (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))

/-- F8 の実際の全複体と、native な構造層での全複体の同型。 -/
def projectivePerfectNativeTotalComplexIso :
    (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).totalComplex ≅
      (projectivePerfectNativeAugmentedSquare (ι := ι) G I p hp hR hA hspan).totalComplex :=
  (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).transportTotalComplexIso
    (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA)
    (projectivePerfectNativeCechComplexIso (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))

/-- 実際の構造層の Frobenius 係数へ移した射影四角形の増大全複体は acyclic。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の射影 Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfectNativeSquare_acyclic :
    (projectivePerfectNativeAugmentedSquare (ι := ι) G I p hp hR hA hspan).totalComplex.Acyclic :=
  (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).transport_acyclic _ _
    (projectivePerfCechAugmentedSquare_acyclic (ι := ι) G I p hp hR hA hspan)

end SerrePositivity.AlgebraicGeometry
