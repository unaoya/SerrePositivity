module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechAugmentedSquare
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareTransport
public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeProjection

/-!
概要：F8 の増大全複体を、実際の Cartesian な閉厚化の構造層へ移す。
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
local instance perfectCartesianSquareGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G 1
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1)))
variable (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))))

/-- F8 の四角形を、実際の Proj と Cartesian な閉厚化 の構造層の係数へ移したもの。 -/
def projectivePerfectCartesianAugmentedSquare : CechAugmentedSquare.{u} ℤ :=
  (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).transport
    (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA)
    (reesClosedPerfectNativeCechIso I G 1 iY g H p hp hR hA)

/-- F8 の実際の全複体と、native な構造層での全複体の同型。 -/
def projectivePerfectCartesianTotalComplexIso :
    (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).totalComplex ≅
      (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).totalComplex :=
  (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).transportTotalComplexIso
    (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA)
    (reesClosedPerfectNativeCechIso I G 1 iY g H p hp hR hA)

/-- 実際の構造層の Frobenius 係数へ移した射影四角形の増大全複体は acyclic。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の射影 Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfectCartesianSquare_acyclic :
    (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).totalComplex.Acyclic :=
  (projectivePerfCechAugmentedSquare (ι := ι) G I p hp hR hA hspan).transport_acyclic _ _
    (projectivePerfCechAugmentedSquare_acyclic (ι := ι) G I p hp hR hA hspan)

/-- 移送した四角形の制限の辺は、実際の構造層の引き戻しそのもの。 -/
theorem projectivePerfectCartesianAugmentedSquare_restriction :
    (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).restriction =
      schemeStructurePerfectCechPullbackMap g p hp
        (projectiveProjPresheaf_primeCast G p hR)
        (projectivePullbackPresheaf_primeCast G g p hR)
        (projectiveProjCechOpen (ι := ι) G) := by
  change (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).inv ≫
    reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1 ≫
      (reesClosedPerfectNativeCechIso I G 1 iY g H p hp hR hA).hom = _
  rw [reesClosedPerfectNativeCechIso_naturality]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.AlgebraicGeometry
