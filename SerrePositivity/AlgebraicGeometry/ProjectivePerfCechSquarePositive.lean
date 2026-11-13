module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareComplexData
public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusRingCechPositive

/-!
概要：実際の四角形の差の余鎖写像は、正次数の Čech H に同型を誘導する。
方針：F6 の実際の閉厚化の制限の同型性を零次項拡張の差の射へ渡す。
規約：F8 のために新しい仮定で正次数の同型性を置かない。
使われ方：増大項付き cone の完全性判定の正次数の入力。
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
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable (I : Ideal R)
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechSquarePositiveGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

include hspan in
/-- 実際の差の射は正次数の Čech H に同型を誘導する。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の Hⁱ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfCechSquareDifferenceMap_positive_homology_bijective (n : ℕ) :
    Function.Bijective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} ℤ) (.up ℕ)
        n (n + 1) (n + 2)).map
          (projectivePerfCechSquareDifferenceMap (ι := ι) G I p hp hR hA))).hom := by
  apply (ConcreteCategory.isIso_iff_bijective _).mp
  dsimp only [projectivePerfCechSquareDifferenceMap, projectivePerfCechSquareSource]
  refine cechZeroTermDifference_positive_homology_isIso
    (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA))
    (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))))
    (reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1)
    (ModuleCat.of ℤ (FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))))
    (projectivePerfCechCenterAugmentation (ι := ι) G I p hp hR hA)
    (projectivePerfCechCenterAugmentation_d (ι := ι) G I p hp hR hA) ?_ n
  intro k
  let f := reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1
  have hb := reesClosedFrobeniusRingCechHomologyMap_bijective (ι := ι)
    G hspan I p hp hR hA (k + 1) (Nat.zero_lt_succ k)
  haveI : IsIso (HomologicalComplex.homologyMap f (k + 1)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have hq : QuasiIsoAt f (k + 1) :=
    (quasiIsoAt_iff_isIso_homologyMap f (k + 1)).mpr inferInstance
  have hs := (quasiIsoAt_iff' f k (k + 1) (k + 2)
    (ComplexShape.prev_eq' (.up ℕ) (by rfl))
    (ComplexShape.next_eq' (.up ℕ) (by rfl))).mp hq
  exact (ShortComplex.quasiIso_iff _).mp hs

end SerrePositivity.AlgebraicGeometry
