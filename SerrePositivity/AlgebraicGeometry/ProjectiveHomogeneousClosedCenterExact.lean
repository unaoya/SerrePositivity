module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFiniteCenterExact

/-!
概要：有限変更の四角形の右下を、閉厚化の実際の切断代数へ移す。
方針：Rees の評価から得た Frobenius 比較の全単射性を短完全列に合成する。
規約：入力は射影構造射の全射性と中心外の同型。核・像の評価は仮定しない。
使われ方：F7 の次数零の四角形を、切断の Frobenius 順極限で実現する。
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
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
local instance homogeneousClosedCenterExactGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 商切断環から閉厚化の切断環への、実際の Frobenius 順極限の射。 -/
abbrev projectiveHomogeneousClosedCenterComparison :=
  frobeniusDirectLimitMap p hp
    (frobeniusQuotientPrimeCast p
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
      ((I ^ 1).map (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G))))
    (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hR)
    (reesClosedHomogeneousSectionQuotientMap G I 1)

/-- 閉厚化の切断を右端に持つ差写像。各辺は商への射と実際の切断の制限の合成。 -/
def projectiveHomogeneousClosedCenterDifference :=
  (projectiveHomogeneousClosedCenterComparison (ι := ι) G I p hp hR).toAddMonoidHom.comp
    (frobeniusCenterDifference p hp hR
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) (I ^ 1))

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hspan in
/-- 射影構造射の中心の四角形は、切断の Frobenius 順極限で短完全。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。Čech H⁰ と順極限の交換は別途接続する。 -/
theorem projectiveHomogeneousClosedCenter_exact (hA : (p : A) = 0) :
    let pair := frobeniusCenterPair p hp hR
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) (I ^ 1)
    Function.Injective pair ∧
    Function.Exact pair (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR) ∧
    Function.Surjective (projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR) := by
  letI : IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
      affineCenterComplement (I ^ 1)) := by
    rw [show I ^ 1 = I from pow_one I]
    infer_instance
  have he' := projectiveHomogeneousFiniteCenter_exact G hspan (I ^ 1) p hp hR
  have hb := reesClosedHomogeneousSectionQuotientMap_frobenius_bijective (ι := ι) G I p hp hR hA
  refine ⟨he'.1, ?_, ?_⟩
  · intro x
    change projectiveHomogeneousClosedCenterComparison (ι := ι) G I p hp hR
      (frobeniusCenterDifference p hp hR _ _ (I ^ 1) x) = 0 ↔ _
    rw [← map_zero (projectiveHomogeneousClosedCenterComparison (ι := ι) G I p hp hR),
      hb.1.eq_iff]
    exact he'.2.1 x
  · exact hb.2.comp he'.2.2

end SerrePositivity.AlgebraicGeometry
