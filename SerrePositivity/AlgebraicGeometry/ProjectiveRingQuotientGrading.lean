module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusNaturality
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：実際の商環の次数成分と、その標準開・Čech Frobenius を作る。
方針：各次数の像を商環の部分加群とし、積と多項式作用を代表元で降ろす。
規約：次数の直和性をこのファイルでは仮定しない。商環が零でもよい。
使われ方：閉厚化の加群表示と実際の環の Frobenius の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (J : Ideal A) (G : ℕ → Submodule R A)

/-- 実際の商環の次数成分は、元の次数成分の商写像による像。 -/
def projectiveRingQuotientGrade (j : ℕ) : Submodule R (A ⧸ J) :=
  (G j).map (Ideal.Quotient.mkₐ R J).toLinearMap

/-- 環の商の次数成分は、単位と積を保つ。 -/
instance projectiveRingQuotientGradeGradedMonoid [SetLike.GradedMonoid G] :
    SetLike.GradedMonoid (projectiveRingQuotientGrade J G) where
  one_mem := ⟨1, SetLike.one_mem_graded G, map_one (Ideal.Quotient.mkₐ R J)⟩
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, (Ideal.Quotient.mkₐ R J).map_mul a b⟩

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 商環の次数成分は、元の多項式環の次数付き作用を受け継ぐ。 -/
instance projectiveRingQuotientGradeGradedSMul :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (projectiveRingQuotientGrade J G) where
  smul_mem := by
    intro i j a x ha hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨a • m, SetLike.GradedSMul.smul_mem ha hm,
      (Ideal.Quotient.mkₐ (MvPolynomial ι R) J).toLinearMap.map_smul a m⟩

/-- 実際の商写像は、商環の次数成分へ元の次数成分を送る。 -/
theorem projectiveRingQuotientProjection_preservesPiece (j : ℕ) (a : A) (ha : a ∈ G j) :
    (Ideal.Quotient.mkₐ (MvPolynomial ι R) J) a ∈ projectiveRingQuotientGrade J G j :=
  ⟨a, ha, rfl⟩

variable (p : ℕ) (hp : p.Prime) [ExpChar R p] (hz : (p : A) = 0)
variable [SetLike.GradedMonoid G]

include hz in
/-- p の像は、零環を許す実際の商環でも零。 -/
theorem projectiveRingQuotient_primeCast_eq_zero : (p : A ⧸ J) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk J), hz, map_zero]

/-- 実際の商環への射影と、標準開の Čech Frobenius は可換。
原典 BS17 Lemma 4.6(i) の Hⁱ と閉厚化の Frobenius に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveRingQuotientCechFrobenius_naturality (d : ℤ) (q : ℕ)
    (x : (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) :
    projectiveNatGradedCechFrobenius (ι := ι) p hp
        (projectiveRingQuotient_primeCast_eq_zero J p hz)
        (projectiveRingQuotientGrade J G) d q
        ((projectiveNatGradedModuleCechHomologyMap G (projectiveRingQuotientGrade J G)
          (Ideal.Quotient.mkₐ (MvPolynomial ι R) J).toLinearMap
          (projectiveRingQuotientProjection_preservesPiece (ι := ι) J G) d q).hom x) =
      (projectiveNatGradedModuleCechHomologyMap G (projectiveRingQuotientGrade J G)
          (Ideal.Quotient.mkₐ (MvPolynomial ι R) J).toLinearMap
          (projectiveRingQuotientProjection_preservesPiece (ι := ι) J G) ((p : ℤ) * d) q).hom
        (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q x) :=
  projectiveNatGradedCechFrobenius_naturality p hp hz G
    (projectiveRingQuotient_primeCast_eq_zero J p hz) (projectiveRingQuotientGrade J G)
    (Ideal.Quotient.mkₐ (MvPolynomial ι R) J)
    (projectiveRingQuotientProjection_preservesPiece (ι := ι) J G) d q x

end SerrePositivity.AlgebraicGeometry
