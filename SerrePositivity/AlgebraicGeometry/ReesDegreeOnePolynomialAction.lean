module

public import SerrePositivity.AlgebraicGeometry.ReesFiniteDegreeOnePresentation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.GradedMulAction

/-!
概要：実際の次数一表示を、多項式環の次数付き作用と有限加群性に渡す。
方針：斉次多項式を単項式に展開し、既存の graded な有限積の法則を使う。
規約：表示の評価から構成した係数作用を使い、全射性は有限加群性だけに使う。
使われ方：G3 の Rees Proj に 2f の射影 Čech の入力を供給する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open Polynomial
universe u v
variable {R : Type u} {ι : Type v} [CommRing R] (I : Ideal R) (a : ι → I)

/-- 次数一の実際の評価からの多項式代数構造。 -/
abbrev reesDegreeOnePolynomialAlgebra : Algebra (MvPolynomial ι R) (reesAlgebra I) :=
  (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))).toAlgebra

/-- 評価による作用は元の R 作用と両立する。 -/
def reesDegreeOnePolynomial_scalarTower :
    letI := reesDegreeOnePolynomialAlgebra I a
    IsScalarTower R (MvPolynomial ι R) (reesAlgebra I) := by
  letI := reesDegreeOnePolynomialAlgebra I a
  exact IsScalarTower.of_algebraMap_eq'
    (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))).comp_algebraMap.symm

/-- 全射な実際の評価は、その多項式環上の有限加群構造を与える。 -/
theorem reesDegreeOnePolynomial_finite
    (h : Function.Surjective (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j)))) :
    letI := reesDegreeOnePolynomialAlgebra I a
    Module.Finite (MvPolynomial ι R) (reesAlgebra I) := by
  letI := reesDegreeOnePolynomialAlgebra I a
  exact Module.Finite.of_surjective (Algebra.linearMap _ _) h

/-- 次数 d の斉次多項式の次数一元での評価は Rees 次数 d に入る。 -/
theorem reesDegreeOne_aeval_mem {d : ℕ} (f : MvPolynomial ι R)
    (hf : f ∈ MvPolynomial.homogeneousSubmodule ι R d) :
    MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j)) f ∈ reesGrade I d := by
  classical
  rw [← f.support_sum_monomial_coeff, map_sum]
  apply Submodule.sum_mem
  intro s hs
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  have hprod := SetLike.prod_pow_mem_graded (reesGrade I) (fun _ : ι ↦ (1 : ℕ))
    (fun j ↦ reesDegreeOne I (a j)) s (F := s.support) (fun j _ ↦ reesDegreeOne_mem I (a j))
  have hdeg := (MvPolynomial.mem_homogeneousSubmodule d f).mp hf
  have he : (∑ k ∈ s.support, s k • (1 : ℕ)) = d := by
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using
      (hdeg.degree_eq_sum_deg_support hs).symm
  simpa only [he, Finsupp.prod] using hprod

/-- 実際の評価による多項式作用は次数付きの作用。 -/
def reesDegreeOnePolynomial_gradedSMul :
    letI := reesDegreeOnePolynomialAlgebra I a
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (reesGrade I) := by
  letI := reesDegreeOnePolynomialAlgebra I a
  refine ⟨?_⟩
  intro d e f x hf hx
  change MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j)) f * x ∈
    reesGrade I (d + e)
  exact SetLike.mul_mem_graded (reesDegreeOne_aeval_mem I a f hf) hx

end SerrePositivity.AlgebraicGeometry
