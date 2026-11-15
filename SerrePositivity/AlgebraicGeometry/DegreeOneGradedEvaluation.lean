module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
概要：係数環の異なる次数付き環への、次数一元による評価の次数保存。
方針：斉次多項式を単項式に展開し、定数の次数零と graded な有限積を使う。
規約：係数が次数零に入ることを明示する。平坦性は要求しない。
使われ方：G3 の Segre 座標を底変換した grading に送る接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R S C ι : Type*} [CommRing R] [CommRing S] [CommRing C]
variable [Algebra R C] [Module S C] (D : ℕ → Submodule S C) [SetLike.GradedMonoid D]
variable (hR : ∀ r : R, algebraMap R C r ∈ D 0) (x : ι → C) (hx : ∀ i, x i ∈ D 1)
include hR hx

/-- 次数一の元による実際の評価は、係数が次数零なら斉次次数を保つ。 -/
theorem degreeOne_aeval_mem_grade {d : ℕ} (f : MvPolynomial ι R)
    (hf : f ∈ MvPolynomial.homogeneousSubmodule ι R d) :
    MvPolynomial.aeval (R := R) x f ∈ D d := by
  classical
  rw [← f.support_sum_monomial_coeff, map_sum]
  apply Submodule.sum_mem
  intro s hs
  rw [MvPolynomial.aeval_monomial]
  have hprod := SetLike.prod_pow_mem_graded D (fun _ : ι ↦ (1 : ℕ)) x s
    (F := s.support) (fun i _ ↦ hx i)
  have hdeg := (MvPolynomial.mem_homogeneousSubmodule d f).mp hf
  have he : (∑ i ∈ s.support, s i • (1 : ℕ)) = d := by
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using
      (hdeg.degree_eq_sum_deg_support hs).symm
  rw [he] at hprod
  simpa only [zero_add, Finsupp.prod] using
    SetLike.mul_mem_graded (hR (f.coeff s)) hprod

/-- 同じ次数一評価を束ねた graded な環準同型。 -/
def degreeOneGradedEvaluation : (MvPolynomial.homogeneousSubmodule ι R) →+*ᵍ D where
  toRingHom := (MvPolynomial.aeval (R := R) x).toRingHom
  map_mem := fun hf ↦ degreeOne_aeval_mem_grade D hR x hx _ hf

end SerrePositivity.AlgebraicGeometry
