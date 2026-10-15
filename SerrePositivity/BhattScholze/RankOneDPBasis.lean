module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.DividedPowers.RatAlgebra
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # 既存一元分冪代数の具体的基底

線形生成は任意の可換環で成立する。線形独立性にはℚ代数への単射を明示する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]

/-- 任意の可換環上の一元分冪代数は全γ_n(1)で線形生成される。 -/
theorem rankOneDP_span_eq_top :
    Submodule.span A (Set.range (fun n : ℕ ↦ DividedPowerAlgebra.dp A n (1 : A))) = ⊤ := by
  let V := Submodule.span A (Set.range (fun n : ℕ ↦ DividedPowerAlgebra.dp A n (1 : A)))
  apply top_unique
  intro f hf
  clear hf
  change f ∈ V
  induction f using DividedPowerAlgebra.induction_on with
  | C a =>
      have h0 : DividedPowerAlgebra.dp A 0 (1 : A) ∈ V :=
        Submodule.subset_span (Set.mem_range_self 0)
      simpa only [DividedPowerAlgebra.dp_zero, Algebra.smul_def, mul_one] using V.smul_mem a h0
  | add f g hf hg => exact V.add_mem hf hg
  | dp f n a hf =>
      have ha : DividedPowerAlgebra.dp A n a =
          a ^ n • DividedPowerAlgebra.dp A n (1 : A) := by
        simpa only [smul_eq_mul, mul_one] using
          (DividedPowerAlgebra.dp_smul (R := A) (r := a) (n := n) (m := (1 : A)))
      rw [ha, mul_smul_comm]
      apply V.smul_mem
      induction hf using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨k, rfl⟩ := hz
          rw [DividedPowerAlgebra.dp_mul]
          have hmem : DividedPowerAlgebra.dp A (k + n) (1 : A) ∈ V :=
            Submodule.subset_span (Set.mem_range_self (k + n))
          exact nsmul_mem hmem _
      | zero => simpa only [zero_mul] using V.zero_mem
      | add x z hx hz ihx ihz => simpa only [add_mul] using V.add_mem ihx ihz
      | smul r z hz ih => simpa only [smul_mul_assoc] using V.smul_mem r ih

/-- 有理代数の多項式環への標準分冪評価。 -/
def rankOneDPPolynomialEval (A : Type u) [CommRing A] (C : Type v) [CommRing C]
    [Algebra A C] [Algebra ℚ C] : DividedPowerAlgebra A A →ₐ[A] Polynomial C := by
  classical
  exact DividedPowerAlgebra.lift
    (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal (Polynomial C)))
    (LinearMap.toSpanSingleton A (Polynomial C) Polynomial.X)
    (by intro m; exact Submodule.mem_top)

/-- 標準評価はγ_n(1)を、係数環内の階乗逆数倍のX^nへ送る。 -/
theorem rankOneDPPolynomialEval_dp (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (n : ℕ) :
    rankOneDPPolynomialEval A C (DividedPowerAlgebra.dp A n (1 : A)) =
      Polynomial.C (Ring.inverse (n.factorial : C)) * Polynomial.X ^ n := by
  classical
  rw [rankOneDPPolynomialEval, DividedPowerAlgebra.lift_apply_dp,
    LinearMap.toSpanSingleton_apply_one, DividedPowers.RatAlgebra.dpow_apply,
    ite_eq_left (by trivial)]
  have hunit := IsUnit.natCast_factorial_of_algebra ℚ n (A := C)
  have hm := hunit.map_ringInverse Polynomial.C
  simp only [map_natCast] at hm
  rw [← hm]

/-- 有理代数への単射がある場合、全γ_n(1)は線形独立。 -/
theorem rankOneDP_linearIndependent (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (hAC : Function.Injective (algebraMap A C)) :
    LinearIndependent A (fun n : ℕ ↦ DividedPowerAlgebra.dp A n (1 : A)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a hs n hn
  have he := congrArg (fun z : Polynomial C ↦ z.coeff n)
    (congrArg (rankOneDPPolynomialEval A C) hs)
  have he' : algebraMap A C (a n) * Ring.inverse (n.factorial : C) = 0 := by
    simpa [map_sum, map_smul, rankOneDPPolynomialEval_dp, Polynomial.coeff_sum,
      Polynomial.coeff_smul, Polynomial.coeff_C_mul_X_pow, Algebra.smul_def, hn] using he
  have hem := congrArg (fun z : C ↦ z * (n.factorial : C)) he'
  rw [mul_assoc, Ring.inverse_mul_cancel _
    (IsUnit.natCast_factorial_of_algebra ℚ n), mul_one, zero_mul] at hem
  apply hAC
  simpa only [map_zero] using hem

/-- 有理代数への単射の下での、既存一元分冪代数の実基底。 -/
def rankOneDPBasis (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (hAC : Function.Injective (algebraMap A C)) :
    Module.Basis ℕ A (DividedPowerAlgebra A A) :=
  Module.Basis.mk (rankOneDP_linearIndependent C hAC) (by rw [rankOneDP_span_eq_top])

/-- 構成した基底の値は元の標準分冪生成元そのもの。 -/
theorem rankOneDPBasis_apply (C : Type v) [CommRing C] [Algebra A C] [Algebra ℚ C]
    (hAC : Function.Injective (algebraMap A C)) (n : ℕ) :
    rankOneDPBasis C hAC n = DividedPowerAlgebra.dp A n (1 : A) :=
  Module.Basis.mk_apply _ _ _

end SerrePositivity.BhattScholze
