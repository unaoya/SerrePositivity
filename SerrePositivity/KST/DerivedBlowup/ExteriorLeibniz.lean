module

public import SerrePositivity.KST.DerivedBlowup.ExteriorGrading

/-!
概要：KST Def3.1 の外積 Koszul 微分の graded Leibniz 則を証明する。
方針：同次部分を生成元の像の冪として扱い、左生成元の積について帰納する。
規約：外積次数nは cochain 次数−n、符号はどちらも (−1)^n。
使われ方：Koszul チャートの積を複体の chain map として装備する。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：同次左因子に対する外積収縮の graded Leibniz 則。
方針：係数・同次の和・生成元の左乗法の三段で証明する。
規約：KST Def3.1、右因子は非同次でもよい。使われ方：Koszul dg 代数の微分と積の適合。 -/
theorem exteriorContraction_mul (d : M →ₗ[R] R) (n : ℕ) (x : ExteriorAlgebra R M)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R n M) (y : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := 0) d (x * y) =
      CliffordAlgebra.contractLeft (Q := 0) d x * y +
        (-1 : R) ^ n • (x * CliffordAlgebra.contractLeft (Q := 0) d y) := by
  change x ∈ (LinearMap.range (ExteriorAlgebra.ι R (M := M))) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' generalizing y with
  | algebraMap r =>
    rw [CliffordAlgebra.contractLeft_algebraMap_mul,
      CliffordAlgebra.contractLeft_algebraMap, zero_mul, zero_add, pow_zero, one_smul]
  | add x z n hx hz ihx ihz =>
    rw [add_mul, map_add, ihx, ihz, map_add, add_mul, add_mul, smul_add]
    abel
  | mem_mul m hm n x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, ih,
      CliffordAlgebra.contractLeft_ι_mul]
    simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm,
      mul_assoc, pow_succ, mul_neg_one, neg_smul]
    abel

end SerrePositivity.KST.DerivedBlowup
