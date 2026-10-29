module

public import SerrePositivity.FieldTheory.FrobeniusPowerSubfield
public import SerrePositivity.FieldTheory.PBasisTransport
public import Mathlib.RingTheory.AlgebraTower

/-! # Frobenius 部分体の塔の各段階の基底

`k^{p^n}` の `k^{p^(n+1)}` 上の基底を、元の p-basis から実際に移送する。
部分体間の係数作用と、体同型の両立を明示する。
-/

@[expose] public section
namespace SerrePositivity

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

theorem frobeniusPowerSubfield_succ_le (n : ℕ) :
    frobeniusPowerSubfield k p (n + 1) ≤ frobeniusPowerSubfield k p n := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_frobeniusPowerSubfield k p (n + 1) x).mp hx
  refine (mem_frobeniusPowerSubfield k p n _).mpr ⟨y ^ p, ?_⟩
  rw [← pow_mul, pow_succ, Nat.mul_comm p (p ^ n)]

/-- 隣接する部分体間の係数作用は、包含写像によるもの。 -/
noncomputable instance frobeniusPowerAlgebra (n : ℕ) :
    Algebra (frobeniusPowerSubfield k p (n + 1)) (frobeniusPowerSubfield k p n) :=
  (Subfield.inclusion (frobeniusPowerSubfield_succ_le k p n)).toAlgebra

instance frobeniusPowerIsScalarTower (n : ℕ) :
    IsScalarTower (frobeniusPowerSubfield k p (n + 1)) (frobeniusPowerSubfield k p n) k :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- p 乗係数部分体を、塔の次の係数部分体へ移す同型。 -/
noncomputable def frobeniusLayerCoefficientEquiv (n : ℕ) :
    pPowerSubfield k p ≃+* frobeniusPowerSubfield k p (n + 1) :=
  (pPowerEquiv k p).symm.trans (frobeniusPowerEquiv k p (n + 1))

@[simp] theorem frobeniusLayerCoefficientEquiv_apply_coe (n : ℕ)
    (c : pPowerSubfield k p) :
    (frobeniusLayerCoefficientEquiv k p n c : k) = (c : k) ^ p ^ n := by
  change ((pPowerEquiv k p).symm c) ^ p ^ (n + 1) = (c : k) ^ p ^ n
  have hc : ((pPowerEquiv k p).symm c) ^ p = (c : k) :=
    congrArg Subtype.val ((pPowerEquiv k p).apply_symm_apply c)
  rw [pow_succ, Nat.mul_comm (p ^ n) p, pow_mul, hc]

/-- 塔の各段階で、係数の同型と元の同型は代数構造の写像と可換である。 -/
theorem frobeniusLayer_algebraMap_compat (n : ℕ) (c : pPowerSubfield k p) :
    frobeniusPowerEquiv k p n (algebraMap (pPowerSubfield k p) k c) =
      algebraMap (frobeniusPowerSubfield k p (n + 1)) (frobeniusPowerSubfield k p n)
        (frobeniusLayerCoefficientEquiv k p n c) := by
  apply Subtype.ext
  change (c : k) ^ p ^ n = (frobeniusLayerCoefficientEquiv k p n c : k)
  exact (frobeniusLayerCoefficientEquiv_apply_coe k p n c).symm

variable {k p} {ι : Type*} {b : ι → k}

/-- 塔の各段階の実際の基底。元の p-basis を、Frobenius 冪の同型で移送したもの。
添字の有限性・完全体性は不要。 -/
noncomputable def IsPBasis.frobeniusLayerBasis (hb : IsPBasis k p b) (n : ℕ) :
    Module.Basis (PExponent p ι) (frobeniusPowerSubfield k p (n + 1))
      (frobeniusPowerSubfield k p n) :=
  basisOfRingEquiv hb.basis (frobeniusLayerCoefficientEquiv k p n)
    (frobeniusPowerEquiv k p n) (frobeniusLayer_algebraMap_compat k p n)

/-- 各 Frobenius 段階で、移送した単項式は独立性だけでなく全体の基底になる。 -/
@[simp] theorem IsPBasis.frobeniusLayerBasis_apply (hb : IsPBasis k p b) (n : ℕ)
    (d : PExponent p ι) :
    hb.frobeniusLayerBasis n d = frobeniusPowerEquiv k p n (pMonomial b d) := by
  simp [IsPBasis.frobeniusLayerBasis, hb.basis_apply]

end SerrePositivity
