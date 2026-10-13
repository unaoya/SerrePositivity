module

public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusKernel

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.Regular.SMul

/-! # 正則な p 乗根と Frobenius 核条件からの reduced 性

正則元 π の p 乗が p であり、x^p が p で割れれば x が π で割れるとき、
p 進分離性から環の reduced 性を導く。
この具体的な条件を integral perfectoid の定義から導く部分、
および p ねじれを持つ環の分解はここで仮定・証明済みと扱わない。
-/

@[expose] public section
universe u
namespace SerrePositivity

/-- 正則な p 乗根と具体的な Frobenius 核条件、p 進分離性から環は reduced。
x^p=0 の場合を正則 π で繰り返し割り、p の全冪に入ることを示す。
p ねじれを許す perfectoid 環の一般の reduced 定理とは区別する。 -/
theorem isReduced_of_regular_root_frobenius_kernel
    (R : Type u) [CommRing R] (p : ℕ) (hp : 1 < p)
    (π : R) (hπ : π ^ p = (p : R)) (hregular : IsSMulRegular R π)
    (hsep : IsHausdorff (Ideal.span {(p : R)}) R)
    (hF : ∀ x : R, x ^ p ∈ Ideal.span {(p : R)} → x ∈ Ideal.span {π}) :
    IsReduced R := by
  apply (isReduced_iff_pow_one_lt p hp).mpr
  intro x hx
  have hfactor (k : ℕ) : ∃ y : R, x = π ^ k * y ∧ y ^ p = 0 := by
    induction k with
    | zero => exact ⟨x, by simp, hx⟩
    | succ k ih =>
        obtain ⟨y, hxy, hy⟩ := ih
        have hyπ : y ∈ Ideal.span {π} := hF y (hy ▸ Ideal.zero_mem _)
        obtain ⟨z, hyz⟩ := Ideal.mem_span_singleton.mp hyπ
        have hz : z ^ p = 0 := by
          apply IsSMulRegular.pow p hregular
          change π ^ p * z ^ p = π ^ p * 0
          rw [← mul_pow, ← hyz, hy, mul_zero]
        refine ⟨z, ?_, hz⟩
        rw [hxy, hyz, pow_succ, mul_assoc]
  apply hsep.haus x
  intro n
  apply SModEq.zero.mpr
  change x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Ideal R)
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨y, hxy, _⟩ := hfactor (p * n)
  apply Ideal.mem_span_singleton.mpr
  refine ⟨y, ?_⟩
  simpa only [pow_mul, hπ] using hxy

/-- 正則なp乗根を持つ整perfectoid環では、四条件から被約性を供給する。
一般のpねじれを持つ場合の分解は、この結果には含めない。 -/
theorem IsIntegralPerfectoid.isReduced_of_regular_p_root
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (π : R) (hπ : π ^ p = (p : R))
    (hregular : IsSMulRegular R π) : IsReduced R := by
  rcases hR with hsub | hdata
  · let : Subsingleton R := hsub
    exact ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
  · have hR' : IsIntegralPerfectoid R p := Or.inr hdata
    obtain ⟨hp, hc, _⟩ := hdata
    let := hc
    apply isReduced_of_regular_root_frobenius_kernel R p (Fact.out : p.Prime).one_lt
      π hπ hregular inferInstance
    intro x hx
    apply hR'.frobenius_kernel_of_unit_root R p π 1 (by simpa using hπ.symm) x
    simpa only [hπ] using hx

end SerrePositivity
