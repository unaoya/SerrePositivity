module

public import SerrePositivity.CommutativeAlgebra.AdicRecurrence

/-! # 有界冪ねじれと主元進分離性 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 有界なf冪ねじれの下では、差分作用の単射性からf進分離性が従う。 -/
theorem isHausdorff_of_adicRecurrenceMap_injective_of_bounded_torsion (f : R)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, f ^ n • x = 0 → f ^ N • x = 0)
    (hinj : Function.Injective (adicRecurrenceMap (M := M) f)) :
    IsHausdorff (Ideal.span {f}) M := by
  classical
  obtain ⟨N, hN⟩ := hbounded
  constructor
  intro x hx
  have hdiv (n : ℕ) : ∃ y : M, f ^ n • y = x := by
    apply (mem_principal_pow_smul_top f n x).mp
    simpa only [sub_zero] using SModEq.sub_mem.mp (hx n)
  choose y hy using hdiv
  let z : ℕ → M := fun n ↦ f ^ N • y (n + N)
  have hstep (n : ℕ) : z n = f • z (n + 1) := by
    have herr : f ^ (n + N) • (y (n + N) - f • y (n + 1 + N)) = 0 := by
      rw [smul_sub, ← mul_smul, ← pow_succ, hy]
      have he : n + N + 1 = n + 1 + N := by omega
      rw [he, hy, sub_self]
    have h := hN (n + N) _ herr
    dsimp only [z]
    rw [smul_sub, smul_smul, mul_comm (f ^ N) f, ← smul_smul] at h
    exact sub_eq_zero.mp h
  have hz : adicRecurrenceMap f z = 0 := by
    ext n
    exact sub_eq_zero.mpr (hstep n)
  have hzero : z = 0 := hinj (hz.trans (map_zero _).symm)
  have hxz : z 0 = x := by simpa only [z, zero_add] using hy N
  rw [hzero] at hxz
  exact hxz.symm

end SerrePositivity
