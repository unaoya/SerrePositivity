module

public import SerrePositivity.FieldTheory.FrobeniusPowerSubfield

/-! # 高い Frobenius 係数部分体上の生成

p-basis の有限台展開を Frobenius 冪で移して係数を次の部分体へ送る。
生成性だけを証明し、高い冪の単項式の独立性はここでは主張しない。
-/

@[expose] public section
namespace SerrePositivity

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
variable {ι : Type*} {b : ι → k}

/-- p-basis は任意の高い p 冪の係数部分体上でも、代数として体全体を生成する。 -/
theorem IsPBasis.adjoin_frobeniusPowerSubfield_eq_top (hb : IsPBasis k p b) (n : ℕ) :
    Algebra.adjoin (frobeniusPowerSubfield k p n) (Set.range b) = ⊤ := by
  classical
  induction n with
  | zero =>
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ frobeniusPowerSubfield k p 0 := by rw [frobeniusPowerSubfield_zero]; trivial
    exact (Algebra.adjoin (frobeniusPowerSubfield k p 0) (Set.range b)).algebraMap_mem ⟨x, hx⟩
  | succ n ih =>
    let A := Algebra.adjoin (frobeniusPowerSubfield k p (n + 1)) (Set.range b)
    have hpow (x : k) : x ^ p ^ n ∈ A := by
      rw [← hb.sum_expansionEquiv x]
      change iterateFrobenius k p n ((hb.expansionEquiv x).sum
        (fun d c ↦ c ^ p * pMonomial b d)) ∈ A
      rw [Finsupp.sum, map_sum]
      apply A.sum_mem
      intro d _
      rw [map_mul]
      change ((hb.expansionEquiv x d) ^ p) ^ p ^ n * (pMonomial b d) ^ p ^ n ∈ A
      have hc : ((hb.expansionEquiv x d) ^ p) ^ p ^ n ∈ A := by
        have heq : ((hb.expansionEquiv x d) ^ p) ^ p ^ n =
            (hb.expansionEquiv x d) ^ p ^ (n + 1) := by
          rw [← pow_mul, Nat.pow_succ, Nat.mul_comm]
        rw [heq]
        exact A.algebraMap_mem
          ⟨_, (mem_frobeniusPowerSubfield k p (n + 1) _).mpr ⟨_, rfl⟩⟩
      have hm : pMonomial b d ∈ A := by
        apply A.prod_mem
        intro i _
        exact A.pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) _
      exact A.mul_mem hc (A.pow_mem hm _)
    let A' : Subalgebra (frobeniusPowerSubfield k p n) k :=
      { A.toSubsemiring with
        algebraMap_mem' := fun c ↦ by
          obtain ⟨x, hx⟩ := (mem_frobeniusPowerSubfield k p n c).mp c.property
          change (c : k) ∈ A
          rw [← hx]
          exact hpow x }
    have hle : Algebra.adjoin (frobeniusPowerSubfield k p n) (Set.range b) ≤ A' := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact (show b i ∈ A from Algebra.subset_adjoin (Set.mem_range_self i))
    apply top_le_iff.mp
    intro x _
    exact hle (ih.symm ▸ Algebra.mem_top)

end SerrePositivity
