module

public import SerrePositivity.FieldTheory.PMonomialSpan
public import SerrePositivity.FieldTheory.PAdjoin
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # 指定された底体上の相対p単項式空間

各生成元のp乗が底体の像にあるとき、p未満の単項式の線形包は生成部分代数に等しい。
底体を絶対p乗部分体に固定せず、添字の有限性も要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {F K ι : Type*} [Field F] [Field K] [Algebra F K]
  {p : ℕ} [Fact p.Prime] [CharP K p] (b : ι → K)
  (hpow : ∀ i, ∃ a : F, b i ^ p = algebraMap F K a)

include hpow

omit [CharP K p] in
/-- 相対p単項式の線形包は、指定された底体上の生成部分代数に等しい。 -/
theorem span_pMonomial_eq_adjoin_of_pow_mem :
    Submodule.span F (Set.range (pMonomial (p := p) b)) =
      (Algebra.adjoin F (Set.range b)).toSubmodule := by
  classical
  let S := Submodule.span F (Set.range (pMonomial (p := p) b))
  have h1 : (1 : K) ∈ S := Submodule.subset_span ⟨0, pMonomial_zero b⟩
  have hmono (d : ι →₀ ℕ) : d.prod (fun i n ↦ b i ^ n) ∈ S := by
    choose a ha using hpow
    rw [finsuppMonomial_eq_pow_mul_remainder p b d]
    have hc : (d.prod (fun i n ↦ b i ^ (n / p))) ^ p =
        algebraMap F K (d.prod (fun i n ↦ a i ^ (n / p))) := by
      simp only [Finsupp.prod, ← Finset.prod_pow, map_prod, map_pow]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_mul, Nat.mul_comm, pow_mul, ha]
    rw [hc]
    simpa only [Algebra.smul_def] using S.smul_mem (d.prod (fun i n ↦ a i ^ (n / p)))
      (Submodule.subset_span ⟨PExponent.remainder p d, rfl⟩)
  have hmul {x y : K} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨e, rfl⟩ := hy
        rw [pMonomial, pMonomial, ← Finsupp.prod_add_index'
          (by intro i; simp) (by intro i m n; exact pow_add _ _ _)]
        exact hmono (d.val + e.val)
      | zero => simp [S]
      | add y z _ _ hy hz => simpa [mul_add] using S.add_mem hy hz
      | smul c y _ hy => simpa [Algebra.smul_def, mul_left_comm] using S.smul_mem c hy
    | zero => simp [S]
    | add x z _ _ hx hz => simpa [add_mul] using S.add_mem hx hz
    | smul c x _ hx => simpa [Algebra.smul_def, mul_assoc] using S.smul_mem c hx
  let A : Subalgebra F K :=
    { carrier := S
      zero_mem' := S.zero_mem
      add_mem' := S.add_mem
      one_mem' := h1
      mul_mem' := hmul
      algebraMap_mem' := fun c ↦ by simpa [Algebra.smul_def] using S.smul_mem c h1 }
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact (Algebra.adjoin F (Set.range b)).prod_mem (fun i _ ↦
      (Algebra.adjoin F (Set.range b)).pow_mem (Algebra.subset_adjoin ⟨i, rfl⟩) _)
  · have hle : Algebra.adjoin F (Set.range b) ≤ A := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      change b i ∈ S
      have hi := hmono (Finsupp.single i 1)
      simpa using hi
    exact hle

omit [CharP K p] in
/-- 各生成元がp乗根なら、中間体としての添加も同じ単項式空間で表せる。 -/
theorem adjoin_toSubmodule_eq_span_pMonomial_of_pow_mem :
    (IntermediateField.adjoin F (Set.range b)).toSubalgebra.toSubmodule =
      Submodule.span F (Set.range (pMonomial (p := p) b)) := by
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic]
  · exact (span_pMonomial_eq_adjoin_of_pow_mem b hpow).symm
  · rintro _ ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := hpow i
    exact (isIntegral_of_prime_pow_eq (b i) a ha).isAlgebraic

end SerrePositivity
