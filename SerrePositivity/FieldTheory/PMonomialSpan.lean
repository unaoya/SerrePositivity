module

public import SerrePositivity.FieldTheory.PBasis
public import SerrePositivity.FieldTheory.PrimeRootAdjoin
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # p 単項式の線形包と添加

概要：体の拡大 `K/F` と族 `b : ι → K` で、各 `b i` の p 乗が `F` に属するとする。このとき
`F` 上の添加 `F[b] = F(b)` は、指数 `p` 未満の p 単項式の `F` 上の線形包に等しい。
`F` が p 乗部分体 `K^p` のときは仮定が自動的に成り立ち、`K^p(b)` が p 単項式で張られる。
方針：Mathlib の `Algebra.adjoin_eq_span` で添加を単項式の線形包として書き、各単項式を
指数の商と余りで `(p 乗の因子) • (p 単項式)` に分ける（`finsuppMonomial_eq_pow_mul_remainder`）。
中間体としての添加は、生成元が代数的なので部分代数としての添加と一致する。
規約：添字の有限性も族の独立性も仮定しない。
使われ方：p 基底の補中間体（`PBasisComplement`）、p 独立族の拡張（`PIndependentSet`）、
p 基底の微分（`PBasisDifferentials`）。
-/

@[expose] public section
namespace SerrePositivity

section Relative

variable {F K ι : Type*} [Field F] [Field K] [Algebra F K] {p : ℕ} (b : ι → K)
  (hpow : ∀ i, ∃ a : F, b i ^ p = algebraMap F K a)

include hpow

/-- 各生成元の p 乗が底体にあれば、p 単項式の線形包は生成部分代数に等しい。 -/
theorem span_pMonomial_eq_adjoin_of_pow_mem [NeZero p] :
    Submodule.span F (Set.range (pMonomial (p := p) b)) =
      (Algebra.adjoin F (Set.range b)).toSubmodule := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨d, rfl⟩
    exact Subalgebra.prod_mem _ fun i _ ↦
      Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _
  · rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    obtain ⟨d, rfl⟩ := Submonoid.exists_finsupp_of_mem_closure_range b x hx
    choose a ha using hpow
    rw [finsuppMonomial_eq_pow_mul_remainder p b d]
    have hc : (d.prod fun i n ↦ b i ^ (n / p)) ^ p =
        algebraMap F K (d.prod fun i n ↦ a i ^ (n / p)) := by
      simp only [Finsupp.prod, ← Finset.prod_pow, map_prod, map_pow]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [← pow_mul, Nat.mul_comm, pow_mul, ha]
    rw [hc, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- 各生成元の p 乗が底体にあれば、中間体としての添加も p 単項式の線形包。 -/
theorem adjoin_toSubmodule_eq_span_pMonomial_of_pow_mem [Fact p.Prime] :
    (IntermediateField.adjoin F (Set.range b)).toSubalgebra.toSubmodule =
      Submodule.span F (Set.range (pMonomial (p := p) b)) := by
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic,
    span_pMonomial_eq_adjoin_of_pow_mem b hpow]
  rintro _ ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := hpow i
  exact (isIntegral_of_prime_pow_eq (b i) a ha).isAlgebraic

end Relative

variable {K ι : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (b : ι → K)

/-- p 乗部分体上の添加は p 単項式の線形包。 -/
theorem adjoin_pPowerSubfield_toSubmodule_eq_span_pMonomial :
    (IntermediateField.adjoin (pPowerSubfield K p) (Set.range b)).toSubalgebra.toSubmodule =
      Submodule.span (pPowerSubfield K p) (Set.range (pMonomial (p := p) b)) :=
  adjoin_toSubmodule_eq_span_pMonomial_of_pow_mem (F := pPowerSubfield K p) b fun i ↦
    ⟨⟨b i ^ p, (mem_pPowerSubfield K p _).mpr ⟨b i, rfl⟩⟩, rfl⟩

theorem mem_adjoin_pPowerSubfield_iff_mem_span_pMonomial {x : K} :
    x ∈ IntermediateField.adjoin (pPowerSubfield K p) (Set.range b) ↔
      x ∈ Submodule.span (pPowerSubfield K p) (Set.range (pMonomial (p := p) b)) := by
  rw [← adjoin_pPowerSubfield_toSubmodule_eq_span_pMonomial]
  rfl

end SerrePositivity
