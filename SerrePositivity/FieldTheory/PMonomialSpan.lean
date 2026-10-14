module

public import SerrePositivity.FieldTheory.PBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # p 単項式空間と中間体

指数の除法で積の繰り上がりを p 乗係数に移す。
逆元の閉性は `x⁻¹ = (x^p)⁻¹ * x^(p-1)` から従い、添字の有限性は不要。
-/

@[expose] public section
namespace SerrePositivity

namespace PExponent

/-- 有限台指数の各成分を p で割った余り。 -/
noncomputable def remainder {ι : Type*} (p : ℕ) [NeZero p] (d : ι →₀ ℕ) :
    PExponent p ι :=
  ⟨d.mapRange (fun n ↦ n % p) (Nat.zero_mod p),
    fun _ ↦ Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))⟩

end PExponent

/-- 任意の単項式を、p 乗の係数と指数 p 未満の単項式に分解する。 -/
theorem finsuppMonomial_eq_pow_mul_remainder
    {ι K : Type*} [CommMonoid K] (p : ℕ) [NeZero p] (b : ι → K) (d : ι →₀ ℕ) :
    d.prod (fun i n ↦ b i ^ n) =
      (d.prod (fun i n ↦ b i ^ (n / p))) ^ p *
        pMonomial b (PExponent.remainder p d) := by
  classical
  rw [pMonomial, PExponent.remainder,
    Finsupp.prod_mapRange_index (by intro i; simp)]
  simp only [Finsupp.prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← pow_mul,
    ← pow_add, Nat.div_add_mod']

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable {ι : Type*} (b : ι → K)

/-- p 乗部分体上の p 単項式の線形包。 -/
def pMonomialSpan : Submodule (pPowerSubfield K p) K :=
  Submodule.span (pPowerSubfield K p) (Set.range (pMonomial (p := p) b))

theorem one_mem_pMonomialSpan : (1 : K) ∈ pMonomialSpan (p := p) b :=
  Submodule.subset_span ⟨0, pMonomial_zero b⟩

/-- 一般の有限台単項式も同じ空間に属する。 -/
theorem finsuppMonomial_mem_pMonomialSpan (d : ι →₀ ℕ) :
    d.prod (fun i n ↦ b i ^ n) ∈ pMonomialSpan (p := p) b := by
  rw [finsuppMonomial_eq_pow_mul_remainder p b d]
  let c : pPowerSubfield K p :=
    ⟨(d.prod (fun i n ↦ b i ^ (n / p))) ^ p,
      (mem_pPowerSubfield K p _).mpr ⟨_, rfl⟩⟩
  exact (pMonomialSpan (p := p) b).smul_mem c
    (Submodule.subset_span ⟨PExponent.remainder p d, rfl⟩)

theorem pMonomial_mul_mem_span (d e : PExponent p ι) :
    pMonomial b d * pMonomial b e ∈ pMonomialSpan (p := p) b := by
  rw [pMonomial, pMonomial,
    ← Finsupp.prod_add_index' (by intro i; simp) (by intro i m n; exact pow_add _ _ _)]
  exact finsuppMonomial_mem_pMonomialSpan b (d.val + e.val)

/-- p 単項式空間は積で閉じる。 -/
theorem mul_mem_pMonomialSpan {x y : K}
    (hx : x ∈ pMonomialSpan (p := p) b) (hy : y ∈ pMonomialSpan (p := p) b) :
    x * y ∈ pMonomialSpan (p := p) b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, rfl⟩ := hy
      exact pMonomial_mul_mem_span b d e
    | zero => simp
    | add y z _ _ hy hz => simpa [mul_add] using (pMonomialSpan b).add_mem hy hz
    | smul c y _ hy =>
      simpa [Algebra.smul_def, mul_left_comm] using (pMonomialSpan b).smul_mem c hy
  | zero => simp
  | add x z _ _ hx hz => simpa [add_mul] using (pMonomialSpan b).add_mem hx hz
  | smul c x _ hx =>
    simpa [Algebra.smul_def, mul_assoc] using (pMonomialSpan b).smul_mem c hx

/-- 単項式空間を部分代数として実現する。 -/
def pMonomialSubalgebra : Subalgebra (pPowerSubfield K p) K where
  carrier := pMonomialSpan (p := p) b
  zero_mem' := (pMonomialSpan (p := p) b).zero_mem
  add_mem' := (pMonomialSpan (p := p) b).add_mem
  one_mem' := one_mem_pMonomialSpan (p := p) b
  mul_mem' := mul_mem_pMonomialSpan (p := p) b
  algebraMap_mem' c := by
    change (c : K) ∈ pMonomialSpan (p := p) b
    have h := (pMonomialSpan (p := p) b).smul_mem c (one_mem_pMonomialSpan b)
    change (c : K) * 1 ∈ _ at h
    simpa using h

/-- 任意の部分族の単項式空間は逆元で閉じる。 -/
theorem inv_mem_pMonomialSpan {x : K} (hx : x ∈ pMonomialSpan (p := p) b) :
    x⁻¹ ∈ pMonomialSpan (p := p) b := by
  by_cases hx0 : x = 0
  · simp [hx0, pMonomialSpan]
  have hpow : x ^ (p - 1) ∈ pMonomialSpan (p := p) b :=
    (pMonomialSubalgebra b).pow_mem hx _
  let c : pPowerSubfield K p :=
    ⟨(x⁻¹) ^ p, (mem_pPowerSubfield K p _).mpr ⟨x⁻¹, rfl⟩⟩
  have h := (pMonomialSpan b).smul_mem c hpow
  change (x⁻¹) ^ p * x ^ (p - 1) ∈ _ at h
  have heq : (x⁻¹) ^ p * x ^ (p - 1) = x⁻¹ := by
    rw [inv_pow, pow_sub₀ x hx0 (Fact.out : p.Prime).one_le, pow_one]
    field_simp
  rwa [heq] at h

/-- p 単項式空間を中間体として実現する。有限性・独立性の仮定は不要。 -/
def pMonomialIntermediateField : IntermediateField (pPowerSubfield K p) K :=
  (pMonomialSubalgebra (p := p) b).toIntermediateField
    (fun _ hx ↦ inv_mem_pMonomialSpan b hx)

/-- 単項式空間として構成した中間体は、指定族を添加した中間体そのもの。 -/
theorem pMonomialIntermediateField_eq_adjoin :
    pMonomialIntermediateField (p := p) b =
      IntermediateField.adjoin (pPowerSubfield K p) (Set.range b) := by
  classical
  let A := IntermediateField.adjoin (pPowerSubfield K p) (Set.range b)
  apply le_antisymm
  · have hle : pMonomialSpan (p := p) b ≤ A.toSubalgebra.toSubmodule := by
      apply Submodule.span_le.mpr
      rintro _ ⟨d, rfl⟩
      apply A.prod_mem
      intro i _
      exact A.toSubalgebra.pow_mem
        (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)) (d.val i)
    exact hle
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    change b i ∈ pMonomialSpan (p := p) b
    let n : Fin p := ⟨1, (Fact.out : p.Prime).one_lt⟩
    have heq : pMonomial b (PExponent.single i n) = b i := by simp [n]
    rw [← heq]
    exact Submodule.subset_span (Set.mem_range_self _)

/-- 有限な独立族が生成する中間体の次数を、実際の単項式空間から計算する。 -/
theorem finrank_pMonomialIntermediateField [Fintype ι]
    (hb : LinearIndependent (pPowerSubfield K p) (pMonomial (p := p) b)) :
    Module.finrank (pPowerSubfield K p) (pMonomialIntermediateField (p := p) b) =
      p ^ Fintype.card ι := by
  change Module.finrank (pPowerSubfield K p) (pMonomialSpan (p := p) b) = _
  exact finrank_span_pMonomial hb

/-- p-basis の任意の有限部分が生成する中間体の次数。 -/
theorem IsPBasis.finrank_adjoin_comp {κ : Type*} [Fintype κ]
    (hb : IsPBasis K p b) (e : κ ↪ ι) :
    Module.finrank (pPowerSubfield K p)
      (IntermediateField.adjoin (pPowerSubfield K p) (Set.range (b ∘ e))) =
        p ^ Fintype.card κ := by
  rw [← pMonomialIntermediateField_eq_adjoin]
  exact finrank_pMonomialIntermediateField _ (hb.linearIndependent_comp e)

/-- 有限族の生成する中間体は有限拡大。独立性を仮定しない。 -/
theorem finite_pMonomialIntermediateField [Finite ι] :
    Module.Finite (pPowerSubfield K p) (pMonomialIntermediateField (p := p) b) := by
  classical
  let := Fintype.ofFinite ι
  change Module.Finite (pPowerSubfield K p) (pMonomialSpan (p := p) b)
  exact Module.Finite.span_of_finite _ (Set.finite_range _)

end SerrePositivity
