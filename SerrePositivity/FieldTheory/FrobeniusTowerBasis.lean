module

public import SerrePositivity.FieldTheory.FrobeniusLayerBasis

/-! # 高い Frobenius 冪上の単項式基底

有限台の p 進の桁を添字とし、各段階の基底を `Basis.smulTower` で合成する。
桁数は有限だが、p-basis 自体の添字集合は有限と仮定しない。
-/

@[expose] public section
namespace SerrePositivity

universe u

/-- 高い冪から低い冪へ並べた、有限台指数の p 進の桁。 -/
abbrev FrobeniusDigits (p : ℕ) (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => PExponent p ι × FrobeniusDigits p ι n

noncomputable instance FrobeniusDigits.fintype (p : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) :
    Fintype (FrobeniusDigits p ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (PExponent p ι × FrobeniusDigits p ι n))

theorem FrobeniusDigits.card (p : ℕ) (ι : Type*) [Fintype ι] (n : ℕ) :
    Fintype.card (FrobeniusDigits p ι n) = (p ^ Fintype.card ι) ^ n := by
  induction n with
  | zero => simp [FrobeniusDigits]
  | succ n ih =>
    change Fintype.card (PExponent p ι × FrobeniusDigits p ι n) = _
    rw [Fintype.card_prod, PExponent.card, ih, pow_succ, Nat.mul_comm]

/-- 桁で表した単項式。0 桁では空積。 -/
noncomputable def frobeniusDigitMonomial {p : ℕ} {ι k : Type*} [CommMonoid k]
    (b : ι → k) : (n : ℕ) → FrobeniusDigits p ι n → k
  | 0, _ => 1
  | n + 1, d => (pMonomial b d.1) ^ p ^ n * frobeniusDigitMonomial b n d.2

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {ι : Type*} {b : ι → k}

/-- k 自身と 0 回目の Frobenius 部分体との基底の同定。 -/
theorem exists_frobeniusZeroBasis :
    ∃ B : Module.Basis PUnit (frobeniusPowerSubfield k p 0) k, ∀ i, B i = 1 := by
  have h : ∀ (c : k) (x : k), frobeniusPowerEquiv k p 0 c • x = c • x := by
    intro c x
    simp only [Algebra.smul_def]
    change c ^ p ^ 0 * x = c * x
    simp
  exact ⟨(Module.Basis.singleton PUnit k).mapCoeffs (frobeniusPowerEquiv k p 0) h,
    fun i ↦ by simp⟩

/-- 任意の n に対する k/k^{p^n} の実際の基底。 -/
noncomputable def IsPBasis.frobeniusTowerBasis (hb : IsPBasis k p b) :
    (n : ℕ) → Module.Basis (FrobeniusDigits p ι n) (frobeniusPowerSubfield k p n) k
  | 0 => exists_frobeniusZeroBasis.choose
  | n + 1 => (hb.frobeniusLayerBasis n).smulTower (hb.frobeniusTowerBasis n)

@[simp] theorem IsPBasis.frobeniusTowerBasis_apply (hb : IsPBasis k p b) (n : ℕ)
    (d : FrobeniusDigits p ι n) :
    hb.frobeniusTowerBasis n d = frobeniusDigitMonomial b n d := by
  induction n with
  | zero => exact exists_frobeniusZeroBasis.choose_spec d
  | succ n ih =>
    rw [IsPBasis.frobeniusTowerBasis, Module.Basis.smulTower_apply,
      hb.frobeniusLayerBasis_apply, ih]
    simp only [Algebra.smul_def]
    rfl

/-- 高い冪上の単項式の独立性。生成性だけから推論したものではない。 -/
theorem IsPBasis.linearIndependent_frobeniusDigitMonomial (hb : IsPBasis k p b) (n : ℕ) :
    LinearIndependent (frobeniusPowerSubfield k p n)
      (frobeniusDigitMonomial (p := p) b n) := by
  have h : (hb.frobeniusTowerBasis n : FrobeniusDigits p ι n → k) =
      frobeniusDigitMonomial (p := p) b n := funext (hb.frobeniusTowerBasis_apply n)
  exact h ▸ (hb.frobeniusTowerBasis n).linearIndependent

theorem IsPBasis.span_frobeniusDigitMonomial (hb : IsPBasis k p b) (n : ℕ) :
    Submodule.span (frobeniusPowerSubfield k p n)
      (Set.range (frobeniusDigitMonomial (p := p) b n)) = ⊤ := by
  have h : (hb.frobeniusTowerBasis n : FrobeniusDigits p ι n → k) =
      frobeniusDigitMonomial (p := p) b n := funext (hb.frobeniusTowerBasis_apply n)
  exact h ▸ (hb.frobeniusTowerBasis n).span_eq

/-- 高い冪上でも、任意の元は有限台の係数で一意に展開できる。 -/
theorem IsPBasis.existsUnique_frobeniusExpansion (hb : IsPBasis k p b) (n : ℕ) (x : k) :
    ∃! c : FrobeniusDigits p ι n →₀ frobeniusPowerSubfield k p n,
      c.sum (fun d a ↦ (a : k) * frobeniusDigitMonomial b n d) = x := by
  let B := hb.frobeniusTowerBasis n
  have hsum : ∀ c : FrobeniusDigits p ι n →₀ frobeniusPowerSubfield k p n,
      c.sum (fun d a ↦ (a : k) * frobeniusDigitMonomial b n d) = B.repr.symm c := by
    intro c
    rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    apply Finsupp.sum_congr
    intro d _
    simp only [B, hb.frobeniusTowerBasis_apply, Algebra.smul_def]
    rfl
  refine ⟨B.repr x, ?_, ?_⟩
  · exact (hsum _).trans (B.repr.symm_apply_apply x)
  · intro c hc
    apply B.repr.symm.injective
    rw [← hsum, hc, B.repr.symm_apply_apply]

/-- 有限 p-basis の場合に限り、拡大次数も計算する。 -/
theorem IsPBasis.finrank_frobeniusPowerSubfield [Fintype ι]
    (hb : IsPBasis k p b) (n : ℕ) :
    Module.finrank (frobeniusPowerSubfield k p n) k = p ^ (n * Fintype.card ι) := by
  rw [Module.finrank_eq_card_basis (hb.frobeniusTowerBasis n), FrobeniusDigits.card,
    ← pow_mul, Nat.mul_comm]

end SerrePositivity
