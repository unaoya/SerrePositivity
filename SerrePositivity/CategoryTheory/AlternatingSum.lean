module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Int.Interval

/-! # Euler 評価に共通する交代和の添字変換

環や複体に依存しない、整数添字の平行移動と自然数添字への取り直し。
有限支持でない場合も `finsum` の規約と両立する。
-/

@[expose] public section

namespace SerrePositivity

/-- Alternating sums in any abelian group change sign under an index shift. -/
lemma alternatingGroupFinsum_sub_one {A : Type*} [AddCommGroup A] (f : ℤ → A) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) • f (i - 1)) =
      -(∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) • f i) := by
  calc
    _ = ∑ᶠ i : ℤ, (((i + 1).negOnePow : ℤˣ) : ℤ) • f i := by
      have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ) • f (i - 1))
      simpa using h.symm
    _ = ∑ᶠ i : ℤ, -(((i.negOnePow : ℤˣ) : ℤ) • f i) := by
      congr 1
      funext i
      simp [Int.negOnePow_add]
    _ = _ := finsum_neg_distrib _

/-- Cancellation of the connecting images in a group-valued exact Euler sequence. -/
lemma alternatingGroupFinsum_exact {A : Type*} [AddCommGroup A] (a b d : ℤ → A)
    (ha : Function.HasFiniteSupport a) (hb : Function.HasFiniteSupport b)
    (hd : Function.HasFiniteSupport d) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) • (a i + b i)) =
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) • (d (i - 1) + a i)) +
      ∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) • (b i + d i) := by
  have haw : Function.HasFiniteSupport
      (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ) • a i) :=
    Function.HasFiniteSupport.smul_right (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ)) ha
  have hbw : Function.HasFiniteSupport
      (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ) • b i) :=
    Function.HasFiniteSupport.smul_right (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ)) hb
  have hdw : Function.HasFiniteSupport
      (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ) • d i) :=
    Function.HasFiniteSupport.smul_right (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ)) hd
  have hds : Function.HasFiniteSupport
      (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ) • d (i - 1)) :=
    Function.HasFiniteSupport.smul_right (fun i : ℤ => ((i.negOnePow : ℤˣ) : ℤ))
      (hd.preimage (Equiv.subRight (1 : ℤ)).injective.injOn)
  simp_rw [smul_add]
  rw [finsum_add_distrib haw hbw, finsum_add_distrib hds haw,
    finsum_add_distrib hbw hdw, alternatingGroupFinsum_sub_one]
  abel

/-- 整数添字の交代和を一つずらすと符号が反転する。 -/
lemma alternatingFinsum_sub_one (f : ℤ → ℝ) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f (i - 1)) =
      -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f i) := by
  simpa only [zsmul_eq_mul] using alternatingGroupFinsum_sub_one f

/-- 整数添字の交代和を正方向へ一つずらすと符号が反転する。 -/
lemma alternatingFinsum_add_one (f : ℤ → ℝ) :
    (∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * f (q + 1)) =
      -(∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * f q) := by
  have h := alternatingFinsum_sub_one (fun i => f (i + 1))
  simpa using (congrArg Neg.neg h).symm

/-- 正の添字で `0` になる実数列 `a : ℤ → ℝ` について、交代和 `Σ_{i ∈ ℤ} (-1)^i a_i` は
`Σ_{n ∈ ℕ} (-1)^n a_{-n}` に等しい。`finsum` の台が `{-n}` に含まれることと、単射 `n ↦ -n` に沿った
`finsum` の取り直し（`finsum_mem_range`）による。有限台を仮定せず、`finsum` の規約による値も含めて
成り立つ。 -/
lemma alternating_finsum_eq_nat (a : ℤ → ℝ) (hpos : ∀ i, 0 < i → a i = 0) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) =
      ∑ᶠ n : ℕ, (-1 : ℝ) ^ n * a (-(n : ℤ)) := by
  let f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * a i
  let g := fun i : ℕ ↦ -(i : ℤ)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    exact_mod_cast neg_injective hij
  have hs : Function.support f ⊆ Set.range g := by
    intro i hi
    have hnonpos : i ≤ 0 := by
      by_contra hn
      exact hi (by simp [f, hpos i (by omega)])
    refine ⟨(-i).toNat, ?_⟩
    dsimp [g]
    rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hfull : (∑ᶠ i ∈ Set.range g, f i) = ∑ᶠ i : ℤ, f i := by
    rw [← finsum_mem_inter_support f (Set.range g), Set.inter_eq_right.mpr hs,
      finsum_mem_support]
  change (∑ᶠ i : ℤ, f i) = _
  rw [← hfull, finsum_mem_range hg]
  simp only [f, g, Int.negOnePow_neg, Int.cast_negOnePow_natCast]

/-- 境界の寄与をもつ有限台の係数恒等式の Euler 相殺。
対象の圏・通常長さ・有限長性とは独立に、隣接する境界を相殺する。 -/
lemma alternatingFinsum_eq_of_boundary (terms homology boundary : ℤ → ℝ)
    (hb : Function.HasFiniteSupport boundary) (hh : Function.HasFiniteSupport homology)
    (he : ∀ q, terms q = boundary (q - 1) + homology q + boundary q) :
    (∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * homology q) =
      ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * terms q := by
  have hbp : Function.HasFiniteSupport (fun q : ℤ ↦ boundary (q - 1)) :=
    hb.preimage (Equiv.subRight (1 : ℤ)).injective.injOn
  have hbw : Function.HasFiniteSupport
      (fun q : ℤ ↦ ((q.negOnePow : ℤ) : ℝ) * boundary q) := hb.mul_right _
  have hbpw : Function.HasFiniteSupport
      (fun q : ℤ ↦ ((q.negOnePow : ℤ) : ℝ) * boundary (q - 1)) := hbp.mul_right _
  have hhw : Function.HasFiniteSupport
      (fun q : ℤ ↦ ((q.negOnePow : ℤ) : ℝ) * homology q) := hh.mul_right _
  symm
  calc
    _ = ((∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * boundary (q - 1)) +
        ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * homology q) +
        ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * boundary q := by
      simp_rw [he, mul_add]
      have hfirst := finsum_add_distrib (hbpw.add hhw) hbw
      simp only [Pi.add_apply] at hfirst
      rw [hfirst, finsum_add_distrib hbpw hhw]
    _ = _ := by rw [alternatingFinsum_sub_one]; ring

/-- 像に分解された自然数添字の完全列の有限区間 Euler 公式。
終端の連結像だけが零であればよく、区間より上の全消滅は要求しない。 -/
lemma alternatingSum_range_exact (A B C a b d : ℕ → ℤ)
    (eA : ∀ i, A i = d i + a i) (eB : ∀ i, B i = a i + b i)
    (eC : ∀ i, C (i + 1) = b (i + 1) + d i) (eC0 : C 0 = b 0)
    (n : ℕ) (hd : d n = 0) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * B i) =
      (∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * A i) +
      (∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * C i) := by
  have hsum : ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * B i) -
      (∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * A i) -
      (∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * C i) =
      -((-1 : ℤ)^k * d k) := by
    intro k
    induction k with
    | zero => simp [eA, eB, eC0]; ring
    | succ k ih =>
      simp only [Finset.sum_range_succ (n := k + 1)]
      rw [eA (k + 1), eB (k + 1), eC k, pow_succ]
      linear_combination ih
  have h := hsum n
  rw [hd, mul_zero, neg_zero] at h
  linarith

end SerrePositivity
