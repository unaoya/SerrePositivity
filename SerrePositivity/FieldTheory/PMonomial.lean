module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finsupp.Option

/-! # 有限台の p 単項式

添字集合は有限と仮定しない。各指数が p 未満の有限台関数を用いる。
単項式自体は標数の仮定なしで定義し、p-basis の基礎として再利用する。
-/

@[expose] public section
namespace SerrePositivity

/-- 各成分が `p` 未満の有限台指数。 -/
abbrev PExponent (p : ℕ) (ι : Type*) := {d : ι →₀ ℕ // ∀ i, d i < p}

namespace PExponent

variable {p : ℕ} {ι κ : Type*}

instance [NeZero p] : Zero (PExponent p ι) :=
  ⟨⟨0, fun _ ↦ Nat.pos_of_ne_zero (NeZero.ne p)⟩⟩

/-- 添字の埋め込みに沿って指数を零で延長する。 -/
noncomputable def embDomain [NeZero p] (e : ι ↪ κ) (d : PExponent p ι) :
    PExponent p κ := by
  classical
  refine ⟨d.val.embDomain e, fun i ↦ ?_⟩
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    simpa using d.property j
  · rw [Finsupp.embDomain_of_notMem_range e d.val i hi]
    exact Nat.pos_of_ne_zero (NeZero.ne p)

theorem embDomain_injective [NeZero p] (e : ι ↪ κ) :
    Function.Injective (embDomain (p := p) e) := by
  intro d d' h
  apply Subtype.ext
  exact Finsupp.embDomain_injective e (congrArg Subtype.val h)

/-- 有限添字に限れば、有限台指数は `Fin p` 値の関数と同じ。 -/
noncomputable def equivFin [Finite ι] : PExponent p ι ≃ (ι → Fin p) where
  toFun d i := ⟨d.val i, d.property i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (f i).val), fun i ↦ (f i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rfl
  right_inv f := by
    funext i
    rfl

noncomputable instance [Fintype ι] : Fintype (PExponent p ι) := by
  classical
  exact Fintype.ofEquiv (ι → Fin p) equivFin.symm

theorem card [Fintype ι] : Fintype.card (PExponent p ι) = p ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr equivFin]
  simp

/-- 一つの変数だけに指定指数を置く。 -/
noncomputable def single (i : ι) (n : Fin p) : PExponent p ι := by
  classical
  refine ⟨Finsupp.single i n.val, fun j ↦ ?_⟩
  by_cases h : i = j
  · subst j
    simp
  · simpa [Finsupp.single_apply, h, Ne.symm h] using Nat.zero_lt_of_lt n.isLt

/-- 新しい一つの添字の指数と、既存添字の指数を分ける。 -/
noncomputable def splitOption (d : PExponent p (Option ι)) : PExponent p ι × Fin p :=
  (⟨d.val.some, fun i ↦ d.property (some i)⟩, ⟨d.val none, d.property none⟩)

theorem splitOption_injective : Function.Injective (splitOption (p := p) (ι := ι)) := by
  intro d e h
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  cases i with
  | none => exact congrArg (fun z : PExponent p ι × Fin p ↦ z.2.val) h
  | some i => exact congrArg (fun z : PExponent p ι × Fin p ↦ z.1.val i) h

end PExponent

/-- 族 `b` の有限台 p 単項式。 -/
noncomputable def pMonomial {p : ℕ} {ι K : Type*} [CommMonoid K]
    (b : ι → K) (d : PExponent p ι) : K :=
  d.val.prod (fun i n ↦ b i ^ n)

@[simp] theorem pMonomial_zero {p : ℕ} {ι K : Type*} [NeZero p] [CommMonoid K]
    (b : ι → K) : pMonomial b (0 : PExponent p ι) = 1 := by
  change (0 : ι →₀ ℕ).prod (fun i n ↦ b i ^ n) = 1
  simp

@[simp] theorem pMonomial_single {p : ℕ} {ι K : Type*} [CommMonoid K]
    (b : ι → K) (i : ι) (n : Fin p) :
    pMonomial b (PExponent.single i n) = b i ^ n.val := by
  exact Finsupp.prod_single_index (pow_zero _)

/-- 部分族の単項式は、指数を零で延長した元の族の単項式に一致する。 -/
theorem pMonomial_embDomain {p : ℕ} {ι κ K : Type*} [NeZero p] [CommMonoid K]
    (b : κ → K) (e : ι ↪ κ) (d : PExponent p ι) :
    pMonomial b (PExponent.embDomain e d) = pMonomial (b ∘ e) d := by
  exact Finsupp.prod_embDomain

/-- 一つの元を添加した族の単項式を、既存の単項式と新しい元の冪に分解する。 -/
theorem pMonomial_optionElim {p : ℕ} {ι K : Type*} [CommMonoid K]
    (b : ι → K) (x : K) (d : PExponent p (Option ι)) :
    pMonomial (Option.elim' x b) d =
      pMonomial b (PExponent.splitOption d).1 * x ^ (PExponent.splitOption d).2.val := by
  rw [pMonomial, Finsupp.prod_option_index _ _ (by intro i; simp)
    (by intro i m n; exact pow_add _ _ _)]
  exact mul_comm _ _

/-- p 単項式の独立性は任意の部分族へ制限できる。 -/
theorem linearIndependent_pMonomial_comp
    {p : ℕ} {ι κ F K : Type*} [NeZero p] [Field F] [Field K] [Algebra F K]
    {b : κ → K} (hb : LinearIndependent F (pMonomial (p := p) b)) (e : ι ↪ κ) :
    LinearIndependent F (pMonomial (p := p) (b ∘ e)) := by
  have h := hb.comp (PExponent.embDomain e) (PExponent.embDomain_injective e)
  simpa only [Function.comp_def, pMonomial_embDomain] using h

/-- 有限族の独立な p 単項式が張る空間の次元は `p ^ |ι|`。 -/
theorem finrank_span_pMonomial
    {p : ℕ} {ι F K : Type*} [Fintype ι] [Field F] [Field K] [Algebra F K]
    {b : ι → K} (hb : LinearIndependent F (pMonomial (p := p) b)) :
    Module.finrank F (Submodule.span F (Set.range (pMonomial (p := p) b))) =
      p ^ Fintype.card ι := by
  rw [finrank_span_eq_card hb, PExponent.card]

end SerrePositivity
