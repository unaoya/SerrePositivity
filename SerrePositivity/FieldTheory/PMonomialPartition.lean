module

public import SerrePositivity.FieldTheory.PMonomial
public import Mathlib.Logic.Equiv.Sum

/-! # 互いに素な部分族の単項式の合成

有限台の指数を直和で合成し、補集合の分割に沿って元の添字へ戻す。
指数の繰り上がりが起こらない、互いに素な方向の積を扱う。
-/

@[expose] public section
namespace SerrePositivity
namespace PExponent

/-- 直和の二つの成分の有限台指数を合成する。 -/
noncomputable def sumElim {p : ℕ} {ι κ : Type*}
    (d : PExponent p ι) (e : PExponent p κ) : PExponent p (ι ⊕ κ) :=
  ⟨d.val.sumElim e.val, by
    intro i
    cases i with
    | inl i => simpa using d.property i
    | inr i => simpa using e.property i⟩

theorem sumElim_injective {p : ℕ} {ι κ : Type*} :
    Function.Injective (fun z : PExponent p ι × PExponent p κ ↦ sumElim z.1 z.2) := by
  intro d e h
  apply Prod.ext
  · apply Subtype.ext
    ext i
    exact congrArg (fun z : PExponent p (ι ⊕ κ) ↦ z.val (Sum.inl i)) h
  · apply Subtype.ext
    ext i
    exact congrArg (fun z : PExponent p (ι ⊕ κ) ↦ z.val (Sum.inr i)) h

/-- 直和上の有限台p指数を二つの成分へ分ける同値。添字の有限性は不要。 -/
noncomputable def sumEquiv {p : ℕ} {ι κ : Type*} :
    PExponent p (ι ⊕ κ) ≃ PExponent p ι × PExponent p κ where
  toFun d :=
    (⟨(Finsupp.sumFinsuppEquivProdFinsupp d.val).1, fun i ↦ d.property (Sum.inl i)⟩,
      ⟨(Finsupp.sumFinsuppEquivProdFinsupp d.val).2, fun i ↦ d.property (Sum.inr i)⟩)
  invFun z := sumElim z.1 z.2
  left_inv d := by
    apply Subtype.ext
    ext i
    cases i <;> rfl
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext <;> ext i <;> rfl

/-- 補集合と元の集合の指数を、元の添字上の指数へ合成する。 -/
noncomputable def combinePartition {p : ℕ} [NeZero p] {ι : Type*} (s : Set ι)
    (z : PExponent p s × PExponent p {i // i ∉ s}) : PExponent p ι := by
  classical
  exact embDomain (Equiv.sumCompl (· ∈ s)).toEmbedding (sumElim z.1 z.2)

theorem combinePartition_injective {p : ℕ} [NeZero p] {ι : Type*} (s : Set ι) :
    Function.Injective (combinePartition (p := p) s) := by
  classical
  exact (embDomain_injective (Equiv.sumCompl (· ∈ s)).toEmbedding).comp sumElim_injective

end PExponent

theorem pMonomial_sumElim {p : ℕ} {ι κ K : Type*} [CommMonoid K]
    (b : ι ⊕ κ → K) (d : PExponent p ι) (e : PExponent p κ) :
    pMonomial b (PExponent.sumElim d e) =
      pMonomial (b ∘ Sum.inl) d * pMonomial (b ∘ Sum.inr) e :=
  Finsupp.prod_sumElim d.val e.val _

/-- 補集合の単項式と残した方向の単項式の積は、元の族の一つの単項式。 -/
theorem pMonomial_combinePartition {p : ℕ} [NeZero p] {ι K : Type*} [CommMonoid K]
    (b : ι → K) (s : Set ι)
    (z : PExponent p s × PExponent p {i // i ∉ s}) :
    pMonomial b (PExponent.combinePartition s z) =
      pMonomial (fun i : s ↦ b i) z.1 *
        pMonomial (fun i : {i // i ∉ s} ↦ b i) z.2 := by
  classical
  rw [PExponent.combinePartition, pMonomial_embDomain, pMonomial_sumElim]
  rfl

end SerrePositivity
