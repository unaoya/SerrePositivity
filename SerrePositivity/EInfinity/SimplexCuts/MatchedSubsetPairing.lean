module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Sum.Basic
public import Mathlib.Algebra.Group.Basic

/-!
# 部分集合と対応する項だけを交換する有限対合

Berger–Fresse §2.2.6、M14 L12a、報告 §371。
指定した同値と逆だけを使い、対応しない右の零項を固定点として残す。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.EInfinity.SimplexCuts
variable {α : Type u} {β : Type v}

/-- 指定された部分集合の同値と逆を交換し、残る右の添字を固定する（BF §2.2.6）。 -/
def matchedSubsetExchange (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) :
    α ⊕ β → α ⊕ β
  | Sum.inl a => Sum.inr (e a).val
  | Sum.inr b => if h : P b then Sum.inl (e.symm ⟨b, h⟩) else Sum.inr b

/-- 同じ同値の両逆によって二回の交換は恒等（BF §2.2.6）。 -/
lemma matchedSubsetExchange_involutive (P : β → Prop) [DecidablePred P]
    (e : α ≃ {b // P b}) : Function.Involutive (matchedSubsetExchange P e) := by
  rintro (a | b)
  · simp [matchedSubsetExchange, (e a).property]
  · by_cases hb : P b <;> simp [matchedSubsetExchange, hb]

/-- 元の交換関数を同じ有限添字の自己同値として読む（BF §2.2.6）。 -/
def matchedSubsetPerm (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) :
    Equiv.Perm (α ⊕ β) where
  toFun := matchedSubsetExchange P e
  invFun := matchedSubsetExchange P e
  left_inv := matchedSubsetExchange_involutive P e
  right_inv := matchedSubsetExchange_involutive P e

/-- 元の左項と、負号付きの元の右項（BF §2.2.6）。 -/
def matchedSubsetBalanceTerm {M : Type w} [AddCommGroup M] (F : α → M) (G : β → M) :
    α ⊕ β → M
  | Sum.inl a => F a
  | Sum.inr b => -G b

/-- 対応しない右の零項は、元の有限対合の固定零項になる（BF §2.2.6）。 -/
lemma matchedSubsetPerm_fixed_zero {M : Type w} [AddCommGroup M]
    (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) (F : α → M) (G : β → M)
    (hzero : ∀ b, ¬P b → G b = 0) (i : α ⊕ β) (hi : matchedSubsetPerm P e i = i) :
    matchedSubsetBalanceTerm F G i = 0 := by
  cases i with
  | inl a =>
    change Sum.inr (e a).val = Sum.inl a at hi
    cases hi
  | inr b =>
    by_cases hb : P b
    · change (if h : P b then Sum.inl (e.symm ⟨b, h⟩) else Sum.inr b) = Sum.inr b at hi
      rw [dite_eq_left hb] at hi
      cases hi
    · change -G b = 0
      rw [hzero b hb, neg_zero]

/-- 対応する同じ実項は符号で相殺し、固定された零項も保持する（BF §2.2.6）。 -/
lemma matchedSubsetPerm_term_neg {M : Type w} [AddCommGroup M]
    (P : β → Prop) [DecidablePred P] (e : α ≃ {b // P b}) (F : α → M) (G : β → M)
    (hpair : ∀ a, F a = G (e a).val) (hzero : ∀ b, ¬P b → G b = 0) (i : α ⊕ β) :
    matchedSubsetBalanceTerm F G (matchedSubsetPerm P e i) =
      -matchedSubsetBalanceTerm F G i := by
  cases i with
  | inl a =>
    change -G (e a).val = -F a
    rw [hpair a]
  | inr b =>
    by_cases hb : P b
    · change matchedSubsetBalanceTerm F G
        (if h : P b then Sum.inl (e.symm ⟨b, h⟩) else Sum.inr b) = -(-G b)
      rw [dite_eq_left hb]
      change F (e.symm ⟨b, hb⟩) = -(-G b)
      rw [neg_neg, hpair]
      exact congrArg (fun b => G b.val) (e.apply_symm_apply ⟨b, hb⟩)
    · change matchedSubsetBalanceTerm F G
        (if h : P b then Sum.inl (e.symm ⟨b, h⟩) else Sum.inr b) = -(-G b)
      rw [dite_eq_right hb]
      change -G b = -(-G b)
      rw [hzero b hb, neg_zero, neg_zero]

end SerrePositivity.EInfinity.SimplexCuts
