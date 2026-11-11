module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
概要：有限半順序集合の任意の下方閉部分を固定し、その外の極大点を除去して帰納する。
方針：補集合の極大点は元の全体でも極大であり、除去部分の濃度は厳密に小さい。
規約：固定部分を全体とする基底と、元の極大点を明示した段階を使う。
使われ方：Ind の指定下方余錐を保つ有限半順序図式の延長帰納。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
/-- 概要：真の下方閉部分の外には、元の全体の極大点がある。
方針：有限補集合の極大性を全体へ戻す。規約：元の点。使われ方：固定部分の外の除去。 -/
lemma finitePoset_exists_isMax_outside_lowerSet {P : Type u} [PartialOrder P] [Finite P]
    (U : Set P) (hU : IsLowerSet U) (h : ∃ p, p ∉ U) :
    ∃ a : P, a ∉ U ∧ IsMax a := by
  obtain ⟨a, ha, hmax⟩ := (Set.toFinite Uᶜ).exists_maximal h
  refine ⟨a, ha, ?_⟩
  intro b hab
  have hb : b ∉ U := fun hb ↦ ha (hU hab hb)
  exact hmax hb hab
/-- 概要：下方閉部分を固定する性質は、その外の極大点除去により有限半順序帰納できる。
方針：元の全体の有限濃度で強帰納。規約：元の部分を逆像で保持。
使われ方：指定余錐の厳密な持ち上げと点追加の帰納。 -/
lemma finitePoset_lowerSet_induction
    (Q : ∀ (P : Type u) [PartialOrder P] [Finite P], Set P → Prop)
    (base : ∀ (P : Type u) [PartialOrder P] [Finite P] (U : Set P),
      IsLowerSet U → (∀ p, p ∈ U) → Q P U)
    (step : ∀ (P : Type u) [PartialOrder P] [Finite P] (U : Set P),
      IsLowerSet U → ∀ a : P, a ∉ U → IsMax a →
      Q {p : P // p ≠ a} (Subtype.val ⁻¹' U) → Q P U) :
    ∀ (P : Type u) [PartialOrder P] [Finite P] (U : Set P), IsLowerSet U → Q P U := by
  suffices ∀ n : ℕ, ∀ (P : Type u) [PartialOrder P] [Finite P],
      Nat.card P = n → ∀ (U : Set P), IsLowerSet U → Q P U by
    intro P _ _ U hU
    exact this (Nat.card P) P rfl U hU
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P _ _ hcard U hU
    by_cases hfull : ∀ p, p ∈ U
    · exact base P U hU hfull
    obtain ⟨a, ha, hmax⟩ := finitePoset_exists_isMax_outside_lowerSet U hU
      (not_forall.mp hfull)
    apply step P U hU a ha hmax
    have hlt : Nat.card {p : P // p ≠ a} < n := by
      rw [← hcard]
      exact Finite.card_subtype_lt (x := a) (by simp)
    apply ih (Nat.card {p : P // p ≠ a}) hlt {p : P // p ≠ a} rfl
    intro x y hxy hy
    exact hU hxy hy
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
