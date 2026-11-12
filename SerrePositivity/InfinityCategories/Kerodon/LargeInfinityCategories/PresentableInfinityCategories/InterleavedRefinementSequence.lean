module

public import Mathlib.Order.Monotone.Basic

/-!
概要：二つの上方共終な細分条件を、交互に増大する二列へ揃える。
方針：各条件の実拡大を選び、二段の拡大を自然数再帰で反復する。
規約：選択した拡大写像自体の単調性は要求しない。使われ方：二辺の相対細分の交互列。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 上方共終な二条件を満たす二列を、Lₙ ≤ Rₙ ≤ Lₙ₊₁ として同時に構成する。 -/
lemma exists_interleavedRefinementSequence
    {X : Type u} [Preorder X] (Q₀ Q₁ : X → Prop)
    (h₀ : ∀ x, ∃ y, x ≤ y ∧ Q₀ y) (h₁ : ∀ x, ∃ y, x ≤ y ∧ Q₁ y) (x : X) :
    ∃ L R : ℕ → X, Monotone L ∧ Monotone R ∧ x ≤ L 0 ∧
      ∀ n, Q₀ (L n) ∧ Q₁ (R n) ∧ L n ≤ R n ∧ R n ≤ L (n + 1) := by
  classical
  let f : X → X := fun x ↦ Classical.choose (h₀ x)
  let g : X → X := fun x ↦ Classical.choose (h₁ x)
  have hf (x : X) : x ≤ f x ∧ Q₀ (f x) := Classical.choose_spec (h₀ x)
  have hg (x : X) : x ≤ g x ∧ Q₁ (g x) := Classical.choose_spec (h₁ x)
  let L : ℕ → X := Nat.rec (f x) (fun _ a ↦ f (g a))
  let R : ℕ → X := fun n ↦ g (L n)
  have hLR (n : ℕ) : L n ≤ R n := (hg (L n)).1
  have hRL (n : ℕ) : R n ≤ L (n + 1) := (hf (g (L n))).1
  have hL : Monotone L := monotone_nat_of_le_succ (fun n ↦ (hLR n).trans (hRL n))
  have hR : Monotone R := monotone_nat_of_le_succ
    (fun n ↦ (hRL n).trans (hLR (n + 1)))
  refine ⟨L, R, hL, hR, (hf x).1, fun n ↦ ⟨?_, (hg (L n)).2, hLR n, hRL n⟩⟩
  cases n with
  | zero => exact (hf x).2
  | succ n => exact (hf (g (L n))).2

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
