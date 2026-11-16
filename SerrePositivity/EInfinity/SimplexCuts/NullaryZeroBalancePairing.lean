module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroBalanceValues

/-!
# 元の零出力の全分割と全Cutの対合

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §378。
全入力次数で同じ唯一Cutを指定して左右を交換する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 全空語分割と空Cutを同じ元のcard=0で同一視する（BF §2.2.6）。 -/
def nullaryZeroCutEquiv (u : Surjection.BasisWord 1 0) (k : Fin 1) (q : ℕ) :
    (Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit.{1}) ≃ Cut 0 q := by
  have hc : Surjection.occurrenceCount u.val k = 1 := by
    have hu : u.val = fun _ => k := funext (fun _ => Subsingleton.elim _ _)
    simp [Surjection.occurrenceCount, hu, List.ofFn_succ]
  let ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 :=
    Eq.mp (congrArg (fun c => Surjection.OverlapPartition c 0) hc.symm)
      (Surjection.OverlapPartition.single 0)
  exact
    { toFun := fun _ => ⟨∅, rfl⟩
      invFun := fun _ => (ρ, PUnit.unit)
      left_inv := fun c => Prod.ext
        ((overlap_eq_single_of_count_one hc ρ).trans
          (overlap_eq_single_of_count_one hc c.1).symm) (Subsingleton.elim _ _)
      right_inv := fun s => Subtype.ext (Finset.card_eq_zero.mp s.property).symm }

/-- 元の空作用の項と負の二段Cut項（BF §2.2.6）。 -/
def nullaryZeroBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) (q : ℕ)
    (i : NullaryZeroBalanceIndex u k q) (x : S _⦋q⦌) : (power (chains A S) 0).X (-(q : ℤ)) :=
  matchedSubsetBalanceTerm (fun c => nullaryZeroCompositeTerm A S u ν k c x)
    (fun s => nullaryZeroOuterTerm A S u ν k s x) i

/-- 零出力の元の全項を、全係数環・全単体に共通に対にする（BF §2.2.6）。 -/
lemma nullaryZeroBalance_pairing (u : Surjection.BasisWord 1 0)
    (ν : Surjection.BasisWord 0 0) (k : Fin 1) (q : ℕ) :
    ∃ τ : Equiv.Perm (NullaryZeroBalanceIndex u k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryZeroBalanceTerm A S u ν k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryZeroBalanceTerm A S u ν k q (τ i) x =
          -nullaryZeroBalanceTerm A S u ν k q i x) := by
  let Z : Cut 0 q → Prop := fun _ => True
  let e : (Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit.{1}) ≃
      {s : Cut 0 q // Z s} :=
    (nullaryZeroCutEquiv u k q).trans
      ⟨fun s => ⟨s, trivial⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  refine ⟨matchedSubsetPerm Z e, matchedSubsetExchange_involutive Z e, ?_, ?_⟩
  · intro i hi A hA S x
    exact matchedSubsetPerm_fixed_zero Z e
      (fun c => nullaryZeroCompositeTerm A S u ν k c x)
      (fun s => nullaryZeroOuterTerm A S u ν k s x)
      (fun _ hs => False.elim (hs trivial)) i hi
  · intro i _ A hA S x
    exact matchedSubsetPerm_term_neg Z e
      (fun c => nullaryZeroCompositeTerm A S u ν k c x)
      (fun s => nullaryZeroOuterTerm A S u ν k s x)
      (fun c => nullaryZeroCompositeTerm_eq_outer A S u ν k c (e c).val x)
      (fun _ hs => False.elim (hs trivial)) i

end SerrePositivity.EInfinity.SimplexCuts
