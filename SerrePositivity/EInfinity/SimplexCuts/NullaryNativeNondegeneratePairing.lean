module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryNativeZeroValues

/-!
# 元の全分割を保持する非退化空語の対合

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §374。
元の分割の一意性と同じ一点Cut挿入を合成し、零項も全て残す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 元の空語分割の一意性による同じCutへの同値（BF §1.2.4）。 -/
def nullaryOverlapCutEquiv {c N q : ℕ} (ρ : Surjection.OverlapPartition c 0) :
    (Surjection.OverlapPartition c 0 × Cut N q) ≃ Cut N q where
  toFun := Prod.snd
  invFun t := (ρ, t)
  left_inv a := by
    apply Prod.ext
    · exact (overlap_eq_single_of_count_one ρ.count_eq_one_of_empty ρ).trans
        (overlap_eq_single_of_count_one ρ.count_eq_one_of_empty a.1).symm
    · rfl
  right_inv _ := rfl

/-- 同じ非退化raw語の元の全分割の項は小Cut項（BF §2.2.6）。 -/
lemma nullaryNativeCompositeTerm_eq_small
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord (m + 1) d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ)
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × Cut (m + d) q)
    (x : S _⦋q⦌) :
    nullaryNativeCompositeTerm A S u ν k q c x =
      nullarySmallCutTerm A S (positiveWord w) x (-((d + q : ℕ) : ℤ)) (by omega) c.2 := by
  have hc : c.1 = ρ :=
    (overlap_eq_single_of_count_one ρ.count_eq_one_of_empty c.1).trans
      (overlap_eq_single_of_count_one ρ.count_eq_one_of_empty ρ).symm
  rcases c with ⟨ρ', t⟩
  dsimp only at hc
  subst ρ'
  have hnd : Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k ρ) := by
    rw [← hw]
    exact w.property.2
  unfold nullaryNativeCompositeTerm
  rw [dite_eq_left hnd]
  have he : (⟨IntervalCuts.nullaryRawWord u ν k ρ,
      IntervalCuts.nullaryRawWord_surjective u ν k ρ, hnd⟩ :
      Surjection.BasisWord (m + 1) d) = w := Subtype.ext hw.symm
  dsimp only
  rw [he, Surjection.compositionSign_inner_degree_zero, one_smul]

/-- 元の全分割・全Cut上で非退化空語の固定零項と相殺を与える（BF §2.2.6）。 -/
lemma nullaryNativeBalance_pairing_of_nondegenerate {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord (m + 1) d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ) :
    ∃ τ : Equiv.Perm (NullaryNativeBalanceIndex u k q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryNativeBalanceTerm A S u ν k q i x = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌),
        nullaryNativeBalanceTerm A S u ν k q (τ i) x =
          -nullaryNativeBalanceTerm A S u ν k q i x) := by
  have hV : (m + 2) + d = (m + d) + 2 := by omega
  obtain ⟨p, hp, hu⟩ := unique_position_of_occurrenceCount_one u.val k ρ.count_eq_one_of_empty
  let P : Fin ((m + d) + 2) := Fin.cast hV p
  have hvp : (nullaryNativeOuterWord u).val P = k ∧
      ∀ j, (nullaryNativeOuterWord u).val j = k → j = P := word_eq_mp_unique hV u p k hp hu
  have hvw : ∀ i, k.succAbove ((positiveWord w).val i) =
      (nullaryNativeOuterWord u).val (P.succAbove i) := by
    intro i
    exact nullaryRawWord_eq_mp_erase_value (by omega) u ν k ρ w hw p hu i
  let Z : Cut ((m + d) + 1) q → Prop := fun s => outputDegree s (nullaryNativeOuterWord u) k = 0
  let e := (nullaryOverlapCutEquiv ρ).trans
    (nullaryOutputCutEquiv (m + d) q (m + 2) (nullaryNativeOuterWord u) P k hvp.1 hvp.2)
  refine ⟨matchedSubsetPerm Z e, matchedSubsetExchange_involutive Z e, ?_, ?_⟩
  · intro i hi A hA S x
    exact matchedSubsetPerm_fixed_zero Z e
      (fun c => nullaryNativeCompositeTerm A S u ν k q c x)
      (fun s => nullaryNativeOuterTerm A S u ν k q s x)
      (fun s hs => nullaryOuterCutTerm_eq_zero_of_nonzero A S _ ν k x _ (by omega) s hs) i hi
  · intro i _ A hA S x
    apply matchedSubsetPerm_term_neg Z e
      (fun c => nullaryNativeCompositeTerm A S u ν k q c x)
      (fun s => nullaryNativeOuterTerm A S u ν k q s x)
    · intro c
      rw [nullaryNativeCompositeTerm_eq_small A S u ν k ρ w hw c x]
      exact nullarySmallCutTerm_eq_insert A S _ (positiveWord w) ν P k hvp.1 hvp.2 hvw
        x _ (by omega) c.2
    · intro s hs
      exact nullaryOuterCutTerm_eq_zero_of_nonzero A S _ ν k x _ (by omega) s hs

end SerrePositivity.EInfinity.SimplexCuts
