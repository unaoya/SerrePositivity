module

public import SerrePositivity.EInfinity.Surjection.OccurrenceOrder
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# 元の語の全出現位置と指定色以外の有限和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
同じ語の色の fiber で有限和をまとめ、元の位置の和へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 全色の全出現で数えた和は、元の全位置の和（BF §1.2.4）。 -/
lemma sum_occurrences {r l : ℕ} (w : Fin l → Fin r) (F : Fin l → ℕ) :
    (∑ a : Fin r, ∑ h : ↥(Surjection.occurrences w a), F h.val) = ∑ h, F h := by
  have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := w) (fun _ _ => Finset.mem_univ _) F
  rw [← h]
  apply Finset.sum_congr rfl
  intro a _
  exact (Finset.sum_subtype _ (fun _ => Iff.rfl) F).symm

/-- 指定色以外の全出現の和は、元の指定色以外の位置の和（BF §1.2.4）。 -/
lemma sum_non_slot_occurrences {r l : ℕ} (w : Fin l → Fin r) (k : Fin r)
    (F : Fin l → ℕ) :
    (∑ a : {a : Fin r // a ≠ k}, ∑ h : ↥(Surjection.occurrences w a.val), F h.val) =
      ∑ h : {h : Fin l // w h ≠ k}, F h.val := by
  let S := Finset.univ.filter (fun p : Fin l => w p ≠ k)
  let T := Finset.univ.filter (fun a : Fin r => a ≠ k)
  have hf : ∀ p ∈ S, w p ∈ T := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  have h := Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := w) hf F
  calc
    _ = ∑ a ∈ T, ∑ p : ↥(Surjection.occurrences w a), F p.val :=
      (Finset.sum_subtype T (fun a => by simp [T])
        (fun a => ∑ p : ↥(Surjection.occurrences w a), F p.val)).symm
    _ = ∑ a ∈ T, ∑ p ∈ S.filter (fun p => w p = a), F p := by
      apply Finset.sum_congr rfl
      intro a ha
      have hak : a ≠ k := (Finset.mem_filter.mp ha).2
      have he : S.filter (fun p => w p = a) = Surjection.occurrences w a := by
        ext p
        simp only [S, Surjection.occurrences, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hp => hp.2
        · intro hp
          exact ⟨by rw [hp]; exact hak, hp⟩
      rw [he]
      exact (Finset.sum_subtype _ (fun _ => Iff.rfl) F).symm
    _ = ∑ p ∈ S, F p := h
    _ = _ := Finset.sum_subtype S (fun p => by simp [S]) F

end SerrePositivity.EInfinity.SimplexCuts
