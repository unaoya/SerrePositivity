module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeNondegenerateComponents
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSlotBoundary
public import SerrePositivity.EInfinity.SimplexCuts.VerticesStrictIntervals
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrenceComparison

/-!
# 元の合成切断と二段切断の非退化性の一致

Berger–Fresse §2.2.6、M14 L12a のC453。
外側の指定色も元の共有端点で検査し、両方向の同じ非退化性を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory

/-- 元の合成切断が非退化なら、外側の指定色の全異なる区間は厳密に離れる（BF §2.2.6）。 -/
lemma positiveComposite_outer_slot_intervals_strict {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val)
    (i j : Fin (Surjection.occurrenceCount u.val k)) (hij : i < j) :
    hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) <
      lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k j) := by
  let nextIndex : Fin (Surjection.occurrenceCount u.val k) :=
    ⟨i.val + 1, by have hj := j.isLt; omega⟩
  have hs := positiveComposite_outer_slot_boundary_strict u v k c h i nextIndex rfl
  have hle : nextIndex ≤ j := hij
  exact lt_of_lt_of_le hs
    (lo_monotone _ ((positiveOccurrencePosition_strictMono u k).monotone hle))

/-- 元の合成切断が非退化なら、同じ外側切断も非退化（BF §2.2.6）。 -/
lemma positiveCompositeCut_outer_nondegenerate {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Nondegenerate (positiveCompositeOuterCut u v k c) (positiveWord u).val := by
  apply (faces_mono_iff _ _).mp
  intro a
  apply SimplexCategory.mono_iff_injective.mpr
  by_cases ha : a = k
  · subst a
    apply vertices_injective_of_strict_intervals
    intro p p' hp hp' hpp'
    obtain ⟨i, hi⟩ := occurrenceAt_exists (positiveWord u).val k p hp
    obtain ⟨j, hj⟩ := occurrenceAt_exists (positiveWord u).val k p' hp'
    let i' : Fin (Surjection.occurrenceCount u.val k) :=
      Fin.cast (positiveWord_occurrenceCount u k) i
    let j' : Fin (Surjection.occurrenceCount u.val k) :=
      Fin.cast (positiveWord_occurrenceCount u k) j
    have hip : positiveOccurrencePosition u k i' = p :=
      (positiveOccurrencePosition_eq u k i' i rfl).trans hi
    have hjp : positiveOccurrencePosition u k j' = p' :=
      (positiveOccurrencePosition_eq u k j' j rfl).trans hj
    have ho : positiveOccurrencePosition u k i' < positiveOccurrencePosition u k j' := by
      rw [hip, hjp]
      exact hpp'
    have hij : i' < j' := (positiveOccurrencePosition_strictMono u k).lt_iff_lt.mp ho
    simpa only [hip, hjp] using positiveComposite_outer_slot_intervals_strict u v k c h i' j' hij
  · have he := positiveComposite_remaining_face u v k c ⟨a, ha⟩
    have hp := congrArg (fun f : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
      Function.Injective f.2) he
    exact hp.mpr (vertices_strictMono h
      (BarrattEccles.remainingPosition m (n + 1) k ⟨a, ha⟩)).injective

/-- C453：元の合成切断と同じ二段切断の非退化性は一致（BF §2.2.6）。 -/
lemma positiveCompositeCut_nondegenerate_iff {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val ↔
      Nondegenerate (positiveCompositeOuterCut u v k c) (positiveWord u).val ∧
        Nondegenerate (positiveCompositeInnerCut u v k c) (positiveWord v).val :=
  ⟨fun h => ⟨positiveCompositeCut_outer_nondegenerate u v k c h,
    positiveCompositeCut_inner_nondegenerate u v k c h⟩,
    fun h => positiveCompositeCut_nondegenerate_of_nested u v k c h.1 h.2⟩

end SerrePositivity.EInfinity.SimplexCuts
