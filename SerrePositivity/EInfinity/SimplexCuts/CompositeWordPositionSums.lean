module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePositionDecomposition
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentPositionInjective
public import SerrePositivity.EInfinity.SimplexCuts.CompositeFirstPositionOrder
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# 同じ合成語の全位置の有限和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
既存の残り位置と部分語の位置が、重複なく全位置を覆う法則で再添字付けする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の全合成位置の和は、同じ残り位置と全部分語の位置の和（BF §2.2.6）。 -/
lemma positiveComposite_wordPosition_sum {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (F : Fin (m + n + (d + e) + 1) → ℕ) :
    (∑ h, F h) =
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        F (compositeFirstPosition u v k r p.val)) +
      ∑ i : Fin (Surjection.occurrenceCount u.val k), ∑ z : Fin (r.val i).val,
        F (positiveCompositeSegmentPosition u v k r i z) := by
  let f : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k} ⊕
      (Σ i, Fin (r.val i).val) → Fin (m + n + (d + e) + 1) :=
    Sum.elim (fun p => compositeFirstPosition u v k r p.val)
      (fun t => positiveCompositeSegmentPosition u v k r t.1 t.2)
  have hdis (p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k})
      (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val)
      (he : compositeFirstPosition u v k r p.val = positiveCompositeSegmentPosition u v k r i z) :
      False := by
    have hv := congrArg (positiveCompositeCutWord u v k r).val he
    rw [positiveCompositeFirstPosition_label u v k r p.val p.property,
      positiveCompositeSegmentPosition_label] at hv
    exact BarrattEccles.remainingPosition_ne_inserted m (n + 1) k _ _ hv
  have hi : Function.Injective f := by
    rintro (p | ⟨i, z⟩) (p' | ⟨j, w⟩) he
    · change compositeFirstPosition u v k r p.val = compositeFirstPosition u v k r p'.val at he
      exact congrArg Sum.inl
        (Subtype.ext ((compositeFirstPosition_strictMono u v k r).injective he))
    · exact False.elim (hdis p j w he)
    · exact False.elim (hdis p' i z he.symm)
    · change positiveCompositeSegmentPosition u v k r i z =
        positiveCompositeSegmentPosition u v k r j w at he
      exact congrArg Sum.inr (positiveCompositeSegmentPosition_sigma_injective u v k r he)
  have hs : Function.Surjective f := by
    intro h
    rcases positiveCompositePosition_remaining_or_segment u v k r h with
      ⟨p, hp, he⟩ | ⟨i, z, he⟩
    · exact ⟨Sum.inl ⟨p, hp⟩, he.symm⟩
    · exact ⟨Sum.inr ⟨i, z⟩, he.symm⟩
  have hsum := Fintype.sum_bijective f ⟨hi, hs⟩ (F ∘ f) F (fun _ => rfl)
  simpa only [Fintype.sum_sum_type, Fintype.sum_sigma, Function.comp_apply, f,
    Sum.elim_inl, Sum.elim_inr] using hsum.symm

end SerrePositivity.EInfinity.SimplexCuts
