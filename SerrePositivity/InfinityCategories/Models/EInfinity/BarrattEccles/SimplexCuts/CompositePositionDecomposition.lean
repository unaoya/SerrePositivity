module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeSegmentPositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeRemainingPositions

/-!
模型。文献の定義との比較は後で
# 元の合成語の全位置のブロック分解

Berger–Fresse §1.2.4・§2.2.6、M14 L12a のC451。
元の増加する接頭長で位置を挟み、同じ一文字か部分語の相対位置へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の合成語のどの位置も、同じ一つの接頭ブロック内（BF §2.2.6）。 -/
lemma positiveCompositePosition_block {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (h : Fin (m + n + (d + e) + 1)) :
    ∃ p : Fin (m + d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val ≤ h.val ∧
      h.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r (p.val + 1) := by
  let S : Finset (Fin (m + d + 1)) :=
    Finset.univ.filter (fun p => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val ≤ h.val)
  have hS : S.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [Fin.val_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength_zero]
    exact Nat.zero_le _
  let p := S.max' hS
  refine ⟨p, (Finset.mem_filter.mp (S.max'_mem hS)).2, ?_⟩
  by_contra hn
  have hn' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r (p.val + 1) ≤ h.val := le_of_not_gt hn
  by_cases hp : p.val + 1 = m + d + 1
  · have he : p.val + 1 = (m + 1) + d := by omega
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength_full] at hn'
    have hh := h.isLt
    omega
  · let p' : Fin (m + d + 1) := ⟨p.val + 1, by have hb := p.isLt; omega⟩
    have hp' : p' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn'⟩
    have hle := S.le_max' p' hp'
    change p.val + 1 ≤ p.val at hle
    omega

/-- 元の全合成位置は、残りの一文字か同じ挿入部分語の位置（BF §2.2.6）。 -/
lemma positiveCompositePosition_remaining_or_segment {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (h : Fin (m + n + (d + e) + 1)) :
    (∃ (p : Fin (m + d + 1)) (_hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k),
      h = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeFirstPosition u v k r p) ∨
      ∃ (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val),
        h = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z := by
  obtain ⟨p, hl, hr⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositePosition_block u v k r h
  by_cases hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p = k
  · let p' : Fin ((m + 1) + d) := ⟨p.val, by have h := p.isLt; omega⟩
    have hw : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p = u.val p' := by
      unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value (by omega) u p p' rfl
    obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.occurrenceAt_exists u.val k p' (hw.symm.trans hp)
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_prefix_length_at_occurrence u v k r i
    rw [hi] at hs
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r (p.val + 1) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val + (r.val i).val at hs
    let z : Fin (r.val i).val := ⟨h.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val, by omega⟩
    refine Or.inr ⟨i, z, Fin.ext ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition_val, hi]
    change h.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val +
      (h.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val)
    omega
  · have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength_at_non_slot u v k r p hp
    refine Or.inl ⟨p, hp, Fin.ext ?_⟩
    change h.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositePrefixLength u v k r p.val
    omega

/-- 挿入ラベルを持つ元の位置は、非退化性なしに同じ部分語から読む（BF §2.2.6）。 -/
lemma positiveCompositePosition_of_inserted_label {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (h : Fin (m + n + (d + e) + 1)) (b : Fin (n + 1))
    (hb : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k r).val h = _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b) :
    ∃ (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val),
      h = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentPosition u v k r i z := by
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositePosition_remaining_or_segment u v k r h with ⟨p, hp, he⟩ | he
  · rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeFirstPosition_label u v k r p hp] at hb
    exact False.elim (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition_ne_inserted m (n + 1) k _ b hb)
  · exact he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
