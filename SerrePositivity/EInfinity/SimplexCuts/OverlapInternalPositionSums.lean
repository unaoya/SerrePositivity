module

public import SerrePositivity.EInfinity.SimplexCuts.SegmentEdgeOwner
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# 元の重なる部分語の内部位置による有限和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
報告 §289 の有限位置の分解。既存の辺の所属番号をそのまま使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ全内部辺の和を、所属する元の部分語ごとに読む（BF §2.2.6）。 -/
lemma sum_overlap_internal_positions {t n e : ℕ}
    (r : Surjection.OverlapPartition t ((n + 1) + e)) (ht : 0 < t)
    (F : Fin (n + e) → ℕ) :
    (∑ a, F a) = ∑ i : Fin t, ∑ z : Fin ((r.val i).val - 1),
      F ⟨r.start i + z.val, by have hb := r.start_add_length_le i; have hz := z.isLt; omega⟩ := by
  let f : (Σ i : Fin t, Fin ((r.val i).val - 1)) → Fin (n + e) := fun x =>
    ⟨r.start x.1 + x.2.val, by
      have hb := r.start_add_length_le x.1; have hz := x.2.isLt; omega⟩
  have ho (i : Fin t) (z : Fin ((r.val i).val - 1)) :
      segmentEdgeOwner r ht (f ⟨i, z⟩).val = i := by
    apply segmentEdgeOwner_unique
    · have hb := (f ⟨i, z⟩).isLt; omega
    · change r.start i ≤ r.start i + z.val
      omega
    · change r.start i + z.val + 1 < r.start i + (r.val i).val
      have hz := z.isLt; omega
  have hi : Function.Injective f := by
    rintro ⟨i, z⟩ ⟨j, w⟩ he
    have hei := congrArg (fun a : Fin (n + e) => segmentEdgeOwner r ht a.val) he
    rw [ho, ho] at hei
    subst j
    have hz := congrArg (fun a : Fin (n + e) => a.val) he
    have hzw : z = w := Fin.ext (by change r.start i + z.val = r.start i + w.val at hz; omega)
    subst w
    rfl
  have hs : Function.Surjective f := by
    intro a
    let i := segmentEdgeOwner r ht a.val
    have hl := segmentEdgeOwner_start_le r ht a.val
    have hr := segmentEdgeOwner_end_gt r ht a.val (by have hb := a.isLt; omega)
    let z : Fin ((r.val i).val - 1) := ⟨a.val - r.start i, by
      change r.start i ≤ a.val at hl
      change a.val + 1 < r.start i + (r.val i).val at hr
      omega⟩
    refine ⟨⟨i, z⟩, Fin.ext ?_⟩
    change r.start i + (a.val - r.start i) = a.val
    change r.start i ≤ a.val at hl
    omega
  have hsum := Fintype.sum_bijective f ⟨hi, hs⟩ (F ∘ f) F (fun _ => rfl)
  simpa only [Fintype.sum_sigma, Function.comp_apply, f] using hsum.symm

end SerrePositivity.EInfinity.SimplexCuts
