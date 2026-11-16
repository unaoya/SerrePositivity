module

public import SerrePositivity.EInfinity.Surjection.OverlapSegments

/-!
# 元の部分語の相対位置を元の内側語で読む

Berger–Fresse §1.2.4、M14 L12a のC452の添字の移送。
元の開始位置と相対位置の和を同じ語長で読む記法。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の部分語の位置を、同じ元の内側語の位置へ送る（BF §1.2.4）。 -/
def segmentInnerWordPosition {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (i : Fin t) (z : Fin (r.val i).val) : Fin L :=
  ⟨r.start i + z.val, by have h := r.start_add_length_le i; have hz := z.isLt; omega⟩

end SerrePositivity.EInfinity.SimplexCuts
