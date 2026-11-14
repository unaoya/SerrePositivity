module

public import SerrePositivity.EInfinity.SimplexCuts.NestedSegmentBounds
public import SerrePositivity.EInfinity.SimplexCuts.OverlapIntervals

/-!
# 同じ二段切断からの重なる分割の復元

Berger–Fresse §1.2.4・§2.2.6、M14 L12a。
元の内側切断の共有端点から部分長を読み、元の語長・出現数で既存OverlapPartitionへ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ二段切断の各出現における部分長から復元した重なる分割（BF §2.2.6）。 -/
def positiveNestedPartition {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveNestedCutIndex u v k q) :
    Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e) :=
  Eq.mp (congrArg (fun t => Surjection.OverlapPartition t ((n + 1) + e))
    (positiveWord_occurrenceCount u k))
    (overlapOfIntervals (Surjection.occurrenceCount_pos (positiveWord u) k)
      (nestedSegmentStart c.1 (positiveWord u) k c.2)
      (nestedSegmentEnd c.1 (positiveWord u) k c.2)
      (nestedSegmentStart_le_end c.1 (positiveWord u) k c.2)
      (fun j => by have h := nestedSegmentEnd_le c.1 (positiveWord u) k c.2 j; omega)
      (fun j hj => nestedSegmentStart_zero c.1 (positiveWord u) k c.2 j hj)
      (fun j hj => by
        have h := nestedSegmentEnd_last c.1 (positiveWord u) k c.2 j hj
        omega)
      (fun i j hij => nestedSegmentEnd_eq_start c.1 (positiveWord u) k c.2 i j hij))

end SerrePositivity.EInfinity.SimplexCuts
