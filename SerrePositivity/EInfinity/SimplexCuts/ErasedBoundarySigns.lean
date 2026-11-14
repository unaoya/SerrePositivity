module

public import SerrePositivity.EInfinity.SimplexCuts.CaesuraVertexDeletion
public import SerrePositivity.EInfinity.SimplexCuts.InactiveColorDegrees

/-!
# 削除した色列の逆転符号で読むBF境界符号

Berger–Fresse §1.2.3・§2.2.4・§2.2.7、M14 L09a。
同じ頂点を削除した色列に逆転符号を移し、元の単語削除係数を残す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts (positionInversionCount)

/-- 同じ色列の一位置削除後のcaesuraの逆転符号。 -/
def erasedColorSign {N r : ℕ} (v : Fin (N + 1) → Fin r) (k : Fin (N + 1)) : ℤ :=
  (-1) ^ positionInversionCount (Surjection.erase v k) (caesuraPositions (Surjection.erase v k))

lemma caesuraRank_label_eq_active_rank {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) :
    Surjection.caesuraRank (label s v) k =
      ((activeVertexPositions s v).filter (fun j => j < k)).card := by
  unfold Surjection.caesuraRank
  congr 1
  ext j
  simp only [activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- C125：活動頂点の境界符号を同じ削除色列へ移す。 -/
lemma outputBoundarySignAt_erase_active {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : Surjection.Caesura (label s v.val) k) :
    outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
      erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k := by
  have hm : k ∈ activeVertexPositions s v.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  rw [outputBoundarySignAt_of_active s v k hm]
  unfold erasedColorSign
  rw [inversionCount_erase_active _ _ hk, Surjection.deletionCoefficient_of_caesura _ _ hk,
    caesuraRank_label_eq_active_rank]
  rfl

/-- C126：最後の非活動頂点も同じ削除色列へ移り、直前同色の符号の負を取る。 -/
lemma outputBoundarySignAt_erase_final {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : ¬ Surjection.Caesura (label s v.val) k)
    (hp : (Surjection.previousOccurrences (label s v.val) k).Nonempty) :
    outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
      erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k := by
  rw [outputBoundarySignAt_via_previous s v k hp]
  unfold erasedColorSign Surjection.deletionCoefficient
  rw [inversionCount_erase_final _ _ hk hp, ite_eq_right hk, dite_eq_left hp,
    caesuraRank_label_eq_active_rank]
  simp only [mul_neg]
  rfl

/-- C127：正の出力次数を持つ頂点の境界符号は、削除色列と単語削除係数で計算できる。 -/
lemma outputBoundarySignAt_erase {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < outputDegree s v (label s v.val k)) :
    outputBoundarySignAt s v k = (-1 : ℤ) ^ positionExponent s v.val *
      erasedColorSign (label s v.val) k * Surjection.deletionCoefficient (label s v.val) k := by
  by_cases hk : Surjection.Caesura (label s v.val) k
  · exact outputBoundarySignAt_erase_active s v k hk
  · have hm : k ∉ activeVertexPositions s v.val := fun h => hk (Finset.mem_filter.mp h).2
    exact outputBoundarySignAt_erase_final s v k hk
      (previousOccurrences_nonempty_of_inactive_degree_pos s v k hm hd)

end SerrePositivity.EInfinity.SimplexCuts
