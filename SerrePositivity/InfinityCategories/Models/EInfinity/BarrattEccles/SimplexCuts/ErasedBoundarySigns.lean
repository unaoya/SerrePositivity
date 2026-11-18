module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CaesuraVertexDeletion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.InactiveColorDegrees

/-!
模型。文献の定義との比較は後で
# 削除した色列の逆転符号で読むBF境界符号

Berger–Fresse §1.2.3・§2.2.4・§2.2.7、M14 L09a。
同じ頂点を削除した色列に逆転符号を移し、元の単語削除係数を残す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts (positionInversionCount)

/-- 同じ色列の一位置削除後のcaesuraの逆転符号。 -/
def erasedColorSign {N r : ℕ} (v : Fin (N + 1) → Fin r) (k : Fin (N + 1)) : ℤ :=
  (-1) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v k))

lemma caesuraRank_label_eq_active_rank {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v).filter (fun j => j < k)).card := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank
  congr 1
  ext j
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- C125：活動頂点の境界符号を同じ削除色列へ移す。 -/
lemma outputBoundarySignAt_erase_active {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v k = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v.val *
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k := by
  have hm : k ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_of_active s v k hm]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.inversionCount_erase_active _ _ hk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _ hk,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraRank_label_eq_active_rank]
  rfl

/-- C126：最後の非活動頂点も同じ削除色列へ移り、直前同色の符号の負を取る。 -/
lemma outputBoundarySignAt_erase_final {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hk : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k).Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v k = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v.val *
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_via_previous s v k hp]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.inversionCount_erase_final _ _ hk hp, ite_eq_right hk, dite_eq_left hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraRank_label_eq_active_rank]
  simp only [mul_neg]
  rfl

/-- C127：正の出力次数を持つ頂点の境界符号は、削除色列と単語削除係数で計算できる。 -/
lemma outputBoundarySignAt_erase {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (k : Fin (m + q + 1))
    (hd : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt s v k = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v.val *
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k := by
  by_cases hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_erase_active s v k hk
  · have hm : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val := fun h => hk (Finset.mem_filter.mp h).2
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_erase_final s v k hk
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousOccurrences_nonempty_of_inactive_degree_pos s v k hm hd)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
