module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ErasedCaesuraRanks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ErasedBoundarySigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerPositionExponent

/-!
模型。文献の定義との比較は後で
# 隣接同色と混合角の削除色列

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
同じ削除色列を使い、残る逆転符号の一致と単語削除係数の交代性を評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C140：隣接する同色のどちらを消しても同じ色列。 -/
lemma erase_adjacent_equal {N r : ℕ} (v : Fin (N + 1) → Fin r) (a b : Fin (N + 1))
    (hab : b.val = a.val + 1) (hv : v a = v b) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v b := by
  funext j
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase, Function.comp_apply, Fin.succAbove]
  split_ifs with hA hB hB
  · rfl
  · change j.val < a.val at hA
    change ¬j.val < b.val at hB
    omega
  · have ha : j.castSucc = a := by
      apply Fin.ext
      change j.val = a.val
      change ¬j.val < a.val at hA
      change j.val < b.val at hB
      omega
    have hb : j.succ = b := by
      apply Fin.ext
      have h := congrArg Fin.val ha
      change j.val = a.val at h
      change j.val + 1 = b.val
      omega
    rw [ha, hb]
    exact hv.symm
  · rfl

/-- C141：隣接同色の二つの単語削除係数は反対。 -/
lemma deletionCoefficient_adjacent_equal {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N)
    (hab : b.val = a.val + 1) (hv : v a = v b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v b = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v a := by
  have hlt : a < b := by change a.val < b.val; omega
  have hA : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v a := ⟨b, hlt, hv.symm⟩
  by_cases hB : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v b
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura v b hB,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura v a hA, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraRank_adjacent v a b hab,
      ite_eq_left hA]
    simp [pow_succ]
  · have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v b).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hv⟩⟩
    have he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v b).max' hp = a := by
      apply (Finset.max'_eq_iff _ _ _).mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hv⟩, ?_⟩
      intro j hj
      have hjb := (Finset.mem_filter.mp hj).2.1
      change j.val ≤ a.val
      change j.val < b.val at hjb
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_final v b hB hp, he]

/-- C142：交換した混合角から同じ中間頂点を消した色列は一致。 -/
lemma erase_label_swapSteps {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (s.swapSteps a b) v) b.castSucc =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) b.castSucc := by
  funext j
  change v ((s.swapSteps a b).horizontal (b.castSucc.succAbove j)) =
    v (s.horizontal (b.castSucc.succAbove j))
  apply congrArg v
  exact s.horizontal_swapSteps a b hab _
    (fun h => Fin.succAbove_ne b.castSucc j (Fin.ext h))

/-- C143：同じ削除色列の逆転符号も一致。 -/
lemma erasedColorSign_swapSteps {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r)
    (a b : Fin (m + q)) (hab : b.val = a.val + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label (s.swapSteps a b) v) b.castSucc =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) b.castSucc := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erase_label_swapSteps s v a b hab]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
