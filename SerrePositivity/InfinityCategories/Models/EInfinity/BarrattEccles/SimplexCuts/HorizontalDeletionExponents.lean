module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedIntervalMaxima
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CaesuraDeletionSums
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalFace

/-!
模型。文献の定義との比較は後で
# 水平削除による右端と位置指数の比較

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
残る区間の右端を対応させ、元の語のcaesura削除の重み付き和を評価する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C174：水平な二辺の中間頂点の削除は、残る全区間の右端を保つ。 -/
lemma hi_horizontalDeletion {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi ((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) i =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s ((s.horizontal a.succ).succAbove i) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_coordinate_cover s _
    (fun k => a.succ.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) k))
    (s.horizontal a.succ).succAbove (Fin.strictMono_succAbove _).injective
  · intro k
    have hh := _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_horizontal s a b hab ha hb
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k)
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) k) = k := Fin.ext rfl
    simpa only [hc] using hh
  · intro k
    have hv := _root_.SerrePositivity.EInfinity.BarrattEccles.horizontalDeletion_vertical s a ha
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k)
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) k) = k := Fin.ext rfl
    simpa only [hc] using hv
  · intro j hj
    have hne : j ≠ a.succ := by
      intro he
      rw [he] at hj
      exact Fin.succAbove_ne (s.horizontal a.succ) i hj.symm
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
    refine ⟨Fin.cast (by omega : m + 1 + q = m + q + 1) k, ?_⟩
    have hc : Fin.cast (by omega : m + q + 1 = m + 1 + q)
        (Fin.cast (by omega : m + 1 + q = m + q + 1) k) = k := Fin.ext rfl
    change a.succ.succAbove (Fin.cast _ (Fin.cast _ k)) = j
    rw [hc]
    exact hk

lemma positionExponent_eq_caesura_sum {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v = ∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions, Finset.sum_filter]

/-- C175：活動区間の削除では、その右端だけが位置指数から消える。 -/
lemma positionExponent_erase_active {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v a)
    (hh : ∀ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (a.succAbove i)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent t (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v a) + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s a := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent_eq_caesura_sum]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_sum_erase_active v a ha (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s)
  simpa only [← hh] using h

/-- C176：最後の非活動区間の削除では、直前同色区間の右端が位置指数から消える。 -/
lemma positionExponent_erase_final {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v a)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v a).Nonempty)
    (hh : ∀ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (a.succAbove i)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent t (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v a) +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousVertex v a hp) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent_eq_caesura_sum]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_sum_erase_final v a ha hp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s)
  simpa only [← hh] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
