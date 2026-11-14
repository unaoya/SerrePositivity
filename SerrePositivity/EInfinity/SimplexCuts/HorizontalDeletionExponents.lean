module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedIntervalMaxima
public import SerrePositivity.EInfinity.SimplexCuts.CaesuraDeletionSums
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalFace

/-!
# 水平削除による右端と位置指数の比較

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
残る区間の右端を対応させ、元の語のcaesura削除の重み付き和を評価する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C174：水平な二辺の中間頂点の削除は、残る全区間の右端を保つ。 -/
lemma hi_horizontalDeletion {m q : ℕ} (s : Cut (m + 1) q)
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1)
    (ha : a ∈ s.val) (hb : b ∈ s.val) (i : Fin (m + 1)) :
    hi ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) i =
      hi s ((s.horizontal a.succ).succAbove i) := by
  apply hi_eq_of_coordinate_cover s _
    (fun k => a.succ.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) k))
    (s.horizontal a.succ).succAbove (Fin.strictMono_succAbove _).injective
  · intro k
    have hh := BarrattEccles.horizontalDeletion_horizontal s a b hab ha hb
      (Fin.cast (by omega : m + q + 1 = m + 1 + q) k)
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) k) = k := Fin.ext rfl
    simpa only [hc] using hh
  · intro k
    have hv := BarrattEccles.horizontalDeletion_vertical s a ha
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

lemma positionExponent_eq_caesura_sum {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) :
    positionExponent s v = ∑ i ∈ caesuraPositions v, hi s i := by
  simp only [positionExponent, caesuraPositions, Finset.sum_filter]

/-- C175：活動区間の削除では、その右端だけが位置指数から消える。 -/
lemma positionExponent_erase_active {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : Surjection.Caesura v a)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
    positionExponent s v = positionExponent t (Surjection.erase v a) + hi s a := by
  simp only [positionExponent_eq_caesura_sum]
  have h := caesura_sum_erase_active v a ha (hi s)
  simpa only [← hh] using h

/-- C176：最後の非活動区間の削除では、直前同色区間の右端が位置指数から消える。 -/
lemma positionExponent_erase_final {m q r : ℕ} (s : Cut (m + 1) q) (t : Cut m q)
    (v : Fin (m + 2) → Fin r) (a : Fin (m + 2)) (ha : ¬Surjection.Caesura v a)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
    positionExponent s v = positionExponent t (Surjection.erase v a) +
      hi s (previousVertex v a hp) := by
  simp only [positionExponent_eq_caesura_sum]
  have h := caesura_sum_erase_final v a ha hp (hi s)
  simpa only [← hh] using h

end SerrePositivity.EInfinity.SimplexCuts
