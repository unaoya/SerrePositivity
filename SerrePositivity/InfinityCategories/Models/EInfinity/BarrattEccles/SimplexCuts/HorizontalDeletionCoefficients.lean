module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalFinalDeletionSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ErasedBoundarySigns

/-!
模型。文献の定義との比較は後で
# 正次数の水平境界の単語削除係数

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
一頂点の水平区間で正の出力次数があれば、最後の位置の先行同色も元の語へ戻せる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C181：一頂点の区間の前に同色頂点があれば、元の語にも先行同色位置がある。 -/
lemma previousOccurrences_of_horizontal_singleton {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin (m + 1)) (k : Fin (m + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k).Nonempty) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v a).Nonempty := by
  obtain ⟨j, hj⟩ := he
  have hjk := (Finset.mem_filter.mp hj).2.1
  have hcolor := (Finset.mem_filter.mp hj).2.2
  refine ⟨s.horizontal j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
  · have hle := s.horizontal.monotone hjk.le
    rw [hk] at hle
    apply lt_of_le_of_ne hle
    intro h
    exact (ne_of_lt hjk) (hsingle j h)
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label, hk] using hcolor

/-- C182：正次数の水平面の位置符号と削除係数は、活動性の仮定なしに元の語へ戻る。 -/
lemma signedDeletionCoefficient_horizontal {m q r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2))
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hd : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k))
    (hh : ∀ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (a.succAbove i)) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v.val * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val a *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent t (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val a) := by
  have hmax : k = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s a).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s a) :=
    (hsingle _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s a)).symm
  by_cases ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val a
  · have hy : (s.vertical k).val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s a := by rw [hmax]; rfl
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.signedDeletionCoefficient_horizontal_active s t v.val a k ha hk hy hh
  · have hca : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val) k := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_label_iff s v.val a k hk, ← hmax]
      simpa only [lt_self_iff_false, false_or] using ha
    have hm : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.activeVertexPositions s v.val := fun h => hca (Finset.mem_filter.mp h).2
    have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousOccurrences_nonempty_of_inactive_degree_pos s v k hm hd
    have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.previousOccurrences_of_horizontal_singleton s v.val a k hk hsingle he
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.signedDeletionCoefficient_horizontal_final s t v.val a k ha hk hsingle hp he hh

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
