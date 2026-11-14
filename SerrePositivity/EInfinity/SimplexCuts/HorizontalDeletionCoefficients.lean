module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalFinalDeletionSigns
public import SerrePositivity.EInfinity.SimplexCuts.ErasedBoundarySigns

/-!
# 正次数の水平境界の単語削除係数

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
一頂点の水平区間で正の出力次数があれば、最後の位置の先行同色も元の語へ戻せる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C181：一頂点の区間の前に同色頂点があれば、元の語にも先行同色位置がある。 -/
lemma previousOccurrences_of_horizontal_singleton {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin (m + 1)) (k : Fin (m + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty) :
    (Surjection.previousOccurrences v a).Nonempty := by
  obtain ⟨j, hj⟩ := he
  have hjk := (Finset.mem_filter.mp hj).2.1
  have hcolor := (Finset.mem_filter.mp hj).2.2
  refine ⟨s.horizontal j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
  · have hle := s.horizontal.monotone hjk.le
    rw [hk] at hle
    apply lt_of_le_of_ne hle
    intro h
    exact (ne_of_lt hjk) (hsingle j h)
  · simpa only [label, hk] using hcolor

/-- C182：正次数の水平面の位置符号と削除係数は、活動性の仮定なしに元の語へ戻る。 -/
lemma signedDeletionCoefficient_horizontal {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Surjection.Word r (m + 2))
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1))
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hd : 0 < outputDegree s v (label s v.val k))
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
    (-1 : ℤ) ^ positionExponent s v.val * Surjection.deletionCoefficient (label s v.val) k =
      Surjection.deletionCoefficient v.val a *
        (-1 : ℤ) ^ positionExponent t (Surjection.erase v.val a) := by
  have hmax : k = (intervalPositions s a).max' (intervalPositions_nonempty s a) :=
    (hsingle _ (horizontal_hi_vertex s a)).symm
  by_cases ha : Surjection.Caesura v.val a
  · have hy : (s.vertical k).val = hi s a := by rw [hmax]; rfl
    exact signedDeletionCoefficient_horizontal_active s t v.val a k ha hk hy hh
  · have hca : ¬Surjection.Caesura (label s v.val) k := by
      rw [caesura_label_iff s v.val a k hk, ← hmax]
      simpa only [lt_self_iff_false, false_or] using ha
    have hm : k ∉ activeVertexPositions s v.val := fun h => hca (Finset.mem_filter.mp h).2
    have he := previousOccurrences_nonempty_of_inactive_degree_pos s v k hm hd
    have hp := previousOccurrences_of_horizontal_singleton s v.val a k hk hsingle he
    exact signedDeletionCoefficient_horizontal_final s t v.val a k ha hk hsingle hp he hh

end SerrePositivity.EInfinity.SimplexCuts
