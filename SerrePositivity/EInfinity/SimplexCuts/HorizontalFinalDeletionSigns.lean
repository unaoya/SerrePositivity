module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalActiveDeletionSigns
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalPreviousVertices

/-!
# 最後の非活動区間の水平削除の符号

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
直前同色区間の最後へ移した削除係数と、同じ右端による位置指数の変化を合わせる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C179：最後の非活動区間の位置符号と削除係数も、元の係数語へ戻る。 -/
lemma signedDeletionCoefficient_horizontal_final {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1)) (ha : ¬Surjection.Caesura v a)
    (hk : s.horizontal k = a) (hsingle : ∀ j, s.horizontal j = a → j = k)
    (hp : (Surjection.previousOccurrences v a).Nonempty)
    (he : (Surjection.previousOccurrences (label s v) k).Nonempty)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
    (-1 : ℤ) ^ positionExponent s v * Surjection.deletionCoefficient (label s v) k =
      Surjection.deletionCoefficient v a *
        (-1 : ℤ) ^ positionExponent t (Surjection.erase v a) := by
  have hmax : k = (intervalPositions s a).max' (intervalPositions_nonempty s a) :=
    (hsingle _ (horizontal_hi_vertex s a)).symm
  have hca : ¬Surjection.Caesura (label s v) k := by
    rw [caesura_label_iff s v a k hk, ← hmax]
    simpa only [lt_self_iff_false, false_or] using ha
  have hprev := previousVertex_label_horizontal_singleton s v a k hk hsingle hp he
  have hhor : s.horizontal (previousVertex (label s v) k he) = previousVertex v a hp := by
    rw [hprev]
    exact horizontal_hi_vertex s _
  have hver : (s.vertical (previousVertex (label s v) k he)).val =
      hi s (previousVertex v a hp) := by rw [hprev]; rfl
  have hbig : Surjection.Caesura (label s v) (previousVertex (label s v) k he) :=
    (Finset.mem_filter.mp (previousVertex_active s v k he)).2
  have hsmall : Surjection.Caesura v (previousVertex v a hp) :=
    ⟨a, previousVertex_lt v a hp, (previousVertex_value v a hp).symm⟩
  simp only [previousVertex] at hbig hsmall hhor hver
  rw [positionExponent_erase_final s t v a ha hp hh,
    Surjection.deletionCoefficient_final _ _ hca he,
    Surjection.deletionCoefficient_of_caesura _ _ hbig, caesuraRank_label, hhor, hver,
    Surjection.deletionCoefficient_final _ _ ha hp,
    Surjection.deletionCoefficient_of_caesura _ _ hsmall]
  simp only [previousVertex, pow_add, mul_neg, neg_mul]
  congr 1
  have cancel (P R : ℤ) (n : ℕ) :
      (P * (-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n * R) = R * P := by
    have hs : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; simp
    calc
      _ = (R * P) * ((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) := by ac_rfl
      _ = _ := by rw [hs, mul_one]
  exact cancel _ _ _

end SerrePositivity.EInfinity.SimplexCuts
