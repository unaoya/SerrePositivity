module

public import SerrePositivity.EInfinity.SimplexCuts.ExpandedCaesuraRanks
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionExponents

/-!
# 活動区間の水平削除の符号

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
展開順位の垂直座標と位置指数の右端が二度現れるので、同じ符号の二乗で消える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C177：活動区間を消す水平面の位置符号と削除係数を、元の係数語へ戻す。 -/
lemma signedDeletionCoefficient_horizontal_active {m q r : ℕ}
    (s : Cut (m + 1) q) (t : Cut m q) (v : Fin (m + 2) → Fin r)
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1)) (ha : Surjection.Caesura v a)
    (hk : s.horizontal k = a) (hy : (s.vertical k).val = hi s a)
    (hh : ∀ i, hi t i = hi s (a.succAbove i)) :
    (-1 : ℤ) ^ positionExponent s v * Surjection.deletionCoefficient (label s v) k =
      Surjection.deletionCoefficient v a *
        (-1 : ℤ) ^ positionExponent t (Surjection.erase v a) := by
  have hc := (caesura_label_iff s v a k hk).mpr (Or.inr ha)
  rw [positionExponent_erase_active s t v a ha hh,
    Surjection.deletionCoefficient_of_caesura _ _ hc, caesuraRank_label s v k, hk, hy,
    Surjection.deletionCoefficient_of_caesura _ _ ha]
  simp only [pow_add]
  have cancel (P R : ℤ) (n : ℕ) :
      (P * (-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n * R) = R * P := by
    have hs : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; simp
    calc
      _ = (R * P) * ((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) := by ac_rfl
      _ = _ := by rw [hs, mul_one]
  exact cancel _ _ _

end SerrePositivity.EInfinity.SimplexCuts
