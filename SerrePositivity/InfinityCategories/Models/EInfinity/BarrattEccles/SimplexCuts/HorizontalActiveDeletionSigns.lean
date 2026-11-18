module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ExpandedCaesuraRanks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalDeletionExponents

/-!
模型。文献の定義との比較は後で
# 活動区間の水平削除の符号

Berger–Fresse §1.2.3・§2.2.7、M14 L09a。
展開順位の垂直座標と位置指数の右端が二度現れるので、同じ符号の二乗で消える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C177：活動区間を消す水平面の位置符号と削除係数を、元の係数語へ戻す。 -/
lemma signedDeletionCoefficient_horizontal_active {m q r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 2) → Fin r)
    (a : Fin (m + 2)) (k : Fin (m + 1 + q + 1)) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v a)
    (hk : s.horizontal k = a) (hy : (s.vertical k).val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s a)
    (hh : ∀ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi t i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s (a.succAbove i)) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent s v * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v a *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent t (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v a) := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_label_iff s v a k hk).mpr (Or.inr ha)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positionExponent_erase_active s t v a ha hh,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _ hc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraRank_label s v k, hk, hy,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _ ha]
  simp only [pow_add]
  have cancel (P R : ℤ) (n : ℕ) :
      (P * (-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n * R) = R * P := by
    have hs : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; simp
    calc
      _ = (R * P) * ((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) := by ac_rfl
      _ = _ := by rw [hs, mul_one]
  exact cancel _ _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
