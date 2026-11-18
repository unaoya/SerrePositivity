module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.AdjacentColorPairs
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutRenaming
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ActiveRanks

/-!
模型。文献の定義との比較は後で
# 隣接色交換と区間切断の Koszul 符号

概要：Berger–Fresse §2.2.4 の切断係数の変化を交換二出力の次数で表す。
方針：逆転集合の対称差を二色の一対へ帰着し、両色の活動性を辺の次数へ同定する。
規約：非退化な切断だけで符号を比較し、退化項は別途零として扱う。
使われ方：実際の区間余演算の隣接互換に対する等変性。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.Coxeter
open scoped _root_.symmDiff

/-- 概要：有限集合の濃度の符号の比は対称差の濃度の符号（BF §2.2.4）。
方針：二つの差集合と共通部分の濃度式で偶数の寄与を消す。
規約：整数の −1 冪。
使われ方：逆転集合の変化を切断符号へ移す。 -/
lemma neg_one_pow_card_symmDiff {α : Type*} [DecidableEq α] (s t : Finset α) :
    (-1 : ℤ) ^ s.card = (-1 : ℤ) ^ t.card * (-1 : ℤ) ^ (s ∆ t).card := by
  have hd : Disjoint (s \ t) (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hc : (s ∆ t).card = (s \ t).card + (t \ s).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  have hs := Finset.card_sdiff_add_card_inter s t
  have ht := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm t s] at ht
  have he : s.card + 2 * (t \ s).card = t.card + (s ∆ t).card := by omega
  have hp := congrArg (fun k : ℕ => (-1 : ℤ) ^ k) he
  simpa only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one] using hp

/-- 概要：色単射な位置集合の隣接交換の逆転符号は二色出現で変わる（BF §2.2.4）。
方針：逆転集合の対称差の濃度と二色対の零一公式を使う。
規約：元位置の集合と順序は固定。
使われ方：切断の活動位置集合への適用。 -/
lemma positionInversionSign_adjacent {n l : ℕ} (a : Fin n)
    (u : Fin l → Fin (n + 1)) (s : Finset (Fin l)) (hu : Set.InjOn u s) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (adjacentTransposition a ∘ u) s =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s *
        (-1 : ℤ) ^ (if a.castSucc ∈ s.image u ∧ a.succ ∈ s.image u then 1 else 0) := by
  have hab : a.castSucc ≠ a.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.neg_one_pow_card_symmDiff (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions (adjacentTransposition a ∘ u) s)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions u s)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions_symmDiff_adjacent] at h
  change (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions (adjacentTransposition a ∘ u) s).card =
    (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversions u s).card *
      (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs u s a.castSucc a.succ).card at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.card_positionInversions, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.card_colorCrossPairs u s hu _ _ hab] using h

/-- 概要：隣接色交換の切断符号は交換二出力の次数の積で変わる（BF §2.2.4）。
方針：活動色の存在を出力が辺である条件へ戻し、面次数の零一公式を使う。
規約：非退化な切断、任意の全射語次数。
使われ方：切断の各項を実際の隣接 Koszul 交換と比較する。 -/
lemma edgeSign_adjacent {n d : ℕ} (a : Fin n) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) d)
    (p : Fin (n + 1 + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (adjacentTransposition a ∘ u.val) p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p *
      (-1 : ℤ) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p a.castSucc) *
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p a.succ)) := by
  have hren := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_rename_iff (adjacentTransposition a) u.val p).mpr h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount hren, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount h,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_rename, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionSign_adjacent a u.val _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn h)]
  have hc (k : Fin (n + 1)) : k ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val p).image u.val ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge := by
    rw [Finset.mem_image]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u p h k).symm
  simp only [hc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_eq_edge_indicator]
  split_ifs <;> simp_all

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
