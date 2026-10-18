module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleMixedBoundary
public import Mathlib.Data.Fintype.BigOperators

/-!
# 隣接する角の三種類への分割

概要：Berger–Fresse §1.1.3 の shuffle の内部境界を水平角・垂直角・混合角へ分割する。
方針：隣り合う二辺の水平辺集合への所属を場合分けする。
規約：混合角は既存の MixedCorner とし、二つの向きを一つの種類にまとめる。
使われ方：全境界和を二つの入力の微分と混合角の相殺に分ける。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：shuffle とその中の隣接する二辺の組（Berger–Fresse §1.1.3）。
方針：経路と辺の組に次の辺の番号が一つ大きい条件を課す。
規約：辺の向きをまだ制限しない。
使われ方：内部の境界面の全ての添字となる。 -/
abbrev AdjacentCorner (p q : ℕ) :=
  {t : ShufflePath p q × (Fin (p + q) × Fin (p + q)) // t.2.2.val = t.2.1.val + 1}

/-- 概要：shuffle の隣接する二つの水平辺の組（Berger–Fresse §1.1.3）。
方針：隣接性に加えて両方の辺が水平辺集合に属する条件を課す。
規約：辺の番号は元の経路の次数で表す。
使われ方：全内部境界の水平方向の部分を添字づける。 -/
abbrev HorizontalAdjacentCorner (p q : ℕ) :=
  {t : ShufflePath p q × (Fin (p + q) × Fin (p + q)) //
    t.2.2.val = t.2.1.val + 1 ∧ t.2.1 ∈ t.1.val ∧ t.2.2 ∈ t.1.val}

/-- 概要：shuffle の隣接する二つの垂直辺の組（Berger–Fresse §1.1.3）。
方針：隣接性に加えて両方の辺が水平辺集合に属さない条件を課す。
規約：辺の番号は元の経路の次数で表す。
使われ方：全内部境界の垂直方向の部分を添字づける。 -/
abbrev VerticalAdjacentCorner (p q : ℕ) :=
  {t : ShufflePath p q × (Fin (p + q) × Fin (p + q)) //
    t.2.2.val = t.2.1.val + 1 ∧ t.2.1 ∉ t.1.val ∧ t.2.2 ∉ t.1.val}

/-- 概要：隣接する角を水平・垂直・混合の三種類へ分ける全単射（Berger–Fresse §1.1.3）。
方針：二辺の所属の四つの場合を、同方向の二種類と異方向の一種類にまとめる。
規約：逆写像は辺の向きの条件を忘れる。
使われ方：全内部境界の有限和を三つの有限和へ分割する。 -/
def cornerPartitionEquiv (p q : ℕ) : AdjacentCorner p q ≃
    HorizontalAdjacentCorner p q ⊕ (VerticalAdjacentCorner p q ⊕ MixedCorner p q) where
  toFun c := by
    by_cases hb : c.val.2.1 ∈ c.val.1.val
    · by_cases ha : c.val.2.2 ∈ c.val.1.val
      · exact Sum.inl ⟨c.val, c.property, hb, ha⟩
      · exact Sum.inr (Sum.inr ⟨c.val, c.property, iff_of_true hb ha⟩)
    · by_cases ha : c.val.2.2 ∈ c.val.1.val
      · exact Sum.inr (Sum.inr ⟨c.val, c.property, iff_of_false hb (not_not.mpr ha)⟩)
      · exact Sum.inr (Sum.inl ⟨c.val, c.property, hb, ha⟩)
  invFun := Sum.elim (fun c => ⟨c.val, c.property.1⟩)
    (Sum.elim (fun c => ⟨c.val, c.property.1⟩) (fun c => ⟨c.val, c.property.1⟩))
  left_inv c := by
    dsimp only
    split_ifs <;> rfl
  right_inv c := by
    rcases c with c | c
    · rcases c with ⟨t, ht, hb, ha⟩
      dsimp only
      split_ifs <;> first | rfl | contradiction
    · rcases c with c | c
      · rcases c with ⟨t, ht, hb, ha⟩
        dsimp only
        split_ifs <;> first | rfl | contradiction
      · dsimp only
        split_ifs with hb ha ha
        · exact False.elim ((c.property.2.mp hb) ha)
        · rfl
        · rfl
        · exact False.elim (hb (c.property.2.mpr ha))

/-- 概要：隣接角の有限和は水平・垂直・混合の三つの和に分かれる（Berger–Fresse §1.1.3）。
方針：角の分割の全単射を有限和に適用して直和型の和を展開する。
規約：任意の可換加法モノイド値の被加数について成立する。
使われ方：内部境界の和の三分割を符号つき正規化鎖へ適用する。 -/
lemma sum_adjacentCorner_partition {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : AdjacentCorner p q → M) :
    ∑ c, f c =
      (∑ c : HorizontalAdjacentCorner p q, f ⟨c.val, c.property.1⟩) +
      ((∑ c : VerticalAdjacentCorner p q, f ⟨c.val, c.property.1⟩) +
        ∑ c : MixedCorner p q, f ⟨c.val, c.property.1⟩) := by
  classical
  rw [← (cornerPartitionEquiv p q).symm.sum_comp f, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
