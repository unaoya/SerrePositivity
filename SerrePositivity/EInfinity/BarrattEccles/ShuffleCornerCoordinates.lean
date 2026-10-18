module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCornerPartition
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalCorner
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalCorner

/-!
# 隣接する角と次数を下げた角の添字の比較

概要：Berger–Fresse §1.1.3 の内部境界の三分割と、辺の削除による添字替えを接続する。
方針：隣接する二辺の最初の番号から小さい次数の辺番号を復元する。
規約：大きい経路の次数は水平方向または垂直方向に一つ増やして表す。
使われ方：分割した同方向の境界和へ既存の微分項の計算を適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：次数を下げた垂直角と元の経路の隣接垂直角の全単射（Berger–Fresse §1.1.3）。
方針：小さい辺番号 a を二辺 a.castSucc と a.succ へ送り、隣接性から逆を作る。
規約：大きい経路の垂直次数は q+1 である。
使われ方：内部境界の垂直部分を辺の削除で計算した和へ移す。 -/
def verticalAdjacentCornerEquiv (p q : ℕ) :
    VerticalCorner p q ≃ VerticalAdjacentCorner p (q + 1) where
  toFun c := ⟨(c.val.1, (c.val.2.castSucc, c.val.2.succ)), rfl, c.property⟩
  invFun c := by
    let a : Fin (p + q) := ⟨c.val.2.1.val, by
      have h := c.val.2.2.isLt
      have hnext := c.property.1
      omega⟩
    have hb : a.castSucc = c.val.2.1 := Fin.ext rfl
    have ha : a.succ = c.val.2.2 := Fin.ext c.property.1.symm
    exact ⟨(c.val.1, a), by simpa only [hb] using c.property.2.1,
      by simpa only [ha] using c.property.2.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; rfl
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Fin.ext; rfl
      · apply Fin.ext; exact c.property.1.symm

/-- 概要：次数を下げた水平角と元の経路の隣接水平角の全単射（Berger–Fresse §1.1.3）。
方針：小さい辺番号から次数を移した連続する二辺を作り、最初の辺の値で逆を与える。
規約：大きい経路の水平次数は p+1 である。
使われ方：内部境界の水平部分を辺の削除で計算した和へ移す。 -/
def horizontalAdjacentCornerEquiv (p q : ℕ) :
    HorizontalCorner p q ≃ HorizontalAdjacentCorner (p + 1) q where
  toFun c := ⟨(c.val.1, (Fin.cast (by omega) c.val.2.castSucc,
    Fin.cast (by omega) c.val.2.succ)), rfl, c.property⟩
  invFun c := by
    let a : Fin (p + q) := ⟨c.val.2.1.val, by
      have h := c.val.2.2.isLt
      have hnext := c.property.1
      omega⟩
    have hb : Fin.cast (by omega) a.castSucc = c.val.2.1 := Fin.ext rfl
    have ha : Fin.cast (by omega) a.succ = c.val.2.2 := Fin.ext c.property.1.symm
    exact ⟨(c.val.1, a), by simpa only [hb] using c.property.2.1,
      by simpa only [ha] using c.property.2.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; rfl
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Fin.ext; rfl
      · apply Fin.ext; exact c.property.1.symm

end SerrePositivity.EInfinity.BarrattEccles
