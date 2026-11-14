module

public import SerrePositivity.EInfinity.SimplexCuts.AllHorizontalDeletionCoordinates
public import SerrePositivity.EInfinity.SimplexCuts.VerticalBoundaryEquiv

/-!
# 全垂直境界同値の指定削除座標

Berger–Fresse §2.2.7、M14 L09a。
既存の方向交換で水平削除の座標を運び、同じ入力面の番号と小さい切断を保持する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C249：既存の全垂直同値は、削除する入力頂点の番号を保つ。 -/
lemma verticalBoundaryFaceEquiv_vertical (m q : ℕ) (c : Fin (q + 2) × Cut m q) :
    (verticalBoundaryFaceEquiv m q c).val.1.vertical
      (verticalBoundaryFaceEquiv m q c).val.2 = c.1 := by
  let z := horizontalBoundaryFaceEquiv q m (c.1, c.2.exchange)
  change z.val.1.exchange.vertical (Fin.cast (by omega : q + 1 + m + 1 = m + (q + 1) + 1)
      z.val.2) = c.1
  rw [BarrattEccles.ShufflePath.exchange_vertical]
  exact horizontalBoundaryFaceEquiv_horizontal q m (c.1, c.2.exchange)

/-- C250：既存の全垂直同値が指定する同じ切断における両座標の削除式。 -/
lemma verticalBoundaryFaceEquiv_deleted_coordinates (m q : ℕ)
    (c : Fin (q + 2) × Cut m q) (j : Fin (m + q + 1)) :
    let z := (verticalBoundaryFaceEquiv m q c).val
    z.1.horizontal (z.2.succAbove j) = c.2.horizontal j ∧
      z.1.vertical (z.2.succAbove j) = c.1.succAbove (c.2.vertical j) := by
  let z := horizontalBoundaryFaceEquiv q m (c.1, c.2.exchange)
  let l : Fin (q + m + 1) := Fin.cast (by omega) j
  let a := z.val.2.succAbove (Fin.cast (by omega : q + m + 1 = q + 1 + m) l)
  have hcast : Fin.cast (by omega : q + 1 + m + 1 = m + (q + 1) + 1) a =
      (Fin.cast (by omega : q + 1 + m + 1 = m + (q + 1) + 1) z.val.2).succAbove j := by
    apply Fin.ext
    simp only [a, l, Fin.succAbove, Fin.val_cast, apply_ite, Fin.lt_def,
      Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> rfl
  have ht := horizontalBoundaryFaceEquiv_deleted_coordinates q m (c.1, c.2.exchange) l
  change z.val.1.horizontal a = c.1.succAbove (c.2.exchange.horizontal l) ∧
    z.val.1.vertical a = c.2.exchange.vertical l at ht
  have hv := c.2.exchange_vertical j
  have hh := c.2.exchange_horizontal j
  change c.2.exchange.vertical l = c.2.horizontal j at hv
  change c.2.exchange.horizontal l = c.2.vertical j at hh
  change z.val.1.exchange.horizontal
      ((Fin.cast (by omega : q + 1 + m + 1 = m + (q + 1) + 1) z.val.2).succAbove j) =
        c.2.horizontal j ∧
    z.val.1.exchange.vertical
      ((Fin.cast (by omega : q + 1 + m + 1 = m + (q + 1) + 1) z.val.2).succAbove j) =
        c.1.succAbove (c.2.vertical j)
  rw [← hcast, BarrattEccles.ShufflePath.exchange_horizontal,
    BarrattEccles.ShufflePath.exchange_vertical, ht.1, ht.2, hv, hh]
  exact ⟨rfl, rfl⟩

end SerrePositivity.EInfinity.SimplexCuts
