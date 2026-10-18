module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalBoundary

/-!
# 内部の水平面の添字の全単射

概要：Berger–Fresse §1.1.3 の連続する水平辺の角を小さい shuffle の水平辺で添字づける。
方針：指定した水平辺の直前へ水平辺を挿入し、その逆で二辺の最初を削除する。
規約：辺番号の次数の括弧の違いは値を変えない Fin.cast で移す。
使われ方：水平な内部面の有限和を小さい shuffle と第一の入力の内部面の和へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：shuffle とその中の一つの水平辺の組（Berger–Fresse §1.1.3）。
方針：経路と辺の直積に、水平辺集合に属する条件を課す。
規約：辺番号は小さい経路の Fin (p+q) に属する。
使われ方：水平な同方向の角を挿入する位置を指定する。 -/
abbrev HorizontalMarkedEdge (p q : ℕ) :=
  {t : ShufflePath p q × Fin (p + q) // t.2 ∈ t.1.val}

/-- 概要：shuffle の連続する二つの水平辺の角（Berger–Fresse §1.1.3）。
方針：小さい辺番号 a から大きい経路の連続する二辺を次数移送で指定する。
規約：経路の水平次数は p+1 で、角の頂点番号は a+1 である。
使われ方：shuffle の微分の内部の水平面を添字づける。 -/
abbrev HorizontalCorner (p q : ℕ) :=
  {t : ShufflePath (p + 1) q × Fin (p + q) //
    Fin.cast (by omega : p + q + 1 = p + 1 + q) t.2.castSucc ∈ t.1.val ∧
      Fin.cast (by omega : p + q + 1 = p + 1 + q) t.2.succ ∈ t.1.val}

/-- 概要：小さい経路の水平辺と大きい経路の内部の水平角の全単射（Berger–Fresse §1.1.3）。
方針：水平辺の直前への挿入と二つの水平辺の最初の削除を互いの逆とする。
規約：辺番号の自然数としての値を保存する。
使われ方：内部の水平面の有限和を小さい経路の和へ添字替えする。 -/
def horizontalCornerEquiv (p q : ℕ) : HorizontalMarkedEdge p q ≃ HorizontalCorner p q where
  toFun v := by
    let h : p + q + 1 = p + 1 + q := by omega
    let e := horizontalInsertionEquiv p q (Fin.cast h v.val.2.castSucc)
    refine ⟨((e v.val.1).val, v.val.2), (e v.val.1).property, ?_⟩
    let c : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr h.symm
    change Fin.cast h v.val.2.succ ∈
      (insertPosition v.val.1.val (c (Fin.cast h v.val.2.castSucc))).map c.symm.toEmbedding
    rw [Finset.mem_map_equiv]
    change v.val.2.succ ∈ insertPosition v.val.1.val v.val.2.castSucc
    rw [insertPosition, Finset.mem_insert]
    right
    have hm := (Finset.mem_map' (Fin.succAboveOrderEmb v.val.2.castSucc).toEmbedding).2
      v.property
    change v.val.2.castSucc.succAbove v.val.2 ∈
      v.val.1.val.map (Fin.succAboveOrderEmb v.val.2.castSucc).toEmbedding at hm
    simpa only [Fin.succAbove_castSucc_self] using hm
  invFun c := by
    let h : p + q + 1 = p + 1 + q := by omega
    let e := horizontalInsertionEquiv p q (Fin.cast h c.val.2.castSucc)
    refine ⟨(e.symm ⟨c.val.1, c.property.1⟩, c.val.2), ?_⟩
    let d : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr h.symm
    change c.val.2 ∈ erasePosition (c.val.1.val.map d.toEmbedding) c.val.2.castSucc
    rw [mem_erasePosition, Fin.succAbove_castSucc_self, Finset.mem_map_equiv]
    change Fin.cast h c.val.2.succ ∈ c.val.1.val
    exact c.property.2
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · exact (horizontalInsertionEquiv p q (Fin.cast (by omega) v.val.2.castSucc)).symm_apply_apply
        v.val.1
    · rfl
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((horizontalInsertionEquiv p q (Fin.cast (by omega) c.val.2.castSucc)).apply_symm_apply
          ⟨c.val.1, c.property.1⟩)
    · rfl

/-- 概要：経路の水平辺をその昇順の番号で添字づける（Berger–Fresse §1.1.3）。
方針：水平辺集合の昇順同値とその逆を使う。
規約：小さい経路の水平辺の番号は Fin p に属する。
使われ方：第一の入力の内部面の有限和と対応させる。 -/
def horizontalMarkedEdgeEquiv (p q : ℕ) :
    ShufflePath p q × Fin p ≃ HorizontalMarkedEdge p q where
  toFun v := ⟨(v.1, (v.1.val.orderIsoOfFin v.1.property v.2).val),
    (v.1.val.orderIsoOfFin v.1.property v.2).property⟩
  invFun v := (v.val.1, (v.val.1.val.orderIsoOfFin v.val.1.property).symm
    ⟨v.val.2, v.property⟩)
  left_inv v := by
    apply Prod.ext
    · rfl
    · exact (v.1.val.orderIsoOfFin v.1.property).symm_apply_apply v.2
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((v.val.1.val.orderIsoOfFin v.val.1.property).apply_symm_apply ⟨v.val.2, v.property⟩)

/-- 概要：昇順に番号づけた水平辺の直前の水平座標はその番号である（Berger–Fresse §1.1.3）。
方針：昇順列挙の逆像を前にある要素数で計算する。
規約：辺自体を含めない 0 始まりの番号。
使われ方：挿入後の角を入力の内部面 j+1 と対応させる。 -/
lemma horizontalMarkedEdgeEquiv_horizontal {p q : ℕ} (s : ShufflePath p q) (j : Fin p) :
    (s.horizontal (horizontalMarkedEdgeEquiv p q (s, j)).val.2.castSucc).val = j.val := by
  have h := orderIsoOfFin_index s.val s.property (s.val.orderIsoOfFin s.property j)
  change (s.val.filter (fun x => x < (s.val.orderIsoOfFin s.property j).val)).card = j.val
  simpa only [OrderIso.symm_apply_apply] using h.symm

/-- 概要：水平角への挿入で角の水平座標は元の辺の直前の座標に一つ加わる（Berger–Fresse §1.1.3）。
方針：削除前後の座標公式を削除辺の直前で適用し、挿入辺の増分を加える。
規約：角の頂点は挿入辺の直後である。
使われ方：内部の水平面と第一の入力の内部面の添字を対応させる。 -/
lemma horizontalCornerEquiv_horizontal {p q : ℕ} (v : HorizontalMarkedEdge p q) :
    ((horizontalCornerEquiv p q v).val.1.horizontal
      (Fin.cast (by omega : p + q + 1 = p + 1 + q) v.val.2.castSucc).succ).val =
      (v.val.1.horizontal v.val.2.castSucc).val + 1 := by
  let a := Fin.cast (by omega : p + q + 1 = p + 1 + q) v.val.2.castSucc
  let e := horizontalInsertionEquiv p q a
  let t := (e v.val.1).val
  have ha := (e v.val.1).property
  have hdel : e.symm ⟨t, ha⟩ = v.val.1 := e.symm_apply_apply v.val.1
  have hv := horizontalDeletion_horizontal_val t a ha a
  change (t.horizontal (a.succ.succAbove a)).val =
    ((e.symm ⟨t, ha⟩).horizontal (Fin.cast (by omega) a)).val +
      if a.val < a.val then 1 else 0 at hv
  rw [hdel, Fin.succAbove_succ_self, ite_eq_right (lt_irrefl _)] at hv
  simp only [Nat.add_zero] at hv
  have hstep := (t.step_of_mem a ha).1
  rw [hv] at hstep
  exact hstep

end SerrePositivity.EInfinity.BarrattEccles
