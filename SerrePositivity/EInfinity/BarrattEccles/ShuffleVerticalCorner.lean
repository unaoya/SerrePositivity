module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalBoundary

/-!
# 内部の垂直面の添字の全単射

概要：Berger–Fresse §1.1.3 の連続する垂直辺の角を小さい shuffle の垂直辺で添字づける。
方針：指定した垂直辺の直前へ垂直辺を挿入し、その逆で二辺の最初を削除する。
規約：内部面は二辺の間の頂点を削除する面であり、始端と終端は別に扱う。
使われ方：垂直な内部面の有限和を小さい shuffle と第二の入力の内部面の和へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：shuffle とその中の一つの垂直辺の組（Berger–Fresse §1.1.3）。
方針：経路と辺の直積に、水平辺集合に属さない条件を課す。
規約：辺番号は小さい経路の Fin (p+q) に属する。
使われ方：垂直な同方向の角を挿入する位置を指定する。 -/
abbrev VerticalMarkedEdge (p q : ℕ) :=
  {t : ShufflePath p q × Fin (p + q) // t.2 ∉ t.1.val}

/-- 概要：shuffle の連続する二つの垂直辺の角（Berger–Fresse §1.1.3）。
方針：小さい辺番号 a を使い、大きい経路の辺 a.castSucc と a.succ の垂直属性を課す。
規約：経路の垂直次数は q+1 で、角の頂点番号は a+1 である。
使われ方：shuffle の微分の内部の垂直面を添字づける。 -/
abbrev VerticalCorner (p q : ℕ) :=
  {t : ShufflePath p (q + 1) × Fin (p + q) //
    t.2.castSucc ∉ t.1.val ∧ t.2.succ ∉ t.1.val}

/-- 概要：小さい経路の垂直辺と大きい経路の内部の垂直角の全単射（Berger–Fresse §1.1.3）。
方針：垂直辺の直前への挿入と二つの垂直辺の最初の削除を互いの逆とする。
規約：添字の辺番号の値は挿入・削除で変わらない。
使われ方：内部の垂直面の有限和を小さい経路の和へ添字替えする。 -/
def verticalCornerEquiv (p q : ℕ) : VerticalMarkedEdge p q ≃ VerticalCorner p q where
  toFun v := by
    let e := verticalInsertionEquiv p q v.val.2.castSucc
    refine ⟨((e v.val.1).val, v.val.2), (e v.val.1).property, ?_⟩
    have hmem : v.val.2.castSucc.succAbove v.val.2 ∈ (e v.val.1).val.val ↔
        v.val.2 ∈ v.val.1.val :=
      Finset.mem_map' (Fin.succAboveOrderEmb v.val.2.castSucc).toEmbedding
    simpa only [Fin.succAbove_castSucc_self] using fun h => v.property (hmem.mp h)
  invFun c := by
    refine ⟨(((verticalInsertionEquiv p q c.val.2.castSucc).symm
      ⟨c.val.1, c.property.1⟩), c.val.2), ?_⟩
    change c.val.2 ∉ erasePosition c.val.1.val c.val.2.castSucc
    simpa only [mem_erasePosition, Fin.succAbove_castSucc_self] using c.property.2
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · exact (verticalInsertionEquiv p q v.val.2.castSucc).symm_apply_apply v.val.1
    · rfl
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((verticalInsertionEquiv p q c.val.2.castSucc).apply_symm_apply ⟨c.val.1, c.property.1⟩)
    · rfl

/-- 概要：経路の垂直辺をその昇順の番号で添字づける（Berger–Fresse §1.1.3）。
方針：水平辺集合の補集合の昇順同値とその逆を使う。
規約：小さい経路の垂直辺の番号は Fin q に属する。
使われ方：内部の第二の入力の面の有限和と対応させる。 -/
def verticalMarkedEdgeEquiv (p q : ℕ) : ShufflePath p q × Fin q ≃ VerticalMarkedEdge p q where
  toFun v := ⟨(v.1, (v.1.valᶜ.orderIsoOfFin v.1.compl_card v.2).val),
    Finset.mem_compl.mp (v.1.valᶜ.orderIsoOfFin v.1.compl_card v.2).property⟩
  invFun v := (v.val.1, (v.val.1.valᶜ.orderIsoOfFin v.val.1.compl_card).symm
    ⟨v.val.2, Finset.mem_compl.mpr v.property⟩)
  left_inv v := by
    apply Prod.ext
    · rfl
    · exact (v.1.valᶜ.orderIsoOfFin v.1.compl_card).symm_apply_apply v.2
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((v.val.1.valᶜ.orderIsoOfFin v.val.1.compl_card).apply_symm_apply
          ⟨v.val.2, Finset.mem_compl.mpr v.property⟩)

/-- 概要：昇順に番号づけた垂直辺の直前の垂直座標はその番号である（Berger–Fresse §1.1.3）。
方針：有限集合の昇順列挙の逆像を、前にある要素数で計算する。
規約：辺自体を数えないので番号は 0 始まりである。
使われ方：挿入後の角の欠落頂点が入力の内部面 j+1 であることを示す。 -/
lemma verticalMarkedEdgeEquiv_vertical {p q : ℕ} (s : ShufflePath p q) (j : Fin q) :
    (s.vertical (verticalMarkedEdgeEquiv p q (s, j)).val.2.castSucc).val = j.val := by
  have h := orderIsoOfFin_index s.valᶜ s.compl_card
    (s.valᶜ.orderIsoOfFin s.compl_card j)
  change (s.valᶜ.filter (fun x => x < (s.valᶜ.orderIsoOfFin s.compl_card j).val)).card = j.val
  simpa only [OrderIso.symm_apply_apply] using h.symm

/-- 概要：垂直角への挿入で角の垂直座標は元の辺の直前の座標に一つ加わる（Berger–Fresse §1.1.3）。
方針：削除前後の座標公式を削除辺の直前で適用し、挿入した垂直辺の増分を加える。
規約：角の頂点は挿入辺の直後である。
使われ方：内部の垂直面と第二の入力の内部面の添字を対応させる。 -/
lemma verticalCornerEquiv_vertical {p q : ℕ} (v : VerticalMarkedEdge p q) :
    ((verticalCornerEquiv p q v).val.1.vertical v.val.2.castSucc.succ).val =
      (v.val.1.vertical v.val.2.castSucc).val + 1 := by
  let e := verticalInsertionEquiv p q v.val.2.castSucc
  let t := (e v.val.1).val
  have ha := (e v.val.1).property
  have hdel : e.symm ⟨t, ha⟩ = v.val.1 := e.symm_apply_apply v.val.1
  have hv := verticalDeletion_vertical_val t v.val.2.castSucc ha v.val.2.castSucc
  change (t.vertical (v.val.2.castSucc.succ.succAbove v.val.2.castSucc)).val =
    ((e.symm ⟨t, ha⟩).vertical v.val.2.castSucc).val +
      if v.val.2.val < v.val.2.val then 1 else 0 at hv
  rw [hdel, ite_eq_right (lt_irrefl _)] at hv
  simp only [Nat.add_zero] at hv
  have hcut : v.val.2.castSucc.succ.succAbove v.val.2.castSucc =
      v.val.2.castSucc.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by change v.val.2.val < v.val.2.val + 1; omega)
  rw [hcut] at hv
  have hstep := (t.step_of_notMem v.val.2.castSucc ha).2
  rw [hv] at hstep
  exact hstep

end SerrePositivity.EInfinity.BarrattEccles
