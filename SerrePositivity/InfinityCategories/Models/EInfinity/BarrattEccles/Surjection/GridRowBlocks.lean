module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionGridCoordinates

/-!
模型。文献の定義との比較は後で
# 元の成分行列を格子座標上の部分合成として表示する

概要：Berger–Fresse §1.5.7 の水平・垂直の実際の行列を格子座標列の map へ同定する。
方針：元の連続置換区間を有限連続座標で列挙し、範囲内の rowAtGrid を評価する。
規約：全ての評価座標に元の行数の上界を証明する。
使われ方：融合行列の連結を実際の経路座標列へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：有限列の連続区間の写像は開始添字を足した有限列（BF §1.5.7）。
方針：リスト長と各位置の drop・take・ofFn の評価を比較する。
規約：切断区間は元の有限列の範囲内。
使われ方：元の連続置換区間を格子の単位座標列へ移す。 -/
lemma map_ofFn_slice {α β : Type*} {D : ℕ} (f : Fin D → α) (g : α → β)
    (a t : ℕ) (h : a + t ≤ D) :
    (((List.ofFn f).drop a).take t).map g =
      List.ofFn (fun k : Fin t => g (f ⟨a + k.val, by have := k.isLt; omega⟩)) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

namespace TableCompositionData

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：実際の水平成分の全格子座標（BF §1.5.7）。
方針：外側始行から成分次数だけ連続して進む。
規約：内側座標は同じ境界の所属行に固定する。
使われ方：実際の水平行列を経路座標へ比較する。 -/
def horizontalGridVertices {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    List (ℕ × ℕ) :=
  List.ofFn (fun k : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree c.outerWord.val c.slot i + 1) =>
    (c.outerGrid i + k.val, c.innerGrid i))

/-- 概要：実際の垂直成分の全格子座標（BF §1.5.7）。
方針：内側始行から成分次数だけ連続して進む。
規約：外側座標は次の出現境界の所属行に固定する。
使われ方：実際の垂直行列を経路座標へ比較する。 -/
def verticalGridVertices {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    List (ℕ × ℕ) :=
  List.ofFn (fun k : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree c.innerWord.val c.cuts i + 1) =>
    (c.outerGrid (i.val + 1), c.innerGrid i.val + k.val))

/-- 概要：水平成分の実際の行列は全格子座標への元の置換部分合成（BF §1.5.7）。
方針：元の外側置換区間の各位置を範囲内の rowAtGrid と同定する。
規約：元の成功表に基づく座標だけを評価する。
使われ方：全融合行列を成分座標列の map にする。 -/
lemma horizontalRows_eq_grid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    (c.horizontalRows i).map Prod.fst = (c.horizontalGridVertices i).map c.rowAtGrid := by
  have ha : c.outerGrid i + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree c.outerWord.val c.slot i + 1) ≤ d + 1 := by
    have hs := c.outerGrid_step i
    have hb := c.outerGrid_le (i + 1)
    omega
  rw [c.horizontalRows_fst]
  change (((List.ofFn c.outer).drop (c.outerGrid i)).take
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree c.outerWord.val c.slot i + 1)).map _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.map_ofFn_slice c.outer _ _ _ ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalGridVertices, List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  have hv := c.rowAtGrid_valid
    ⟨c.outerGrid i + k.val, by have := k.isLt; omega⟩
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.inner c.innerSchedule c.innerWord.val c.inner_success (c.innerPosition i))
  exact hv.symm

/-- 概要：垂直成分の実際の行列は全格子座標への元の置換部分合成（BF §1.5.7）。
方針：元の内側置換区間の各位置を範囲内の rowAtGrid と同定する。
規約：元の成功表に基づく座標だけを評価する。
使われ方：全融合行列を成分座標列の map にする。 -/
lemma verticalRows_eq_grid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    (c.verticalRows i).map Prod.fst = (c.verticalGridVertices i).map c.rowAtGrid := by
  have ha : c.innerGrid i.val + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree c.innerWord.val c.cuts i + 1) ≤ e + 1 := by
    have hs := c.innerGrid_step i
    have hb := c.innerGrid_le (i.val + 1)
    omega
  rw [c.verticalRows_fst]
  change (((List.ofFn c.inner).drop (c.innerGrid i.val)).take
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree c.innerWord.val c.cuts i + 1)).map _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.map_ofFn_slice c.inner _ _ _ ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalGridVertices, List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  have hv := c.rowAtGrid_valid
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.outer c.outerSchedule c.outerWord.val c.outer_success
      (c.outerPosition (i.val + 1)))
    ⟨c.innerGrid i.val + k.val, by have := k.isLt; omega⟩
  exact hv.symm

end TableCompositionData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
