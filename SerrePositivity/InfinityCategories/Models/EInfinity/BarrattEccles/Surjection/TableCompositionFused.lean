module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionRaw
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionJoins
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusionBoundary

/-!
模型。文献の定義との比較は後で
# 全共有行を融合した実際の合成表

概要：Berger–Fresse §1.5.7 の交互成分列の全境界を融合し、元の二つの成功から成功を構成する。
方針：後続から垂直・水平の順に融合し、先頭行の保存で次の共有境界へ接続する。
規約：合成経路・合成語への照合は別途行い、ここでは実際の融合行列と削除出力を使う。
使われ方：経路上の表と一般の TR 合成保存を照合する成功表。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：全ての共有境界を融合した実際の成分行列（BF §1.5.7）。
方針：次の水平以降を構成し、垂直・水平の共有行を順に融合する。
規約：最後は最終水平成分。
使われ方：全ての共有頂点を一つずつ持つ成功表。 -/
noncomputable def fusedRows {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) : List (List (Fin (m + n)) × ℕ) :=
  if hi : i < c.count then
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary (c.horizontalRows i)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary (c.verticalRows ⟨i, hi⟩) (c.fusedRows (i + 1)))
  else c.horizontalRows c.count
termination_by c.count - i
decreasing_by omega

/-- 概要：全共有行の融合で各共有出力の前のコピーを消した実際の語（BF §1.5.7）。
方針：実際のブロックの境界位置で垂直・水平の順に一文字を消す。
規約：既存の compositeWord への同定はまだ要求しない。
使われ方：融合した全表の実際の成功出力。 -/
noncomputable def fusedWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) : List (Fin (m + n)) :=
  if hi : i < c.count then
    (c.horizontalWord i ++
      (c.verticalWord ⟨i, hi⟩ ++ c.fusedWord (i + 1)).eraseIdx
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex (c.verticalRows ⟨i, hi⟩))).eraseIdx
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex (c.horizontalRows i))
  else c.horizontalWord c.count
termination_by c.count - i
decreasing_by omega

/-- 概要：融合した全後続表は非空で、最初の水平の先頭行を保つ（BF §1.5.7）。
方針：元のブロックの正の行数と各境界融合の先頭保存を使う。
規約：成分次数零も含む。
使われ方：前の垂直ブロックとの共有行を元の接続定理へ戻す。 -/
lemma fusedRows_nonempty_head {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) : c.fusedRows i ≠ [] ∧
      ((c.fusedRows i).map Prod.fst).head? = ((c.horizontalRows i).map Prod.fst).head? := by
  have hh : c.horizontalRows i ≠ [] := by
    have := c.horizontalRows_length i
    intro he; rw [he] at this; simp only [List.length_nil] at this; omega
  by_cases hlt : i < c.count
  · have hv : c.verticalRows ⟨i, hlt⟩ ≠ [] := by
      have := c.verticalRows_length ⟨i, hlt⟩
      intro he; rw [he] at this; simp only [List.length_nil] at this; omega
    have hn := (c.fusedRows_nonempty_head (i + 1) (by omega)).1
    have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_ne_nil (c.verticalRows ⟨i, hlt⟩) (c.fusedRows (i + 1)) hv hn
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_left hlt]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_ne_nil _ _ hh hm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_head _ _ hh hm⟩
  · have he : i = c.count := by omega
    subst i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_right (Nat.lt_irrefl _)]
    exact ⟨hh, rfl⟩
termination_by c.count - i
decreasing_by omega

/-- 概要：全共有行を融合した実際の表の成功（BF §1.5.7）。
方針：後続成功へ垂直転送・境界融合、水平転送・境界融合を順に適用する。
規約：元の二つの成功以外に合成の成功を入力にしない。
使われ方：融合後の行列と語を経路・compositeWord へ同定する。 -/
lemma fused_success {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (c.fusedRows i) (c.state i) = some (c.fusedWord i) := by
  by_cases hlt : i < c.count
  · have hnext := c.fused_success (i + 1) (by omega)
    have hn := c.fusedRows_nonempty_head (i + 1) (by omega)
    have hh : c.horizontalRows i ≠ [] := by
      have := c.horizontalRows_length i
      intro he; rw [he] at this; simp only [List.length_nil] at this; omega
    have hv : c.verticalRows ⟨i, hlt⟩ ≠ [] := by
      have := c.verticalRows_length ⟨i, hlt⟩
      intro he; rw [he] at this; simp only [List.length_nil] at this; omega
    have hjv : ((c.verticalRows ⟨i, hlt⟩).map Prod.fst).getLast? =
        ((c.fusedRows (i + 1)).map Prod.fst).head? := by
      rw [hn.2]
      exact c.vertical_horizontal_join ⟨i, hlt⟩
    have hvt := c.vertical_transfer ⟨i, hlt⟩ _ _ hnext
    have hvf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_in_context [] (c.verticalRows ⟨i, hlt⟩)
      (c.fusedRows (i + 1)) [] (c.betweenState i)
      (c.verticalWord ⟨i, hlt⟩ ++ c.fusedWord (i + 1)) hv hn.1
      (c.verticalRows_nodup ⟨i, hlt⟩) hjv
      (by simpa only [List.nil_append, List.append_nil] using hvt)
    simp only [List.nil_append, List.append_nil, List.map_nil, List.sum_nil, Nat.zero_add] at hvf
    have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_ne_nil _ _ hv hn.1
    have hjh : ((c.horizontalRows i).map Prod.fst).getLast? =
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary (c.verticalRows ⟨i, hlt⟩) (c.fusedRows (i + 1))).map Prod.fst).head? := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_head _ _ hv hn.1]
      exact c.horizontal_vertical_join ⟨i, hlt⟩
    have hht := c.horizontal_transfer ⟨i, hlt⟩ _ _ hvf
    have hhf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_in_context [] (c.horizontalRows i)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary (c.verticalRows ⟨i, hlt⟩) (c.fusedRows (i + 1))) [] (c.state i)
      _ hh hm (c.horizontalRows_nodup i) hjh
      (by simpa only [List.nil_append, List.append_nil] using hht)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_left hlt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedWord, dite_eq_left hlt]
    simpa only [List.nil_append, List.append_nil, List.map_nil, List.sum_nil, Nat.zero_add]
      using hhf
  · have he : i = c.count := by omega
    subst i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_right (Nat.lt_irrefl _), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedWord,
      dite_eq_right (Nat.lt_irrefl _)]
    simpa only [List.append_nil] using c.final_transfer [] [] rfl
termination_by c.count - i
decreasing_by omega

/-- 概要：全共有行を融合した表は空の除外状態から成功する（BF §1.5.7）。
方針：第零成分の始状態を元の二つの空の始状態へ戻す。
規約：実際の融合出力を返す。
使われ方：経路表と合成語への照合の出発点。 -/
lemma fused_success_zero {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (c.fusedRows 0) [] = some (c.fusedWord 0) := by
  simpa only [c.state_zero] using c.fused_success 0 (Nat.zero_le _)

/-- 概要：融合で消す水平境界の位置は水平出力の最終位置（BF §1.5.7）。
方針：任意の後続への水平転送を空の後続に適用する。
規約：最後の水平も含む。
使われ方：実際の行長による削除位置を成分語だけの式へ移す。 -/
lemma horizontal_boundaryIndex {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex (c.horizontalRows i) = (c.horizontalWord i).length - 1 := by
  have hn : c.horizontalRows i ≠ [] := by
    have := c.horizontalRows_length i
    intro he; rw [he] at this; simp only [List.length_nil] at this; omega
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex_of_success _ (c.state i) _ hn
  by_cases hlt : i < c.count
  · simpa only [List.append_nil] using c.horizontal_transfer ⟨i, hlt⟩ [] [] rfl
  · have he : i = c.count := by omega
    subst i
    simpa only [List.append_nil] using c.final_transfer [] [] rfl

/-- 概要：融合で消す垂直境界の位置は垂直出力の最終位置（BF §1.5.7）。
方針：任意の後続への垂直転送を空の後続に適用する。
規約：次数零の垂直も含む。
使われ方：削除位置を元の部分語の長さで計算する。 -/
lemma vertical_boundaryIndex {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex (c.verticalRows i) = (c.verticalWord i).length - 1 := by
  have hn : c.verticalRows i ≠ [] := by
    have := c.verticalRows_length i
    intro he; rw [he] at this; simp only [List.length_nil] at this; omega
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.boundaryEraseIndex_of_success _ (c.betweenState i.val) _ hn
  simpa only [List.append_nil] using c.vertical_transfer i [] [] rfl

/-- 概要：融合語の一段は元の成分語の境界文字の削除だけで計算できる（BF §1.5.7）。
方針：実際の行長から得た二つの削除位置を成分語の最終位置へ同定する。
規約：古典選択で作った成分の行長自体を計算する必要はない。
使われ方：融合語と実際の合成語の照合および具体例の監査。 -/
lemma fusedWord_step {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) : c.fusedWord i.val =
    (c.horizontalWord i.val ++
      (c.verticalWord i ++ c.fusedWord (i.val + 1)).eraseIdx
        ((c.verticalWord i).length - 1)).eraseIdx ((c.horizontalWord i.val).length - 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedWord, dite_eq_left i.isLt, c.horizontal_boundaryIndex i.val (by omega),
    c.vertical_boundaryIndex i]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
