module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionFused

/-!
模型。文献の定義との比較は後で
# 融合表の出力を元の成分語だけで表示する

概要：Berger–Fresse §1.5.7 の全融合出力を、成分の末尾を一つずつ省いた計算可能な語へ同定する。
方針：各成分の正の長さと、連結の左最終位置での削除を使う。
規約：古典選択した成分証明書の行長に依存しない。
使われ方：実際の成功表の出力とリスト代入による compositeWord の一般の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非空な左語の最終位置での削除はその末尾だけを除く（BF §1.5.7）。
方針：連結の削除位置を左語内へ制限する。
規約：右語は空でもよい。
使われ方：融合による一文字削除を成分語の dropLast に直す。 -/
lemma eraseLast_append {α : Type*} (left right : List α) (hl : left ≠ []) :
    (left ++ right).eraseIdx (left.length - 1) = left.dropLast ++ right := by
  have hp : 0 < left.length := List.length_pos_iff.mpr hl
  rw [List.eraseIdx_append, ite_eq_left (by omega), List.eraseIdx_eq_dropLast (by omega)]

namespace TableCompositionData

/-- 概要：水平語の長さは元の二出現境界間の位置差＋1（BF §1.5.7）。
方針：元の有限境界の上界と単調性で take の長さを評価する。
規約：全ての自然数成分番号で成立する。
使われ方：水平語が非空であることと融合出力の末尾削除。 -/
lemma horizontalWord_length {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    (c.horizontalWord i).length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot (i + 1) -
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot i + 1 := by
  have hp := (c.outerPosition i).isLt
  have hq := (c.outerPosition (i + 1)).isLt
  have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_mono c.outerWord.val c.slot (show i ≤ i + 1 by omega)
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot i < m + 1 + d at hp
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot (i + 1) < m + 1 + d at hq
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord, List.length_map, List.length_take,
    List.length_drop, List.length_ofFn]
  omega

/-- 概要：共有境界を持つ水平語は非空（BF §1.5.7）。
方針：閉区間の長さが一以上であることを使う。
規約：次数零の成分も含む。
使われ方：水平融合出力を dropLast へ直す。 -/
lemma horizontalWord_ne_nil {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    c.horizontalWord i ≠ [] := by
  intro he
  have hl := c.horizontalWord_length i
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

/-- 概要：正の内側語の各垂直語は非空（BF §1.5.7）。
方針：分割成分の実際の長さと正性を使う。
規約：一文字成分を許す。
使われ方：垂直融合出力を dropLast へ直す。 -/
lemma verticalWord_ne_nil {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    c.verticalWord i ≠ [] := by
  intro he
  have hl : (c.verticalWord i).length = (c.cuts.val i).val := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalWord, List.length_map, c.cuts.segment_length]
  have hp := c.cuts.positive c.inner_positive i
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

/-- 概要：共有文字の前のコピーを省いた元の全成分語（BF §1.5.7）。
方針：各水平・垂直の dropLast を交互に連結し、最終水平は全部残す。
規約：元の語と分割だけから計算し、行証明書の選択を使わない。
使われ方：全融合表の出力を既存のリスト代入へ照合する。 -/
def blockWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    List (Fin (m + n)) :=
  if hi : i < c.count then
    (c.horizontalWord i).dropLast ++ (c.verticalWord ⟨i, hi⟩).dropLast ++ c.blockWord (i + 1)
  else c.horizontalWord c.count
termination_by c.count - i
decreasing_by omega

/-- 概要：実際の全融合出力は元の成分語だけからの計算と一致（BF §1.5.7）。
方針：二つの実際の削除位置を成分の末尾に戻して再帰する。
規約：古典選択した行長の簡約は不要。
使われ方：全融合表の成功出力を compositeWord へ同定する。 -/
lemma fusedWord_eq_blockWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) : c.fusedWord i = c.blockWord i := by
  by_cases hlt : i < c.count
  · rw [c.fusedWord_step ⟨i, hlt⟩,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseLast_append _ _ (c.verticalWord_ne_nil ⟨i, hlt⟩),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseLast_append _ _ (c.horizontalWord_ne_nil i),
      c.fusedWord_eq_blockWord (i + 1) (by omega)]
    conv_rhs => rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.blockWord, dite_eq_left hlt]
    exact (List.append_assoc _ _ _).symm
  · have he : i = c.count := by omega
    subst i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedWord, dite_eq_right (Nat.lt_irrefl _), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.blockWord,
      dite_eq_right (Nat.lt_irrefl _)]
termination_by c.count - i
decreasing_by omega

/-- 概要：全融合表は元の成分語だけで計算した全出力を実際に返す（BF §1.5.7）。
方針：全融合成功の語を計算可能な成分列へ戻す。
規約：元の二つの成功表と分割だけを入力とする。
使われ方：一般の TR 合成保存で経路・代入語への照合に使う成功。 -/
lemma fused_success_blockWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (c.fusedRows 0) [] = some (c.blockWord 0) := by
  rw [← c.fusedWord_eq_blockWord 0 (Nat.zero_le _)]
  exact c.fused_success_zero

end TableCompositionData

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
