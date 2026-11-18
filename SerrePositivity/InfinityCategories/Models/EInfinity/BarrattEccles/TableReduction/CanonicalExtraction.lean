module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalFilteredRows

/-!
模型。文献の定義との比較は後で
# 標準行の指定した長さでの抽出と除外状態の更新

概要：Berger–Fresse §1.4.3 の正しい選択で元の語の一行が抽出されることを示す。
方針：残っている行の先頭は最終出現部分と区切り文字の連結である。
規約：区切り文字は出力に含めるが次の除外リストには加えない。
使われ方：全行の抽出の帰納法と非零項の一意性を組み立てる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定した行長で最終出現部分と区切り文字を抽出する（BF §1.4.3）。
方針：除外後の行の先頭部分と後続列の先頭一文字を読む。
規約：行長は finalSegment.length+1。
使われ方：抽出結果を元の語の対応する区間と同定する。 -/
lemma canonicalRows_selected_prefix {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))).take
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment v i).length + 1) =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment v i ++ [v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i)] := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_canonicalRow_start, List.take_append]
  rw [List.take_of_length_le (Nat.le_succ _), Nat.add_sub_cancel_left]
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val < (List.ofFn v.val).length := by
    simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).isLt
  rw [List.drop_eq_getElem_cons hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.firstOccurrences_cons]
  simp only [List.take_succ_cons, List.take_zero, List.getElem_ofFn, Fin.eta]

/-- 概要：正しい行長での抽出結果は元の語の一行（BF §1.4.3）。
方針：最終出現部分に区切り文字を加える take の式を比較する。
規約：出力は開始位置から区切り位置までの両端を含む区間。
使われ方：全行の抽出を元の全射語へ連結する。 -/
lemma canonicalRows_extract_original_segment {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))).take
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc + 1) =
      ((List.ofFn v.val).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc)).take
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc + 1) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment_length v i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRows_selected_prefix]
  have hstart := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_le_caesuraAt v i
  have hcut := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).isLt
  have hk : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc <
      ((List.ofFn v.val).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc)).length := by
    rw [List.length_drop, List.length_ofFn]
    omega
  have ht := List.take_concat_get'
    ((List.ofFn v.val).drop (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc) hk
  rw [List.getElem_drop, List.getElem_ofFn] at ht
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc + ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val := by omega
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment_length]
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment, hs, Fin.eta] using ht

/-- 概要：正しい行を抽出した後の除外リストは次行開始時の確定値（BF §1.4.3）。
方針：区切り文字を除く行の先頭部分だけを新たに除外する。
規約：区切り文字は後でも使うので除外しない。
使われ方：標準 table の全行の抽出と長さの一意性を帰納的に証明する。 -/
lemma canonicalRows_exclusion_update {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc) ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc))).take
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.succ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_canonicalRow_start, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.finalSegment_length v i, List.take_left,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ_eq_caesuraAt]
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val < (List.ofFn v.val).length := by
    simpa only [List.length_ofFn] using (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).isLt
  have ha : (List.ofFn v.val)[(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val] ∈
      (List.ofFn v.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val + 1) := by
    simpa only [List.getElem_ofFn, Fin.eta] using
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_iff_mem_drop v.val _).mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt_caesura v i)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals_succ_of_mem _ _ hp ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals_cut_eq_start_append]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
