module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalWordEndpoints
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionOccurrenceSteps

/-!
模型。文献の定義との比較は後で
# 全共有行を融合した表の出力と実際の合成語の一致

概要：Berger–Fresse §1.5.7 の全融合表が元の compositeWord を実際に抽出することを示す。
方針：最終水平から戻り、各垂直末尾を次の水平先頭で復元して実際の代入をつなぐ。
規約：元の二表の成功と正の内側語長だけを使い、経路行列の同定は別途行う。
使われ方：一般の TR 合成保存で使う正方向の合成表の実際の成功語。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

/-- 概要：前の指定出現直後の代入を間の語・垂直語・次の尾部へ分解（BF §1.5.7）。
方針：連続出現間の代入公式の未消費部分語を元の重なる分割へ戻す。
規約：前後の番号は連続する。
使われ方：全融合語の後続を同じ実際のリスト代入へ接続する。 -/
lemma substitute_after_occurrence_step {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i j : Fin c.count) (hij : j.val = i.val + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
        ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1))
        ((c.cuts.segments c.innerWord.val).drop j.val) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
        (((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1)).take
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val -
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1)))
        ((c.cuts.segments c.innerWord.val).drop j.val) ++ c.verticalWord j ++
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
            ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val + 1))
            ((c.cuts.segments c.innerWord.val).drop (j.val + 1)) := by
  have hp : ((c.cuts.segments c.innerWord.val).drop j.val).headD [] =
      c.cuts.segment c.innerWord.val j := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.headD_eq_head?_getD, List.head?_eq_getElem?,
      List.getElem?_drop, Nat.add_zero, List.getElem?_ofFn, dite_eq_left j.isLt,
      Option.getD_some]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_between_occurrences c.outerWord.val c.slot i j hij
    ((c.cuts.segments c.innerWord.val).drop j.val)
  simpa only [hp, List.tail_drop, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalWord] using h

/-- 概要：各指定出現の後続融合語は共有文字と実際の未消費代入（BF §1.5.7）。
方針：最後の水平を始点に、中間水平・垂直・後続を逆順に接続する。
規約：共有垂直末尾と水平先頭は同じ文字を一度だけ残す。
使われ方：最初の水平を付けて全融合語を compositeWord へ戻す。 -/
lemma blockWord_after_occurrence {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) : c.blockWord (i.val + 1) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n c.slot
        (c.innerWord.val (c.innerPosition (i.val + 1))) ::
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
        ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot i).val + 1))
        ((c.cuts.segments c.innerWord.val).drop (i.val + 1)) := by
  by_cases hlt : i.val + 1 < c.count
  · let j : Fin c.count := ⟨i.val + 1, hlt⟩
    have hh := c.middleHorizontal_dropLast i j rfl
    have hn := c.blockWord_after_occurrence j
    have hs := c.substitute_after_occurrence_step i j rfl
    have hv := c.verticalWord_append_endpoint j
    have hc : (c.verticalWord j).dropLast ++
        _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n c.slot
          (c.innerWord.val (c.innerPosition (j.val + 1))) ::
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
            ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val + 1))
            ((c.cuts.segments c.innerWord.val).drop (j.val + 1)) =
        c.verticalWord j ++
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
            ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val + 1))
            ((c.cuts.segments c.innerWord.val).drop (j.val + 1)) := by
      rw [← List.singleton_append, ← List.append_assoc, ← hv]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.blockWord, dite_eq_left hlt]
    change (c.horizontalWord j.val).dropLast ++ (c.verticalWord j).dropLast ++
      c.blockWord (j.val + 1) = _
    rw [hh, hn]
    simp only [List.cons_append, List.append_assoc]
    rw [hc]
    apply congrArg (List.cons _)
    simpa only [List.append_assoc, j] using hs.symm
  · have he : i.val + 1 = c.count := by have := i.isLt; omega
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.blockWord, dite_eq_right (Nat.lt_irrefl _), c.finalHorizontal_word i he]
termination_by c.count - (i.val + 1)
decreasing_by omega

/-- 概要：全融合表の成分語表示は実際の compositeWord に一致（BF §1.5.7）。
方針：最初の水平以前の代入と後続代入を、最初の垂直語の共有末尾で接続する。
規約：正の内側語長。元の二表の成功以外に合成の成功を仮定しない。
使われ方：実際の全融合表の成功出力を元の合成語へ同定する。 -/
lemma blockWord_eq_compositeWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    c.blockWord 0 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts := by
  let j : Fin c.count := ⟨0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos c.outerWord c.slot⟩
  have hv := c.verticalWord_append_endpoint j
  have hc : (c.verticalWord j).dropLast ++
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n c.slot
        (c.innerWord.val (c.innerPosition (j.val + 1))) ::
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
          ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val + 1))
          ((c.cuts.segments c.innerWord.val).drop (j.val + 1)) =
      c.verticalWord j ++
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute c.slot
          ((List.ofFn c.outerWord.val).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt c.outerWord.val c.slot j).val + 1))
          ((c.cuts.segments c.innerWord.val).drop (j.val + 1)) := by
    rw [← List.singleton_append, ← List.append_assoc, ← hv]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.blockWord, dite_eq_left (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos c.outerWord c.slot),
    c.firstHorizontal_dropLast, c.blockWord_after_occurrence j]
  rw [List.append_assoc, hc]
  simpa only [List.append_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalWord, j] using
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_at_occurrence c.outerWord c.innerWord c.slot c.cuts j).symm

/-- 概要：元の二表から作った全共有行融合表は実際の合成語を返す（BF §1.5.7）。
方針：融合表の実際の成功と成分語の全体の一致を合わせる。
規約：経路上の元の合成置換列との同定は別途必要。
使われ方：一般の TR 合成保存の正方向で使う具体的な成功表。 -/
lemma fused_success_compositeWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (c.fusedRows 0) [] =
      some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.outerWord c.innerWord c.slot c.cuts) := by
  rw [← c.blockWord_eq_compositeWord]
  exact c.fused_success_blockWord

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
