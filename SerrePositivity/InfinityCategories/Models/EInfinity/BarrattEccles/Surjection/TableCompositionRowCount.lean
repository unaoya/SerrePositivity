module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusionGeometry

/-!
模型。文献の定義との比較は後で
# 全共有行融合表の正しい行数

概要：Berger–Fresse §1.5.7 の全融合表の行数が合成次数＋1であることを証明する。
方針：後続表の行数を元の残り行次数の和で表し、各境界で一行ずつ減らす。
規約：次数零の成分と同じ行内の切断も含む。
使われ方：実際の合成の Schedule と経路上の置換列の長さを供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：融合済みの後続表の行数は内外の残り行次数の和＋1（BF §1.5.7）。
方針：水平・垂直次数の行番号差と二つの境界融合で帰納する。
規約：元の境界の lineRank を使い、行長の選択には依存しない。
使われ方：第零成分で全行数 d+e+1を得る。 -/
lemma fusedRows_remaining_length {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) : (c.fusedRows i).length =
      (d - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.outerWord.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot i)) +
      (e - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.innerWord.val (c.cuts.boundary i)) + 1 := by
  by_cases hlt : i < c.count
  · have hn := (c.fusedRows_nonempty_head (i + 1) (by omega)).1
    have hh : c.horizontalRows i ≠ [] := by
      have := c.horizontalRows_length i
      intro he; rw [he] at this; simp only [List.length_nil] at this; omega
    have hv : c.verticalRows ⟨i, hlt⟩ ≠ [] := by
      have := c.verticalRows_length ⟨i, hlt⟩
      intro he; rw [he] at this; simp only [List.length_nil] at this; omega
    have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_ne_nil _ _ hv hn
    have h1 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_length (c.verticalRows ⟨i, hlt⟩) (c.fusedRows (i + 1)) hv hn
    have h2 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_length (c.horizontalRows i)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary (c.verticalRows ⟨i, hlt⟩) (c.fusedRows (i + 1))) hh hm
    have hnext := c.fusedRows_remaining_length (i + 1) (by omega)
    have hhor := c.horizontalRows_length i
    have hver := c.verticalRows_length ⟨i, hlt⟩
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree] at hhor
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree_eq_boundary c.innerWord.val c.cuts c.inner_positive] at hver
    change (c.verticalRows ⟨i, hlt⟩).length =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.innerWord.val (c.cuts.boundary (i + 1)) -
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.innerWord.val (c.cuts.boundary i) + 1 at hver
    have hao := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono c.outerWord.val)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_mono c.outerWord.val c.slot (show i ≤ i + 1 by omega))
    have hai := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono c.innerWord.val)
      (c.cuts.boundary_mono c.inner_positive (show i ≤ i + 1 by omega))
    have hbo : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.outerWord.val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot (i + 1)) ≤ d := by
      have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.outer c.outerSchedule c.outerWord.val c.outer_success
        (c.outerPosition (i + 1))).isLt
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.outerWord.val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot (i + 1)) < d + 1 at h
      omega
    have hbi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.innerWord.val (c.cuts.boundary (i + 1)) ≤ e := by
      have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.inner c.innerSchedule c.innerWord.val c.inner_success
        (c.innerPosition (i + 1))).isLt
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.innerWord.val (c.cuts.boundary (i + 1)) < e + 1 at h
      omega
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_left hlt]
    omega
  · have he : i = c.count := by omega
    subst i
    have hoe : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.outerWord.val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot (c.count + 1)) = d := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_last, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_last]
    have hie : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.innerWord.val (c.cuts.boundary c.count) = e := by
      rw [c.cuts.boundary_last, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_last]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_right (Nat.lt_irrefl _), c.horizontalRows_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree,
      hoe, hie, Nat.sub_self, Nat.add_zero]
termination_by c.count - i
decreasing_by omega

/-- 概要：全共有行を融合した表の行数は合成次数＋1（BF §1.5.7）。
方針：第零成分で両方の開始行番号を零に戻す。
規約：実際の融合行列についての等式。
使われ方：有限頂点添字と実際の合成 Schedule の行数を合わせる。 -/
lemma fusedRows_length {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    (c.fusedRows 0).length = d + e + 1 := by
  have hz := c.cuts.boundaryPosition_zero c.inner_positive
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos c.outerWord c.slot)
  change c.cuts.boundary 0 = 0 at hz
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_zero, hz, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_zero, Nat.sub_zero] using
    c.fusedRows_remaining_length 0 (Nat.zero_le _)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
