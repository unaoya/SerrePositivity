module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SegmentDegrees

/-!
模型。文献の定義との比較は後で
# 重なる分割の成分端点が属す元の抽出行

概要：Berger–Fresse §1.5.7 の内側成分次数を元の成功表の実際の行区間へ同定する。
方針：分割の正の長さと全長の上界から有限端点を作り、成功表の reductionRow を適用する。
規約：この端点表示は正の語長に対するもの。空語は別途 nullary 合成で扱う。
使われ方：compositionPath の各垂直成分に元の表の開始行と終了行を与える。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

namespace OverlapPartition

/-- 概要：正の部分語の有限な開始位置（BF §1.5.7）。
方針：開始位置と正の部分長の和の上界を使う。
規約：元の語の長さは正。
使われ方：元の成功表の成分開始行を指定する。 -/
def startPosition {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) (i : Fin t) : Fin l :=
  ⟨r.start i, by have := r.start_add_length_le i; have := r.positive hl i; omega⟩

/-- 概要：正の部分語の有限な終了位置（BF §1.5.7）。
方針：開始位置＋部分長−1 が全長より小さいことを使う。
規約：終了位置は部分語に含める。
使われ方：元の成功表の成分終了行を指定する。 -/
def endPosition {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) (i : Fin t) : Fin l :=
  ⟨r.start i + (r.val i).val - 1, by
    have := r.start_add_length_le i; have := r.positive hl i; omega⟩

/-- 概要：同じ部分語の開始位置は終了位置以下（BF §1.5.7）。
方針：部分長が正であることを使う。
規約：一文字成分なら両端は同じ。
使われ方：元の行区間の順序を供給する。 -/
lemma startPosition_le_endPosition {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)
    (hl : 0 < l) (i : Fin t) : r.startPosition hl i ≤ r.endPosition hl i := by
  change r.start i ≤ r.start i + (r.val i).val - 1
  have := r.positive hl i
  omega

end OverlapPartition

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：内側成分の始行と終行は元の成功表で正しい順序を持つ（BF §1.5.7）。
方針：有限端点の順序を実際の所属行の単調性へ渡す。
規約：成分次数零なら同じ行に含まれる。
使われ方：候補経路の垂直成分を元の二行の間へ対応させる。 -/
lemma segment_reductionRow_le {n d t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + d)) (hl : 0 < n + d) (i : Fin t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (r.startPosition hl i) ≤
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (r.endPosition hl i) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow_mono w s v.val h (r.startPosition_le_endPosition hl i)

/-- 概要：成分次数は元の成功表の終行番号と始行番号の差（BF §1.5.7）。
方針：端点の行番号を実際の所属行と同定した定義を使う。
規約：両端を共有する成分の次数。
使われ方：候補経路の垂直辺数を実際の元の抽出行の移動回数へ接続する。 -/
lemma segmentDegree_eq_reductionRows {n d t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + d)) (hl : 0 < n + d) (i : Fin t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (r.endPosition hl i)).val -
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (r.startPosition hl i)).val := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
