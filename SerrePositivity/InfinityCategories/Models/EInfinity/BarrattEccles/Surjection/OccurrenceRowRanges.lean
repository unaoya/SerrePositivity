module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterSegmentDegrees

/-!
模型。文献の定義との比較は後で
# 出現で切った外側成分の元の抽出行

概要：Berger–Fresse §1.5.7 の外側成分次数を実際の成功表の行区間へ同定する。
方針：出現境界を有限位置として保持し、語の lineRank を元の有限行添字へ移す。
規約：正の語長で始点・指定値の各出現・終点を全て含む。
使われ方：compositionPath の各水平成分に元の開始行と終了行を与える。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：出現で切る外側成分の有限境界位置（BF §1.5.7）。
方針：零・有効出現・語の終点の各分岐で語長未満を確認する。
規約：出現数以降の境界は終点で一定。
使われ方：元の成功表の外側成分の両端の行を指定する。 -/
def occurrenceBoundaryPosition {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (hl : 0 < l) (i : ℕ) : Fin l :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k i, by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary
    split_ifs with hzero hocc
    · exact hl
    · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k ⟨i - 1, hocc⟩).isLt
    · omega⟩

/-- 概要：外側成分の有限境界位置は単調（BF §1.5.7）。
方針：既存の自然数境界列の単調性を有限位置へ移す。
規約：一文字成分では両端が一致してよい。
使われ方：元の抽出の外側成分の行区間を順序付きにする。 -/
lemma occurrenceBoundaryPosition_mono {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (hl : 0 < l) : Monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v k hl) := by
  intro i j hij
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_mono v k hij

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：外側成分の始行と終行は元の成功表で順序を保つ（BF §1.5.7）。
方針：境界位置と元の所属行の二つの単調性を合成する。
規約：零次数の成分なら同じ行内に両端がある。
使われ方：候補経路の水平成分の元の行区間。 -/
lemma outerSegment_reductionRow_le {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (k : Fin n) (hl : 0 < n + d) (i : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v.val k hl i) ≤
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v.val k hl (i + 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow_mono w s v.val h
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition_mono v.val k hl (by omega)

/-- 概要：外側成分次数は元の成功表の終行番号と始行番号の差（BF §1.5.7）。
方針：成分端点の lineRank を実際の所属行と同定する。
規約：最初の成分と最後の成分も同じ式で扱う。
使われ方：候補経路の水平辺数を元の抽出行の移動回数へ接続する。 -/
lemma outerSegmentDegree_eq_reductionRows {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn v.val))
    (k : Fin n) (hl : 0 < n + d) (i : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree v.val k i =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v.val k hl (i + 1))).val -
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s v.val h (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundaryPosition v.val k hl i)).val := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
