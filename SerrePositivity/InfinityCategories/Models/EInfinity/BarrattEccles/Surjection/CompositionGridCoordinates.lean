module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionRowProjection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentVertices

/-!
模型。文献の定義との比較は後で
# 元の所属行が指定する合成表の格子座標

概要：Berger–Fresse §1.5.7 の元の二つの成功表から各成分境界の実際の格子座標を取る。
方針：出現境界・分割境界の lineRank を使い、成分次数を隣接座標差へ戻す。
規約：自然数座標を使い、元の有限行数以下であることを証明する。
使われ方：連続置換の部分合成行列と実際の経路座標列の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：第 i 成分境界の元の外側所属行座標（BF §1.5.7）。
方針：外側語の出現境界の行番号を使う。
規約：元の外側成功表の有限行番号と同じ値。
使われ方：各水平成分の始点。 -/
def outerGrid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) : ℕ :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.outerWord.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary c.outerWord.val c.slot i)

/-- 概要：第 i 分割境界の元の内側所属行座標（BF §1.5.7）。
方針：内側語の分割境界の行番号を使う。
規約：元の内側成功表の有限行番号と同じ値。
使われ方：各水平成分で固定する内側座標。 -/
def innerGrid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) : ℕ :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank c.innerWord.val (c.cuts.boundary i)

/-- 概要：外側の境界座標は元の次数以下（BF §1.5.7）。
方針：元の有限所属行の上界を自然数へ移す。
規約：全自然数の成分番号で成立。
使われ方：自然数格子から元の有限置換列を評価する。 -/
lemma outerGrid_le {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    c.outerGrid i ≤ d := by
  have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.outer c.outerSchedule c.outerWord.val c.outer_success
    (c.outerPosition i)).isLt
  change c.outerGrid i < d + 1 at h
  omega

/-- 概要：内側の境界座標は元の次数以下（BF §1.5.7）。
方針：元の有限所属行の上界を自然数へ移す。
規約：正の内側語長により全境界を評価できる。
使われ方：自然数格子から元の有限置換列を評価する。 -/
lemma innerGrid_le {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    c.innerGrid i ≤ e := by
  have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.inner c.innerSchedule c.innerWord.val c.inner_success
    (c.innerPosition i)).isLt
  change c.innerGrid i < e + 1 at h
  omega

/-- 概要：水平次数だけ進むと次の外側境界座標になる（BF §1.5.7）。
方針：単調な行番号の差に元の始点を加える。
規約：次数零なら同じ座標。
使われ方：成分経路の平行移動を元の所属行へ一致させる。 -/
lemma outerGrid_step {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    c.outerGrid i + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree c.outerWord.val c.slot i = c.outerGrid (i + 1) := by
  have hm := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono c.outerWord.val)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_mono c.outerWord.val c.slot (show i ≤ i + 1 by omega))
  change c.outerGrid i ≤ c.outerGrid (i + 1) at hm
  change c.outerGrid i + (c.outerGrid (i + 1) - c.outerGrid i) = _
  omega

/-- 概要：垂直次数だけ進むと次の内側境界座標になる（BF §1.5.7）。
方針：分割境界の単調性と成分次数の差表示を使う。
規約：最後の垂直成分も含む。
使われ方：成分経路の平行移動を元の所属行へ一致させる。 -/
lemma innerGrid_step {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    c.innerGrid i.val + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree c.innerWord.val c.cuts i = c.innerGrid (i.val + 1) := by
  have hm := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono c.innerWord.val)
    (c.cuts.boundary_mono c.inner_positive (show i.val ≤ i.val + 1 by omega))
  change c.innerGrid i.val ≤ c.innerGrid (i.val + 1) at hm
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree_eq_boundary c.innerWord.val c.cuts c.inner_positive i]
  change c.innerGrid i.val + (c.innerGrid (i.val + 1) - c.innerGrid i.val) = _
  omega

/-- 概要：自然数座標から元の置換部分合成の行を評価する（BF §1.5.7）。
方針：元の置換列のリストの getD を使い、範囲内では元の置換をそのまま返す。
規約：範囲外の既定値は単位置換。主経路では上界を証明した座標だけを使う。
使われ方：自然数座標列に map して実際の行列と比較する。 -/
def rowAtGrid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (z : ℕ × ℕ) :
    List (Fin (m + n)) :=
  List.ofFn (permutationComposition m n c.slot
    ((List.ofFn c.outer).getD z.1 1) ((List.ofFn c.inner).getD z.2 1)).symm

/-- 概要：範囲内の格子座標の行は元の二つの置換の実際の部分合成（BF §1.5.7）。
方針：有限位置でのリスト評価を元の置換へ戻す。
規約：範囲外の既定値は使わない。
使われ方：実際の経路座標と元の合成単体の頂点を照合する。 -/
lemma rowAtGrid_valid {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (x : Fin (d + 1)) (y : Fin (e + 1)) : c.rowAtGrid (x.val, y.val) =
      List.ofFn (permutationComposition m n c.slot (c.outer x) (c.inner y)).symm := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.rowAtGrid, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left x.isLt, dite_eq_left y.isLt, Option.getD_some]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
