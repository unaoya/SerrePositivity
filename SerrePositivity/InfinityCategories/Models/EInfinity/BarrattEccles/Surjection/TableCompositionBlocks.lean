module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

/-!
模型。文献の定義との比較は後で
# 全合成表の実際の水平・垂直ブロック

概要：Berger–Fresse §1.5.7 の交互の成分列の各実際の合成行列と出力語を定義する。
方針：元の成功表から構成済みの成分の置換頂点と選択長さを使う。
規約：ブロックの共有頂点はこの段階では両方に残す。
使われ方：全表の成功を構成した後、共有行を融合して経路の頂点数へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：第 i 水平成分の実際の合成行列（BF §1.5.7）。
方針：内側境界の元の置換を固定して外側成分の元の頂点列を合成する。
規約：選択長さは元の外側成分の長さ。
使われ方：合成表の水平ブロック。 -/
noncomputable def horizontalRows {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    List (List (Fin (m + n)) × ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows
    (c.inner (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.inner c.innerSchedule c.innerWord.val c.inner_success
      (c.innerPosition i))) c.slot
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentExtraction c.outer c.outerSchedule c.outerWord c.outer_success c.slot
      (by omega) i).weightedVertices

/-- 概要：第 i 垂直成分の実際の合成行列（BF §1.5.7）。
方針：次の外側出現位置の元の置換を固定して内側成分の元の頂点列を合成する。
規約：選択長さは元の内側成分の長さ。
使われ方：合成表の垂直ブロック。 -/
noncomputable def verticalRows {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin c.count) : List (List (Fin (m + n)) × ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows
    (c.outer (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.outer c.outerSchedule c.outerWord.val c.outer_success
      (c.outerPosition (i.val + 1)))) c.slot
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction c.inner c.innerSchedule c.innerWord c.inner_success c.cuts
      c.inner_positive i).weightedVertices

/-- 概要：第 i 水平成分の合成ラベルでの出力語（BF §1.5.7）。
方針：指定値を内側境界の文字へ移す。
規約：共有文字をこの段階では両側のブロックに含める。
使われ方：全ブロックの成功出力を接続する。 -/
def horizontalWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    List (Fin (m + n)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerComponentWord c.outerWord.val c.slot i).map
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel c.slot (c.innerWord.val (c.innerPosition i)))

/-- 概要：第 i 垂直成分の挿入ラベルでの出力語（BF §1.5.7）。
方針：元の内側部分語を既存の挿入ラベルへ移す。
規約：共有端点を両方の成分に含める。
使われ方：全成分列の垂直ブロックの実際の出力。 -/
def verticalWord {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    List (Fin (m + n)) :=
  (c.cuts.segment c.innerWord.val i).map (insertedPosition m n c.slot)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
