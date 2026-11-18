module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionSchedule

/-!
模型。文献の定義との比較は後で
# 融合表の行の列を元の連続置換で表示する

概要：Berger–Fresse §1.5.7 の行長を忘れた合成行列を、元の内外の連続した置換列へ戻す。
方針：成分の重み付き頂点の第一射影と境界融合の行順保存を使う。
規約：成分抽出証明書の古典選択を評価しない。
使われ方：compositionPath 上の実際の合成置換の頂点列と照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：水平ブロックの行列は元の連続外側置換の実際の部分合成（BF §1.5.7）。
方針：重み付き頂点の第一射影を元の頂点区間へ戻す。
規約：内側は同じ分割境界の元の所属行で固定する。
使われ方：経路の各水平部分の全頂点を照合する。 -/
lemma horizontalRows_fst {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : ℕ) :
    (c.horizontalRows i).map Prod.fst =
      (((List.ofFn c.outer).drop
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.outer c.outerSchedule c.outerWord.val c.outer_success
          (c.outerPosition i)).val).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree c.outerWord.val c.slot i + 1)).map
        (fun σ => List.ofFn (permutationComposition m n c.slot σ
          (c.inner (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.inner c.innerSchedule c.innerWord.val c.inner_success
            (c.innerPosition i)))).symm) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows_fst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.weightedVertices_fst]
  rfl

/-- 概要：垂直ブロックの行列は元の連続内側置換の実際の部分合成（BF §1.5.7）。
方針：重み付き頂点の第一射影を元の頂点区間へ戻す。
規約：外側は同じ指定出現の元の所属行で固定する。
使われ方：経路の各垂直部分の全頂点を照合する。 -/
lemma verticalRows_fst {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    (c.verticalRows i).map Prod.fst =
      (((List.ofFn c.inner).drop
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.inner c.innerSchedule c.innerWord.val c.inner_success
          (c.innerPosition i.val)).val).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree c.innerWord.val c.cuts i + 1)).map
        (fun τ => List.ofFn (permutationComposition m n c.slot
          (c.outer (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow c.outer c.outerSchedule c.outerWord.val c.outer_success
            (c.outerPosition (i.val + 1)))) τ).symm) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows_fst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.weightedVertices_fst]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.innerPosition, c.cuts.boundaryPosition_at]
  rfl

/-- 概要：全融合表の行順は元の水平・垂直・後続の境界一行削除の連結（BF §1.5.7）。
方針：両種類の実際の境界融合の第一射影を順に適用する。
規約：左の共有頂点を残し、右の先頭一行を省く。
使われ方：成分経路の頂点列の連結と全融合表を同じ再帰で比較する。 -/
lemma fusedRows_fst_step {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) (i : Fin c.count) :
    (c.fusedRows i.val).map Prod.fst = (c.horizontalRows i.val).map Prod.fst ++
      ((c.verticalRows i).map Prod.fst ++ ((c.fusedRows (i.val + 1)).map Prod.fst).tail).tail := by
  have hh : c.horizontalRows i.val ≠ [] := by
    have := c.horizontalRows_length i.val
    intro he; rw [he] at this; simp only [List.length_nil] at this; omega
  have hv : c.verticalRows i ≠ [] := by
    have := c.verticalRows_length i
    intro he; rw [he] at this; simp only [List.length_nil] at this; omega
  have hn := (c.fusedRows_nonempty_head (i.val + 1) (by have := i.isLt; omega)).1
  have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_ne_nil _ _ hv hn
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_left i.isLt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_fst _ _ hh hm,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_fst _ _ hv hn]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
