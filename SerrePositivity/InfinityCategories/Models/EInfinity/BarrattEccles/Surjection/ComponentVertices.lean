module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePathVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionPath

/-!
模型。文献の定義との比較は後で
# 成分次数から実際の経路の全頂点列を計算する

概要：Berger–Fresse §1.5.4 の全成分経路の頂点を計算可能な座標リストへ同定する。
方針：純粋な垂直・水平の頂点列を連結し、後続成分を終点座標だけ平行移動する。
規約：次数零の成分を含み、共有頂点は一度だけ残す。
使われ方：compositionPath と実際の全融合行列の連続置換表示の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

namespace DegreePath

/-- 概要：垂直から水平への成分経路の全頂点の明示式（BF §1.5.4）。
方針：実際の二経路の連結座標公式を適用する。
規約：折れ曲がりの共有頂点は水平側に残す。
使われ方：一成分での連続置換の頂点列と照合する。 -/
lemma vertices_corner (h v : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.corner h v) =
    (List.ofFn (fun k : Fin (v + 1) => (0, k.val))).dropLast ++
      List.ofFn (fun k : Fin (h + 1) => (k.val, v)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.corner, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_cast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_vertical, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_horizontal]
  simp only [Nat.zero_add, List.map_ofFn, Function.comp_def, Fin.val_cast, Nat.add_zero]

/-- 概要：成分次数対から全経路の頂点座標を直接計算する（BF §1.5.4）。
方針：一成分の座標列の共有末尾を省き、平行移動した後続座標を付ける。
規約：空の成分列は第零頂点だけを持つ。
使われ方：実際の経路の頂点列を元の次数データだけの式へ戻す。 -/
def blockVertices : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (v, h) :: xs =>
    ((List.ofFn (fun k : Fin (v + 1) => (0, k.val))).dropLast ++
      List.ofFn (fun k : Fin (h + 1) => (k.val, v))).dropLast ++
        (blockVertices xs).map (fun z => (h + z.1, v + z.2))

/-- 概要：全成分経路の実際の頂点列は成分次数だけの計算と一致（BF §1.5.4）。
方針：成分列で帰納し、実際の経路連結の全頂点公式を使う。
規約：有限辺集合や行長の選択を計算しない。
使われ方：compositionPath の全体を成分座標列へ移す。 -/
lemma vertices_blocks (xs : List (ℕ × ℕ)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blocks xs) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices xs := by
  induction xs with
  | nil =>
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blocks, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_horizontal]
    rfl
  | cons pair xs ih =>
    obtain ⟨v, h⟩ := pair
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blocks, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_corner, ih]
    rfl

end DegreePath

/-- 概要：実際の compositionPath の全頂点は内外成分次数からの連続座標列（BF §1.5.4）。
方針：総次数への移送を除き、最初の水平と全後続成分の連結を評価する。
規約：最初の水平の共有末尾は後続側に残す。
使われ方：融合表の全行の列と実際の shuffle 合成単体を比較する。 -/
lemma compositionPath_vertices {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath u v k r) =
      (List.ofFn (fun j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k 0 + 1) => (j.val, 0))).dropLast ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs u v k r)).map
          (fun z => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k 0 + z.1, z.2)) := by
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_cast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_append,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_horizontal, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices_blocks]
  simp only [Nat.zero_add]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
