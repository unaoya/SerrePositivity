module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TranslatedVertices

/-!
模型。文献の定義との比較は後で
# 任意の始点からの交互成分歩行と実際の経路頂点

概要：Berger–Fresse §1.5.4 の水平・垂直の交互歩行を、既存の実際の経路の頂点列へ同定する。
方針：成分次数列で帰納し、共有末尾を省いて後続を更新した始点へ移す。
規約：最後の水平成分は全頂点を残す。
使われ方：元の所属行更新を使って融合格子列と compositionPath を一致させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

/-- 概要：任意の始点から水平・垂直を交互に進む全頂点（BF §1.5.4）。
方針：各成分の共有末尾を省き、更新した座標から次の水平を開始する。
規約：対の第一成分は垂直、第二成分は次の水平次数。
使われ方：元の全融合格子座標と同じ再帰を持つ表示。 -/
def walkVertices (x y h : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h
  | (v, t) :: xs => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h).dropLast ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.verticalAt (x + h) y v).dropLast ++ walkVertices (x + h) (y + v) t xs

/-- 概要：交互成分歩行は最初の水平と既存の全成分経路の平行移動（BF §1.5.4）。
方針：成分列で帰納し、水平側が非空なので二重の共有末尾削除を分配する。
規約：任意の自然数始点から成立する。
使われ方：元の境界更新で得た融合座標を compositionPath へ戻す。 -/
lemma walkVertices_eq_blocks (x y h : ℕ) (xs : List (ℕ × ℕ)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.walkVertices x y h xs = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h).dropLast ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices xs).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift (x + h) y) := by
  induction xs generalizing x y h with
  | nil =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.walkVertices, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices]
    simp only [List.map_cons, List.map_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift, Nat.add_zero]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt_append_last x y h
  | cons pair xs ih =>
    obtain ⟨v, t⟩ := pair
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.walkVertices, ih]
    conv_rhs => rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices_cons]
    rw [List.dropLast_append_of_ne_nil (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt_ne_nil 0 v t)]
    simp only [List.map_append, List.map_dropLast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.map_verticalAt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.map_horizontalAt,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.map_shift, Nat.add_zero, List.append_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath
