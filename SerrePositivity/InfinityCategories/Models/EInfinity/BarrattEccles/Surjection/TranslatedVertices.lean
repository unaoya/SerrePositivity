module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentVertices

/-!
模型。文献の定義との比較は後で
# 平行移動した水平・垂直の成分頂点列

概要：Berger–Fresse §1.5.4 の成分座標列を任意の元の所属行から開始する。
方針：座標対への平行移動と連続有限列の写像を比較する。
規約：共有頂点の前のコピーを省く。
使われ方：全経路の成分次数と元の境界行番号の更新を一致させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

/-- 概要：指定格子点から始まる水平成分の全頂点（BF §1.5.4）。
方針：水平座標だけを連続して増やす。
規約：両端を含む。
使われ方：元の水平成分の格子座標表示。 -/
def horizontalAt (x y h : ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun k : Fin (h + 1) => (x + k.val, y))

/-- 概要：指定格子点から始まる垂直成分の全頂点（BF §1.5.4）。
方針：垂直座標だけを連続して増やす。
規約：両端を含む。
使われ方：元の垂直成分の格子座標表示。 -/
def verticalAt (x y v : ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun k : Fin (v + 1) => (x, y + k.val))

/-- 概要：成分頂点列に適用する格子平行移動（BF §1.5.4）。
方針：両座標へ指定した始点を加える。
規約：次数を変えない。
使われ方：元の所属行へ全経路を移す。 -/
def shift (x y : ℕ) (z : ℕ × ℕ) : ℕ × ℕ := (x + z.1, y + z.2)

/-- 概要：水平成分の平行移動は開始点だけを変える（BF §1.5.4）。
方針：ofFn の各位置の加法の結合則を使う。
規約：元の成分次数は保つ。
使われ方：後続水平成分を元の境界座標へ置く。 -/
lemma map_horizontalAt (a b x y h : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift a b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt (a + x) (b + y) h := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt, List.map_ofFn, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift, Nat.add_assoc]

/-- 概要：垂直成分の平行移動は開始点だけを変える（BF §1.5.4）。
方針：ofFn の各位置の加法の結合則を使う。
規約：元の成分次数は保つ。
使われ方：後続垂直成分を元の境界座標へ置く。 -/
lemma map_verticalAt (a b x y v : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.verticalAt x y v).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift a b) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.verticalAt (a + x) (b + y) v := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.verticalAt, List.map_ofFn, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift, Nat.add_assoc]

/-- 概要：二回の平行移動は座標和による一回の平行移動（BF §1.5.4）。
方針：各頂点の座標の加法の結合則を使う。
規約：座標列は任意。
使われ方：経路の再帰的な連結の始点を計算する。 -/
lemma map_shift (a b x y : ℕ) (xs : List (ℕ × ℕ)) :
    (xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift x y)).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift a b) = xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift (a + x) (b + y)) := by
  rw [List.map_map]
  apply congrArg (fun f => xs.map f)
  funext z
  simp only [Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift, Nat.add_assoc]

/-- 概要：水平成分の最後の頂点は開始点に水平次数を足した点（BF §1.5.4）。
方針：ofFn の最終位置分離と dropLast を評価する。
規約：水平次数零も同じ式。
使われ方：成分列が空になった終端で共有終点を戻す。 -/
lemma horizontalAt_append_last (x y h : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h).dropLast ++ [(x + h, y)] := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt, List.ofFn_succ_last, List.dropLast_concat, Fin.val_last]

/-- 概要：水平成分の頂点列は非空（BF §1.5.4）。
方針：有限頂点数 h+1を使う。
規約：次数零なら一頂点。
使われ方：前の垂直成分との連結で dropLast を分配する。 -/
lemma horizontalAt_ne_nil (x y h : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h ≠ [] := by
  intro he
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt x y h).length = h + 1 := List.length_ofFn
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

/-- 概要：成分列の一段を平行移動した水平・垂直表示へ戻す（BF §1.5.4）。
方針：明示的な座標を零始点の成分へ書き換える。
規約：垂直から水平の順。
使われ方：全経路と元の融合格子列の再帰を合わせる。 -/
lemma blockVertices_cons (v h : ℕ) (xs : List (ℕ × ℕ)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices ((v, h) :: xs) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.verticalAt 0 0 v).dropLast ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt 0 v h).dropLast ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices xs).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.shift h v) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockVertices, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.verticalAt, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontalAt, Nat.zero_add]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath
