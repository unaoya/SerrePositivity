module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePathCoordinates

/-!
模型。文献の定義との比較は後で
# 実際の成分経路の頂点列と連結

概要：Berger–Fresse §1.5.4 の実際の経路の全頂点を座標対のリストとして表示する。
方針：有限頂点の列挙と前半・後半の座標公式を使う。
規約：連結では共有頂点の前のコピーだけを省く。
使われ方：元の連続置換の部分合成行列と経路の全頂点を比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：実際の格子経路の全頂点の自然数座標列（BF §1.5.4）。
方針：水平・垂直座標を同じ有限頂点順で列挙する。
規約：始点と終点を両方含む。
使われ方：経路の連結と元の行列の連結を同じリスト等式へ移す。 -/
def vertices {p q : ℕ} (a : ShufflePath p q) : List (ℕ × ℕ) :=
  List.ofFn (fun k => ((a.horizontal k).val, (a.vertical k).val))

/-- 概要：経路の辺数の等式による移送は頂点座標列を保つ（BF §1.5.4）。
方針：辺数の等式を消去する。
規約：自然数座標対を使うため座標の有限型の移送は残らない。
使われ方：compositionPath の総次数への移送を全頂点の照合から除く。 -/
lemma vertices_cast {p q r s : ℕ} (hp : p = r) (hq : q = s) (a : ShufflePath p q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (shufflePathCastEquiv hp hq a) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices a := by
  subst r s
  rfl

/-- 概要：連結経路の全頂点は前半末尾を省き、平行移動した後半を付けた列（BF §1.5.4）。
方針：各リスト添字を前半の辺数で分け、実際の連結座標公式へ戻す。
規約：共有切断頂点は後半の第零頂点として一度だけ残す。
使われ方：成分経路の頂点列を元の連続置換の連結に合わせる。 -/
lemma vertices_append {p q r s : ℕ} (a : ShufflePath p q) (b : ShufflePath r s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append a b) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices a).dropLast ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices b).map (fun z => (p + z.1, q + z.2)) := by
  apply List.ext_getElem
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices, List.length_ofFn, List.length_append, List.length_dropLast,
      List.length_map]
    omega
  · intro i hi hj
    have ha : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices a).dropLast.length = p + q := by
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices, List.length_dropLast, List.length_ofFn, Nat.add_sub_cancel]
    by_cases hf : i < p + q
    · rw [List.getElem_append_left (by rw [ha]; exact hf), List.getElem_dropLast]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices, List.getElem_ofFn]
      have hk : i < p + q + 1 := by omega
      exact Prod.ext (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append_horizontal_front a b ⟨i, hk⟩)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append_vertical_front a b ⟨i, hk⟩)
    · rw [List.getElem_append_right (by rw [ha]; omega)]
      simp only [ha, List.getElem_map]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices, List.getElem_ofFn]
      have hb : i - (p + q) < r + s + 1 := by
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices, List.length_ofFn] at hi
        omega
      have he : p + q + (i - (p + q)) = i := by omega
      have hx := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append_horizontal_back a b ⟨i - (p + q), hb⟩
      have hy := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append_vertical_back a b ⟨i - (p + q), hb⟩
      simp only [he] at hx hy
      exact Prod.ext hx hy

/-- 概要：純粋な水平経路の頂点列は水平座標の連続列（BF §1.5.4）。
方針：垂直座標の上界零と二座標の和の公式を使う。
規約：零辺の経路では始点だけ。
使われ方：各水平成分の連続外側置換との比較。 -/
lemma vertices_horizontal (p : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal p) =
    List.ofFn (fun k : Fin (p + 1) => (k.val, 0)) := by
  apply congrArg List.ofFn
  funext k
  have hs := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal p).coordinate_sum k
  have hv := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal p).vertical k).isLt
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal p).vertical k).val < 1 at hv
  apply Prod.ext <;> dsimp only <;> omega

/-- 概要：純粋な垂直経路の頂点列は垂直座標の連続列（BF §1.5.4）。
方針：水平座標の上界零と二座標の和の公式を使う。
規約：元の有限頂点型をそのまま使う。
使われ方：各垂直成分の連続内側置換との比較。 -/
lemma vertices_vertical (q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertical q) =
    List.ofFn (fun k : Fin (0 + q + 1) => (0, k.val)) := by
  apply congrArg List.ofFn
  funext k
  have hs := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertical q).coordinate_sum k
  have hh := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertical q).horizontal k).isLt
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertical q).horizontal k).val < 1 at hh
  apply Prod.ext <;> dsimp only <;> omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath
