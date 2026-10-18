module

public import SerrePositivity.EInfinity.BarrattEccles.ParallelShuffleSign
public import SerrePositivity.EInfinity.BarrattEccles.TripleShuffleCoordinates

/-!
# 並列の二段の shuffle の座標

概要：Berger–Fresse §1.1.3 の並列代入の添字替えが各入力の頂点を保存することを示す。
方針：右括弧の経路へ移し、外側の次数移送と内側の方向交換を計算する。
規約：第二・第三入力の役割を交換し、全頂点番号は値を保って移送する。
使われ方：並列合成の単体を各頂点の置換で比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：並列の添字替えは右括弧の外側の水平座標を保つ（Berger–Fresse §1.1.3）。
方針：外側の経路の辺数の移送の公式を使う。
規約：頂点番号の二回の移送を一回にまとめる。
使われ方：最初の入力の頂点を同定する。 -/
lemma parallelShuffle_right_horizontal (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin (p + q + r + 1)) :
    (tripleShuffleEquiv p r q (parallelShuffleEquiv p q r v)).1.horizontal
        (Fin.cast (by omega : p + r + q + 1 = p + (r + q) + 1)
          (Fin.cast (by omega : p + q + r + 1 = p + r + q + 1) a)) =
      (tripleShuffleEquiv p q r v).1.horizontal
        (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) a) := by
  rw [rightTriple_parallelShuffleEquiv]
  have h := shufflePathCastEquiv_horizontal (rfl : p = p) (Nat.add_comm q r)
    (tripleShuffleEquiv p q r v).1
    (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) a)
  simpa only [Fin.cast_cast, Fin.cast_refl, id_eq] using h

/-- 概要：並列の添字替えの右括弧の外側の垂直座標は辺数の交換で移る（Berger–Fresse §1.1.3）。
方針：辺数の等式による垂直座標の保存を使う。
規約：内側の頂点番号の型は q+r+1 から r+q+1 へ移送する。
使われ方：内側の二つの入力の頂点を同定する。 -/
lemma parallelShuffle_right_vertical (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin (p + q + r + 1)) :
    (tripleShuffleEquiv p r q (parallelShuffleEquiv p q r v)).1.vertical
        (Fin.cast (by omega : p + r + q + 1 = p + (r + q) + 1)
          (Fin.cast (by omega : p + q + r + 1 = p + r + q + 1) a)) =
      Fin.cast (by omega : q + r + 1 = r + q + 1)
        ((tripleShuffleEquiv p q r v).1.vertical
          (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) a)) := by
  rw [rightTriple_parallelShuffleEquiv]
  have h := shufflePathCastEquiv_vertical (rfl : p = p) (Nat.add_comm q r)
    (tripleShuffleEquiv p q r v).1
    (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) a)
  simpa only [Fin.cast_cast, Fin.cast_refl] using h

/-- 概要：並列の添字替えは最初の入力の座標を保つ（Berger–Fresse §1.1.3）。
方針：両方の三入力の座標の公式を右括弧の水平座標で比較する。
規約：最初の入力の次数 p は変わらない。
使われ方：並列合成の最初の入力の頂点の置換を同定する。 -/
lemma parallelShuffle_first_coordinate (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin (p + q + r + 1)) :
    v.2.horizontal (v.1.horizontal a) =
      (parallelShuffleEquiv p q r v).2.horizontal
        ((parallelShuffleEquiv p q r v).1.horizontal
          (Fin.cast (by omega : p + q + r + 1 = p + r + q + 1) a)) := by
  rw [tripleShuffle_first_coordinate, tripleShuffle_first_coordinate]
  exact (parallelShuffle_right_horizontal p q r v a).symm

/-- 概要：並列の添字替えは二番目の入力の座標を保つ（Berger–Fresse §1.1.3）。
方針：右括弧の内側の方向交換の垂直座標を使う。
規約：交換後には二番目の入力が外側の垂直座標で表される。
使われ方：並列合成の二番目の入力の頂点の置換を同定する。 -/
lemma parallelShuffle_second_coordinate (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin (p + q + r + 1)) :
    v.2.vertical (v.1.horizontal a) =
      (parallelShuffleEquiv p q r v).1.vertical
        (Fin.cast (by omega : p + q + r + 1 = p + r + q + 1) a) := by
  rw [tripleShuffle_second_coordinate, tripleShuffle_third_coordinate,
    parallelShuffle_right_vertical, rightTriple_parallelShuffleEquiv]
  rw [ShufflePath.exchange_vertical]

/-- 概要：並列の添字替えは三番目の入力の座標を保つ（Berger–Fresse §1.1.3）。
方針：右括弧の内側の方向交換の水平座標を使う。
規約：交換後には三番目の入力が内側の垂直座標で表される。
使われ方：並列合成の三番目の入力の頂点の置換を同定する。 -/
lemma parallelShuffle_third_coordinate (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin (p + q + r + 1)) :
    v.1.vertical a =
      (parallelShuffleEquiv p q r v).2.vertical
        ((parallelShuffleEquiv p q r v).1.horizontal
          (Fin.cast (by omega : p + q + r + 1 = p + r + q + 1) a)) := by
  rw [tripleShuffle_third_coordinate, tripleShuffle_second_coordinate,
    parallelShuffle_right_vertical, rightTriple_parallelShuffleEquiv]
  rw [ShufflePath.exchange_horizontal]

end SerrePositivity.EInfinity.BarrattEccles
