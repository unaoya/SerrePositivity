module

public import SerrePositivity.EInfinity.Shuffle.PathCuts
public import SerrePositivity.EInfinity.Shuffle.Simplices
public import SerrePositivity.EInfinity.AlexanderWhitney.SimplicialCuts

/-!
# shuffle 単体の前半・後半の AW 切断

概要：Berger–Fresse §1.1.4 の AW 切断を二つの shuffle 項の切断へ同定する。
方針：切断した経路の座標と元の経路の座標を単体圏の射として比較する。
規約：切断点の頂点は前半と後半に共有する。
使われ方：shuffle と AW の有限和を添字替えする際の各項の等式。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Shuffle

open CategoryTheory MonoidalCategory BarrattEccles
open scoped Simplicial

/-- 概要：前半経路の水平写像と元の水平写像の切断との一致（Berger–Fresse §1.1.4）。
方針：前半の水平座標の公式を各頂点に適用する。
規約：入力の切断長は切断点の水平座標。
使われ方：shuffle 単体の前半の第一因子を比較する。 -/
lemma front_horizontalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (frontPath s k).horizontalMap ≫
        AlexanderWhitney.segmentMap 0 (s.horizontal k).val p (by omega) =
      AlexanderWhitney.segmentMap 0 ((s.horizontal k).val + (s.vertical k).val) (p + q)
        (by have hc := s.coordinate_sum k; omega) ≫ s.horizontalMap := by
  ext i : 3
  change Fin ((s.horizontal k).val + (s.vertical k).val + 1) at i
  apply Fin.ext
  change 0 + ((frontPath s k).horizontal i).val =
    (s.horizontal ⟨0 + i.val, by have hc := s.coordinate_sum k; omega⟩).val
  simpa only [zero_add] using frontPath_horizontal s k i

/-- 概要：前半経路の垂直写像と元の垂直写像の切断との一致（Berger–Fresse §1.1.4）。
方針：前半の垂直座標の公式を各頂点に適用する。
規約：入力の切断長は切断点の垂直座標。
使われ方：shuffle 単体の前半の第二因子を比較する。 -/
lemma front_verticalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (frontPath s k).verticalMap ≫
        AlexanderWhitney.segmentMap 0 (s.vertical k).val q (by omega) =
      AlexanderWhitney.segmentMap 0 ((s.horizontal k).val + (s.vertical k).val) (p + q)
        (by have hc := s.coordinate_sum k; omega) ≫ s.verticalMap := by
  ext i : 3
  change Fin ((s.horizontal k).val + (s.vertical k).val + 1) at i
  apply Fin.ext
  change 0 + ((frontPath s k).vertical i).val =
    (s.vertical ⟨0 + i.val, by have hc := s.coordinate_sum k; omega⟩).val
  simpa only [zero_add] using frontPath_vertical s k i

/-- 概要：後半経路の水平写像は切断点からの水平増分（Berger–Fresse §1.1.4）。
方針：後半の水平座標の公式を単体圏の射の等式へ移す。
規約：第一因子は切断点の水平座標から最後まで。
使われ方：shuffle 単体の後半の第一因子を比較する。 -/
lemma back_horizontalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (backPath s k).horizontalMap ≫
        AlexanderWhitney.segmentMap (s.horizontal k).val (p - (s.horizontal k).val) p (by omega) =
      AlexanderWhitney.segmentMap k.val ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
        (p + q) (by have hc := s.coordinate_sum k; omega) ≫ s.horizontalMap := by
  ext i : 3
  apply Fin.ext
  exact backPath_horizontal s k i

/-- 概要：後半経路の垂直写像は切断点からの垂直増分（Berger–Fresse §1.1.4）。
方針：後半の垂直座標の公式を単体圏の射の等式へ移す。
規約：第二因子は切断点の垂直座標から最後まで。
使われ方：shuffle 単体の後半の第二因子を比較する。 -/
lemma back_verticalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (backPath s k).verticalMap ≫
        AlexanderWhitney.segmentMap (s.vertical k).val (q - (s.vertical k).val) q (by omega) =
      AlexanderWhitney.segmentMap k.val ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
        (p + q) (by have hc := s.coordinate_sum k; omega) ≫ s.verticalMap := by
  ext i : 3
  apply Fin.ext
  exact backPath_vertical s k i

/-- 概要：shuffle 単体の前半 AW 切断は前半経路の shuffle（Berger–Fresse §1.1.4）。
方針：二つの座標写像の一致を反変関手で移す。
規約：両入力も切断点のそれぞれの座標まで切断する。
使われ方：AW と shuffle の余代数適合性の各項の前半。 -/
lemma simplex_frontCut (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (k : Fin (p + q + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    simplex X Y (frontPath s k)
        (AlexanderWhitney.cut X x 0 (s.horizontal k).val (by omega))
        (AlexanderWhitney.cut Y y 0 (s.vertical k).val (by omega)) =
      AlexanderWhitney.cut (X ⊗ Y) (simplex X Y s x y) 0
        ((s.horizontal k).val + (s.vertical k).val) (by have hc := s.coordinate_sum k; omega) := by
  apply Prod.ext
  · change X.map (frontPath s k).horizontalMap.op
        (X.map (AlexanderWhitney.segmentMap 0 (s.horizontal k).val p (by omega)).op x) =
      X.map (AlexanderWhitney.segmentMap 0
        ((s.horizontal k).val + (s.vertical k).val) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (X.map s.horizontalMap.op x)
    have he := congrArg (fun θ => X.map θ.op x) (front_horizontalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he
  · change Y.map (frontPath s k).verticalMap.op
        (Y.map (AlexanderWhitney.segmentMap 0 (s.vertical k).val q (by omega)).op y) =
      Y.map (AlexanderWhitney.segmentMap 0
        ((s.horizontal k).val + (s.vertical k).val) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (Y.map s.verticalMap.op y)
    have he := congrArg (fun θ => Y.map θ.op y) (front_verticalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he

/-- 概要：shuffle 単体の後半 AW 切断は後半経路の shuffle（Berger–Fresse §1.1.4）。
方針：二つの後半の座標写像の一致を反変関手で移す。
規約：両入力の後半はそれぞれの切断座標から最後まで。
使われ方：AW と shuffle の余代数適合性の各項の後半。 -/
lemma simplex_backCut (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (k : Fin (p + q + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    simplex X Y (backPath s k)
        (AlexanderWhitney.cut X x (s.horizontal k).val (p - (s.horizontal k).val) (by omega))
        (AlexanderWhitney.cut Y y (s.vertical k).val (q - (s.vertical k).val) (by omega)) =
      AlexanderWhitney.cut (X ⊗ Y) (simplex X Y s x y) k.val
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
        (by have hc := s.coordinate_sum k; omega) := by
  apply Prod.ext
  · change X.map (backPath s k).horizontalMap.op
        (X.map (AlexanderWhitney.segmentMap (s.horizontal k).val
          (p - (s.horizontal k).val) p (by omega)).op x) =
      X.map (AlexanderWhitney.segmentMap k.val
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (X.map s.horizontalMap.op x)
    have he := congrArg (fun θ => X.map θ.op x) (back_horizontalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he
  · change Y.map (backPath s k).verticalMap.op
        (Y.map (AlexanderWhitney.segmentMap (s.vertical k).val
          (q - (s.vertical k).val) q (by omega)).op y) =
      Y.map (AlexanderWhitney.segmentMap k.val
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (Y.map s.verticalMap.op y)
    have he := congrArg (fun θ => Y.map θ.op y) (back_verticalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he

end SerrePositivity.EInfinity.Shuffle
