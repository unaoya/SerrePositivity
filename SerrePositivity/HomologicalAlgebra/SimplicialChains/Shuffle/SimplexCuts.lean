module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.PathCuts
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Simplices
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplicialCuts

/-!
# shuffle 単体の前半・後半の AW 切断

概要：Berger–Fresse §1.1.4 の AW 切断を二つの shuffle 項の切断へ同定する。
方針：切断した経路の座標と元の経路の座標を単体圏の射として比較する。
規約：切断点の頂点は前半と後半に共有する。
使われ方：shuffle と AW の有限和を添字替えする際の各項の等式。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

/-- 概要：前半経路の水平写像と元の水平写像の切断との一致（Berger–Fresse §1.1.4）。
方針：前半の水平座標の公式を各頂点に適用する。
規約：入力の切断長は切断点の水平座標。
使われ方：shuffle 単体の前半の第一因子を比較する。 -/
lemma front_horizontalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).horizontalMap ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 (s.horizontal k).val p (by omega) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 ((s.horizontal k).val + (s.vertical k).val) (p + q)
        (by have hc := s.coordinate_sum k; omega) ≫ s.horizontalMap := by
  ext i : 3
  change Fin ((s.horizontal k).val + (s.vertical k).val + 1) at i
  apply Fin.ext
  change 0 + ((_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).horizontal i).val =
    (s.horizontal ⟨0 + i.val, by have hc := s.coordinate_sum k; omega⟩).val
  simpa only [zero_add] using _root_.SerrePositivity.SimplicialChains.Shuffle.frontPath_horizontal s k i

/-- 概要：前半経路の垂直写像と元の垂直写像の切断との一致（Berger–Fresse §1.1.4）。
方針：前半の垂直座標の公式を各頂点に適用する。
規約：入力の切断長は切断点の垂直座標。
使われ方：shuffle 単体の前半の第二因子を比較する。 -/
lemma front_verticalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).verticalMap ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 (s.vertical k).val q (by omega) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 ((s.horizontal k).val + (s.vertical k).val) (p + q)
        (by have hc := s.coordinate_sum k; omega) ≫ s.verticalMap := by
  ext i : 3
  change Fin ((s.horizontal k).val + (s.vertical k).val + 1) at i
  apply Fin.ext
  change 0 + ((_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).vertical i).val =
    (s.vertical ⟨0 + i.val, by have hc := s.coordinate_sum k; omega⟩).val
  simpa only [zero_add] using _root_.SerrePositivity.SimplicialChains.Shuffle.frontPath_vertical s k i

/-- 概要：後半経路の水平写像は切断点からの水平増分（Berger–Fresse §1.1.4）。
方針：後半の水平座標の公式を単体圏の射の等式へ移す。
規約：第一因子は切断点の水平座標から最後まで。
使われ方：shuffle 単体の後半の第一因子を比較する。 -/
lemma back_horizontalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).horizontalMap ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap (s.horizontal k).val (p - (s.horizontal k).val) p (by omega) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap k.val ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
        (p + q) (by have hc := s.coordinate_sum k; omega) ≫ s.horizontalMap := by
  ext i : 3
  apply Fin.ext
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.backPath_horizontal s k i

/-- 概要：後半経路の垂直写像は切断点からの垂直増分（Berger–Fresse §1.1.4）。
方針：後半の垂直座標の公式を単体圏の射の等式へ移す。
規約：第二因子は切断点の垂直座標から最後まで。
使われ方：shuffle 単体の後半の第二因子を比較する。 -/
lemma back_verticalMap {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).verticalMap ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap (s.vertical k).val (q - (s.vertical k).val) q (by omega) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap k.val ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
        (p + q) (by have hc := s.coordinate_sum k; omega) ≫ s.verticalMap := by
  ext i : 3
  apply Fin.ext
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.backPath_vertical s k i

/-- 概要：shuffle 単体の前半 AW 切断は前半経路の shuffle（Berger–Fresse §1.1.4）。
方針：二つの座標写像の一致を反変関手で移す。
規約：両入力も切断点のそれぞれの座標まで切断する。
使われ方：AW と shuffle の余代数適合性の各項の前半。 -/
lemma simplex_frontCut (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (k : Fin (p + q + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 (s.horizontal k).val (by omega))
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y 0 (s.vertical k).val (by omega)) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut (X ⊗ Y) (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) 0
        ((s.horizontal k).val + (s.vertical k).val) (by have hc := s.coordinate_sum k; omega) := by
  apply Prod.ext
  · change X.map (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).horizontalMap.op
        (X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 (s.horizontal k).val p (by omega)).op x) =
      X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0
        ((s.horizontal k).val + (s.vertical k).val) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (X.map s.horizontalMap.op x)
    have he := congrArg (fun θ => X.map θ.op x) (_root_.SerrePositivity.SimplicialChains.Shuffle.front_horizontalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he
  · change Y.map (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).verticalMap.op
        (Y.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 (s.vertical k).val q (by omega)).op y) =
      Y.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0
        ((s.horizontal k).val + (s.vertical k).val) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (Y.map s.verticalMap.op y)
    have he := congrArg (fun θ => Y.map θ.op y) (_root_.SerrePositivity.SimplicialChains.Shuffle.front_verticalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he

/-- 概要：shuffle 単体の後半 AW 切断は後半経路の shuffle（Berger–Fresse §1.1.4）。
方針：二つの後半の座標写像の一致を反変関手で移す。
規約：両入力の後半はそれぞれの切断座標から最後まで。
使われ方：AW と shuffle の余代数適合性の各項の後半。 -/
lemma simplex_backCut (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (k : Fin (p + q + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x (s.horizontal k).val (p - (s.horizontal k).val) (by omega))
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y (s.vertical k).val (q - (s.vertical k).val) (by omega)) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut (X ⊗ Y) (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) k.val
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
        (by have hc := s.coordinate_sum k; omega) := by
  apply Prod.ext
  · change X.map (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).horizontalMap.op
        (X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap (s.horizontal k).val
          (p - (s.horizontal k).val) p (by omega)).op x) =
      X.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap k.val
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (X.map s.horizontalMap.op x)
    have he := congrArg (fun θ => X.map θ.op x) (_root_.SerrePositivity.SimplicialChains.Shuffle.back_horizontalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he
  · change Y.map (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).verticalMap.op
        (Y.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap (s.vertical k).val
          (q - (s.vertical k).val) q (by omega)).op y) =
      Y.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap k.val
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q)
          (by have hc := s.coordinate_sum k; omega)).op (Y.map s.verticalMap.op y)
    have he := congrArg (fun θ => Y.map θ.op y) (_root_.SerrePositivity.SimplicialChains.Shuffle.back_verticalMap s k)
    simpa only [op_comp, Functor.map_comp_apply] using he

end SerrePositivity.SimplicialChains.Shuffle
