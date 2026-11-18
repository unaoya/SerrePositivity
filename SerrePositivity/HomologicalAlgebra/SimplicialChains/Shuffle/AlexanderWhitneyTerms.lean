module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.SimplexCuts
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Components

/-!
# AW 対角と各 shuffle 項の切断

概要：Berger–Fresse §1.1.4 の AW と shuffle の適合性を一経路ごとに述べる。
方針：正規化 AW の生成元公式に前半・後半の shuffle 単体の切断公式を代入する。
規約：係数環は任意であり、符号付き和の添字替えはまだ行わない。
使われ方：経路の分割の全単射と符号公式を用いた余代数射性の証明。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：一経路の shuffle 項の AW 成分は前半・後半の shuffle 項のテンソル（Berger–Fresse §1.1.4）。
方針：AW の生成元公式と shuffle 単体の切断公式を使う。
規約：切断点の二座標が入力のそれぞれの切断点となる。
使われ方：shuffle と AW の余代数適合性の有限和の各項。 -/
lemma aw_component_simplex (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (k : Fin (p + q + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A (X ⊗ Y) (p + q)
        ((s.horizontal k).val + (s.vertical k).val)
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (by omega)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q) (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y)) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) ((s.horizontal k).val + (s.vertical k).val)
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k)
            (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 (s.horizontal k).val (by omega))
            (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y 0 (s.vertical k).val (by omega))) ⊗ₜ[A]
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y)
          ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k)
            (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x (s.horizontal k).val (p - (s.horizontal k).val) (by omega))
            (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y (s.vertical k).val (q - (s.vertical k).val) (by omega))) := by
  have hb : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut (X ⊗ Y) (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y)
      ((s.horizontal k).val + (s.vertical k).val)
      ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (by omega) =
        _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x (s.horizontal k).val (p - (s.horizontal k).val) (by omega))
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y (s.vertical k).val (q - (s.vertical k).val) (by omega)) := by
    have hseg : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap
        ((s.horizontal k).val + (s.vertical k).val)
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q) (by omega) =
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap k.val
          ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q)
          (by have hc := s.coordinate_sum k; omega) := by
      ext i : 3
      apply Fin.ext
      change ((s.horizontal k).val + (s.vertical k).val) + i.val = k.val + i.val
      rw [s.coordinate_sum k]
    change (X ⊗ Y).map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap
      ((s.horizontal k).val + (s.vertical k).val)
      ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q) (by omega)).op
      (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) = _
    rw [hseg]
    exact (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_backCut X Y s k x y).symm
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator, ← _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_frontCut, hb]

end SerrePositivity.SimplicialChains.Shuffle
