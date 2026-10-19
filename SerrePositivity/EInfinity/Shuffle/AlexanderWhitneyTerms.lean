module

public import SerrePositivity.EInfinity.Shuffle.SimplexCuts
public import SerrePositivity.EInfinity.Shuffle.Components

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

namespace SerrePositivity.EInfinity.Shuffle

open CategoryTheory MonoidalCategory BarrattEccles
open scoped Simplicial TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：一経路の shuffle 項の AW 成分は前半・後半の shuffle 項のテンソル（Berger–Fresse §1.1.4）。
方針：AW の生成元公式と shuffle 単体の切断公式を使う。
規約：切断点の二座標が入力のそれぞれの切断点となる。
使われ方：shuffle と AW の余代数適合性の有限和の各項。 -/
lemma aw_component_simplex (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (k : Fin (p + q + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    AlexanderWhitney.component A (X ⊗ Y) (p + q)
        ((s.horizontal k).val + (s.vertical k).val)
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (by omega)
        (AlexanderWhitney.generator A (X ⊗ Y) (p + q) (simplex X Y s x y)) =
      AlexanderWhitney.generator A (X ⊗ Y) ((s.horizontal k).val + (s.vertical k).val)
          (simplex X Y (frontPath s k)
            (AlexanderWhitney.cut X x 0 (s.horizontal k).val (by omega))
            (AlexanderWhitney.cut Y y 0 (s.vertical k).val (by omega))) ⊗ₜ[A]
        AlexanderWhitney.generator A (X ⊗ Y)
          ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
          (simplex X Y (backPath s k)
            (AlexanderWhitney.cut X x (s.horizontal k).val (p - (s.horizontal k).val) (by omega))
            (AlexanderWhitney.cut Y y (s.vertical k).val (q - (s.vertical k).val) (by omega))) := by
  have hb : AlexanderWhitney.cut (X ⊗ Y) (simplex X Y s x y)
      ((s.horizontal k).val + (s.vertical k).val)
      ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (by omega) =
        simplex X Y (backPath s k)
          (AlexanderWhitney.cut X x (s.horizontal k).val (p - (s.horizontal k).val) (by omega))
          (AlexanderWhitney.cut Y y (s.vertical k).val (q - (s.vertical k).val) (by omega)) := by
    have hseg : AlexanderWhitney.segmentMap
        ((s.horizontal k).val + (s.vertical k).val)
        ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q) (by omega) =
        AlexanderWhitney.segmentMap k.val
          ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q)
          (by have hc := s.coordinate_sum k; omega) := by
      ext i : 3
      apply Fin.ext
      change ((s.horizontal k).val + (s.vertical k).val) + i.val = k.val + i.val
      rw [s.coordinate_sum k]
    change (X ⊗ Y).map (AlexanderWhitney.segmentMap
      ((s.horizontal k).val + (s.vertical k).val)
      ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (p + q) (by omega)).op
      (simplex X Y s x y) = _
    rw [hseg]
    exact (simplex_backCut X Y s k x y).symm
  rw [AlexanderWhitney.component_generator, ← simplex_frontCut, hb]

end SerrePositivity.EInfinity.Shuffle
