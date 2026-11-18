module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.LeibnizPositive
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleZeroDirections
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizZero

/-!
# 一般の単体集合の次数0の入力に対する shuffle の微分

概要：Berger–Fresse §1.1.3 の片方の入力が次数0の場合の Leibniz 則を証明する。
方針：全境界を分割し、次数0の方向の辺と角が存在しないことを使って一方向の寄与に帰着する。
規約：非零の入力の次数は後続次数で表す。
使われ方：正次数の計算と合わせて全ての次数の鎖写像の条件を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：第一の入力が次数0の shuffle の微分は垂直方向の寄与のみである（Berger–Fresse §1.1.3）。
方針：全境界の分割から、空の水平辺集合を持つ経路の水平端点と水平角を除く。
規約：全ての境界面は第二の入力の微分に対応する。
使われ方：第一の入力が次数0の場合の Leibniz 則へ帰着する。 -/
lemma shuffleValue_d_leftZero_contribution (X Y : SSet.{0}) (q : ℕ)
    (x : X _⦋0⦌) (y : Y _⦋q + 1⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (0 + (q + 1)) (0 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y 0 (q + 1) x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.verticalBoundaryContribution A X Y x y := by
  classical
  have hN : 0 < 0 + (q + 1) := by omega
  let := isEmpty_horizontalAdjacentCorner_leftZero (q + 1)
  let : IsEmpty {s : ShufflePath 0 (q + 1) // 0 ∈ s.val} :=
    ⟨fun s => s.val.notMem_leftZero 0 s.property⟩
  let : IsEmpty {s : ShufflePath 0 (q + 1) // Fin.last (0 + q) ∈ s.val} :=
    ⟨fun s => s.val.notMem_leftZero _ s.property⟩
  erw [_root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_decomposition A X Y 0 (q + 1) hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_adjacentBoundaryTerm A X Y hN x y]
  let first := fun s : ShufflePath 0 (q + 1) =>
    (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (0 + (q + 1) - 1)
      ((X ⊗ Y).map (boundaryFaceMap (0 + (q + 1)) hN 0).op
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y))
  let last := fun s : ShufflePath 0 (q + 1) =>
    (-1 : ℤ) ^ (0 + (q + 1)) • (s.sign : ℤ) •
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (0 + (q + 1) - 1)
        ((X ⊗ Y).map
          (boundaryFaceMap (0 + (q + 1)) hN (Fin.last (0 + (q + 1)))).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y))
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun s : ShufflePath 0 (q + 1) => 0 ∈ s.val) first,
    ← Fintype.sum_subtype_add_sum_subtype
      (fun s : ShufflePath 0 (q + 1) => Fin.last (0 + q) ∈ s.val) last]
  simp only [Finset.sum_of_isEmpty, zero_add]
  dsimp only [first, last]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.sum_verticalFirstBoundary A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_verticalAdjacentBoundary A X Y hN x y, _root_.SerrePositivity.SimplicialChains.Shuffle.sum_verticalLastBoundary A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.verticalBoundaryContribution, _root_.SerrePositivity.SimplicialChains.Shuffle.sum_vertical_first_face A X Y x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_vertical_last_face A X Y x y]

/-- 概要：第一の入力が次数0の shuffle は第二の入力の微分と可換する（Berger–Fresse §1.1.3）。
方針：唯一の垂直方向の寄与を第二の入力の微分の公式で置き換える。
規約：Koszul 符号は (−1)^0=1 である。
使われ方：次数0の第一の入力に対する鎖写像の条件を与える。 -/
lemma shuffleValue_d_leftZero (X Y : SSet.{0}) (q : ℕ)
    (x : X _⦋0⦌) (y : Y _⦋q + 1⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (0 + (q + 1)) (0 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y 0 (q + 1) x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y 0 q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x)
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y (q + 1) y)) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_leftZero_contribution A X Y q x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.verticalBoundaryContribution_eq A X Y x y, pow_zero, one_smul]

/-- 概要：第二の入力が次数0の shuffle の微分は水平方向の寄与のみである（Berger–Fresse §1.1.3）。
方針：全境界の分割から、全ての辺が水平であることにより垂直端点と垂直角を除く。
規約：全ての境界面は第一の入力の微分に対応する。
使われ方：第二の入力が次数0の場合の Leibniz 則へ帰着する。 -/
lemma shuffleValue_d_rightZero_contribution (X Y : SSet.{0}) (p : ℕ)
    (x : X _⦋p + 1⦌) (y : Y _⦋0⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + 0) (p + 0)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y (p + 1) 0 x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution A X Y x y := by
  classical
  have hN : 0 < p + 1 + 0 := by omega
  let _ := isEmpty_verticalAdjacentCorner_rightZero (p + 1)
  let _ : IsEmpty {s : ShufflePath (p + 1) 0 // 0 ∉ s.val} :=
    ⟨fun s => s.property (s.val.mem_rightZero 0)⟩
  let _ : IsEmpty {s : ShufflePath (p + 1) 0 // Fin.last p ∉ s.val} :=
    ⟨fun s => s.property (s.val.mem_rightZero _)⟩
  erw [_root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_decomposition A X Y (p + 1) 0 hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_adjacentBoundaryTerm A X Y hN x y]
  let first := fun s : ShufflePath (p + 1) 0 =>
    (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + 0 - 1)
      ((X ⊗ Y).map (boundaryFaceMap (p + 1 + 0) hN 0).op
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y))
  let last := fun s : ShufflePath (p + 1) 0 =>
    (-1 : ℤ) ^ (p + 1 + 0) • (s.sign : ℤ) •
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + 0 - 1)
        ((X ⊗ Y).map
          (boundaryFaceMap (p + 1 + 0) hN (Fin.last (p + 1 + 0))).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y))
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun s : ShufflePath (p + 1) 0 => 0 ∈ s.val) first,
    ← Fintype.sum_subtype_add_sum_subtype
      (fun s : ShufflePath (p + 1) 0 => Fin.last p ∈ s.val) last]
  simp only [Finset.sum_of_isEmpty, add_zero]
  dsimp only [first, last]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalFirstBoundary_transport A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalAdjacentBoundary A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalLastBoundary_transport A X Y hN (Fin.last p)
      rfl x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution, _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_first_face A X Y x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_last_face A X Y ⟨p + 0, by omega⟩ rfl x y]
  rfl

/-- 概要：第二の入力が次数0の shuffle は第一の入力の微分と可換する（Berger–Fresse §1.1.3）。
方針：唯一の水平方向の寄与を第一の入力の微分の公式で置き換える。
規約：第一の入力の微分には追加の符号を付けない。
使われ方：次数0の第二の入力に対する鎖写像の条件を与える。 -/
lemma shuffleValue_d_rightZero (X Y : SSet.{0}) (p : ℕ)
    (x : X _⦋p + 1⦌) (y : Y _⦋0⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + 0) (p + 0)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y (p + 1) 0 x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p 0
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + 1) x))
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y 0 y) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_rightZero_contribution A X Y p x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution_eq A X Y x y]

end SerrePositivity.SimplicialChains.Shuffle
