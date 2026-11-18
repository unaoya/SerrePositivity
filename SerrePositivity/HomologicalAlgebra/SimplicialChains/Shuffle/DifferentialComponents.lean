module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.LeibnizChains

/-!
# 一般 shuffle 成分の微分条件

概要：Berger–Fresse §1.1.3 の Leibniz 則を加群テンソルの射の等式にする。
方針：純テンソル上で検査し、任意の正規化鎖の Leibniz 則を使う。
規約：自然数次数の零の境界を二つの場合として分ける。
使われ方：全テンソル複体からの shuffle 鎖写像の構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：正次数二入力の成分微分公式（BF §1.1.3）。
方針：純テンソルの外延性と双線形 Leibniz 則を使う。
規約：第一項の次数の括弧の同定を等式の射で明示する。
使われ方：shuffle 鎖写像の正次数成分。 -/
lemma component_d_positive (X Y : SSet.{0}) (p q : ℕ) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y (p + 1) (q + 1) ≫
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + (q + 1)) (p + 1 + q) =
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p ▷ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X (q + 1)) ≫
        _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p (q + 1) ≫
        eqToHom (congrArg (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X
          (by omega : p + (q + 1) = p + 1 + q)) +
      (-1 : ℤ) ^ (p + 1) •
        (((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X (p + 1) ◁
            (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q) ≫ _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y (p + 1) q) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d _ _ (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y _ _ x y) =
    _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + (q + 1) = p + 1 + q)
      (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p (q + 1) ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d _ _ x) y) +
    (-1 : ℤ) ^ (p + 1) • _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) q x
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d _ _ y)
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.shuffleBilinear_d_positive A X Y p q x y

/-- 概要：第一の入力が零次数の成分微分公式（BF §1.1.3）。
方針：純テンソル上の零次数 Leibniz 則を使う。
規約：第一の入力の微分項は存在しない。
使われ方：shuffle 鎖写像の左端の次数。 -/
lemma component_d_leftZero (X Y : SSet.{0}) (q : ℕ) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y 0 (q + 1) ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (0 + (q + 1)) (0 + q) =
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X 0 ◁ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q) ≫
        _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y 0 q := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.shuffleBilinear_d_leftZero A X Y q x y

/-- 概要：第二の入力が零次数の成分微分公式（BF §1.1.3）。
方針：純テンソル上の零次数 Leibniz 則を使う。
規約：第二の入力の微分項は存在しない。
使われ方：shuffle 鎖写像の右端の次数。 -/
lemma component_d_rightZero (X Y : SSet.{0}) (p : ℕ) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y (p + 1) 0 ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + 0) (p + 0) =
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p ▷ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X 0) ≫
        _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.shuffleBilinear_d_rightZero A X Y p x y

end SerrePositivity.SimplicialChains.Shuffle
