module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Simplices
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ComponentLaws

/-!
# 一般の正規化 shuffle 和

概要：Berger–Fresse §1.1.3 の shuffle の符号付き和を一般の単体集合で定義する。
方針：格子経路の積単体を正規化生成元に写し signature を掛けて加える。
規約：入力単体は退化していてもよい。
使われ方：shuffle の双線形成分を正規化鎖へ降ろす。
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

/-- 概要：退化単体の正規化生成元は零（Berger–Fresse §1.1.3）。
方針：低い次元から来る表示の単体圏の射が非単射であることを使う。
規約：任意の小さい単体集合に適用する。
使われ方：退化した入力から来る shuffle 項を消す。 -/
lemma generator_degenerate (X : SSet.{0}) (n : ℕ) (x : X _⦋n⦌)
    (hx : x ∈ X.degenerate n) : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X n x = 0 := by
  obtain ⟨m, hm, θ, y, rfl⟩ := hx
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_map_of_not_mono
  intro hθ
  have hle := SimplexCategory.le_of_mono θ
  omega

/-- 概要：二つの単体の一般の shuffle 和（Berger–Fresse §1.1.3）。
方針：全格子経路の正規化積単体を符号付きで足す。
規約：p,q 次元の入力の全次数は p+q。
使われ方：正規化鎖上の shuffle の生成元公式。 -/
def value (X Y : SSet.{0}) (p q : ℕ) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q) :=
  ∑ s : ShufflePath p q, (s.sign : ℤ) •
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q) (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y)

/-- 概要：第一の入力の退化写像は shuffle 和で零（Berger–Fresse §1.1.3）。
方針：各経路の積単体が退化するため全ての項を消す。
規約：基礎環の標数に依存しない項ごとの消滅。
使われ方：第一の入力について正規化の関係を保つ。 -/
lemma value_σ_left (X Y : SSet.{0}) (p q : ℕ) (i : Fin (p + 1))
    (x : X _⦋p⦌) (y : Y _⦋q⦌) : _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y (p + 1) q (X.σ i x) y = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.generator_degenerate A _ _ _ (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_σ_left X Y s i x y), smul_zero]

/-- 概要：第二の入力の退化写像は shuffle 和で零（Berger–Fresse §1.1.3）。
方針：各経路の積単体が退化するため全ての項を消す。
規約：符号の相殺を必要としない。
使われ方：第二の入力について正規化の関係を保つ。 -/
lemma value_σ_right (X Y : SSet.{0}) (p q : ℕ) (i : Fin (q + 1))
    (x : X _⦋p⦌) (y : Y _⦋q⦌) : _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p (q + 1) x (Y.σ i y) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.generator_degenerate A _ _ _ (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex_σ_right X Y s i x y), smul_zero]

/-- 概要：一般の shuffle 和は入力の単体集合の射に自然（Berger–Fresse §1.1.3）。
方針：正規化鎖写像を有限和に分配し各積単体の自然性を使う。
規約：左右の射は独立である。
使われ方：shuffle の鎖写像の自然性を生成元で検査する。 -/
lemma value_natural {X X' Y Y' : SSet.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p q : ℕ) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap A (f ⊗ₘ g)).f (p + q) (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.value A X' Y' p q (f.app _ x) (g.app _ y) := by
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value, map_sum, map_zsmul, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainMap_generator, _root_.SerrePositivity.SimplicialChains.Shuffle.simplex_natural]

end SerrePositivity.SimplicialChains.Shuffle
