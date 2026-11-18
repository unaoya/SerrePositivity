module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality

/-!
模型。文献の定義との比較は後で
# 一つの出力への余演算の代入

概要：Berger–Fresse §3.1 のオペラッド余代数の部分合成を記述する射を作る。
方針：出力列を指定位置の前後に分け、係数を移して余演算を適用し再結合する。
規約：arity 0 の余演算も許し、交換には既存の Koszul 対称性を使う。
使われ方：P-coalgebra の合成則と convolution の合成則の記述に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：m+1 出力の位置 i に n 出力の余演算を代入する（Berger–Fresse §3.1）。
方針：前方 i 個を係数と交換し、指定因子に余演算を施し全出力を連結する。
規約：n=0 では指定因子を消し、前後の因子の順序は保つ。
使われ方：P-coalgebra の部分合成条件の右辺となる。 -/
def tensorCoInsertionAction (K C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ K ⟶ power K n) : C ⊗ power K (m + 1) ⟶ power K (m + n) :=
  let s := i.val
  let t := m - s
  (C ◁ (eqToHom (congrArg (power K) (by dsimp [s, t]; omega : m + 1 = s + (t + 1))) ≫
    (appendIso K s (t + 1)).inv)) ≫
  (α_ C (power K s) (power K (t + 1))).inv ≫
  ((β_ C (power K s)).hom ▷ power K (t + 1)) ≫
  (α_ (power K s) C (power K (t + 1))).hom ≫
  (power K s ◁ (α_ C K (power K t)).inv) ≫
  (power K s ◁ (θ ▷ power K t)) ≫
  (power K s ◁ (appendIso K n t).hom) ≫
  (appendIso K s (n + t)).hom ≫
  eqToHom (congrArg (power K) (by dsimp [s, t]; omega : s + (n + t) = m + n))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
