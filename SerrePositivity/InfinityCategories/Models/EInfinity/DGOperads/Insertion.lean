module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality

/-!
模型。文献の定義との比較は後で
# テンソル冪への一つの演算の代入

概要：Berger–Moerdijk §1 の代数の合成則に必要なテンソル冪の代入射を構成する。
方針：入力を挿入位置の前・中・後に分け、係数を Koszul 対称性で移動する。
規約：arity 0 の演算も含める。微分と符号は既存の複体のモノイダル構造に従う。
使われ方：部分合成を使ったオペラッド代数の結合則を述べる。
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

/-- 概要：一つの n 入力演算を m+1 入力の位置 i に代入する射（Berger–Moerdijk §1）。
方針：テンソル冪を分割し、係数 C を先行入力の後へ動かして演算 θ を適用する。
規約：n=0 を許す。C と先行入力の交換には Koszul 符号が含まれる。
使われ方：対称オペラッド代数の部分合成に関する結合則を記述する。 -/
def tensorInsertionAction (K C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ power K n ⟶ K) : C ⊗ power K (m + n) ⟶ power K (m + 1) :=
  let s := i.val
  let t := m - s
  (C ◁ (eqToHom (congrArg (power K) (by dsimp [s, t]; omega : m + n = s + (n + t))) ≫
    (appendIso K s (n + t)).inv)) ≫
  (α_ C (power K s) (power K (n + t))).inv ≫
  ((β_ C (power K s)).hom ▷ power K (n + t)) ≫
  (α_ (power K s) C (power K (n + t))).hom ≫
  (power K s ◁ (C ◁ (appendIso K n t).inv)) ≫
  (power K s ◁ (α_ C (power K n) (power K t)).inv) ≫
  (power K s ◁ (θ ▷ power K t)) ≫
  (appendIso K s (t + 1)).hom ≫
  eqToHom (congrArg (power K) (by dsimp [s, t]; omega : s + (t + 1) = m + 1))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
