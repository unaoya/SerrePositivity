module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
模型。文献の定義との比較は後で
# モノイド対象の反復テンソルの積

概要：BM §1 の Com 代数の全入力演算に用いる反復積を構成する。
方針：零入力を単位、後続入力を二項積で再帰し、連結との両立を証明する。
規約：一般のモノイダル圏、右に括った既存のテンソル冪。
使われ方：離散可換代数を Com の代数として扱う。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open _root_.SerrePositivity.TensorPowers

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (X : C) [MonObj X]

/-- 概要：モノイド対象の全 arity の反復積（BM §1）。
方針：空積は単位射、後続は先頭と残りの積の二項積。
規約：既存の右に括った TensorPowers.power を使う。
使われ方：Com の作用と離散可換代数の演算。 -/
def powerProduct : ∀ n : ℕ, power X n ⟶ X
  | 0 => η[X]
  | n + 1 => (X ◁ powerProduct n) ≫ μ[X]

/-- 概要：等しい入力数の反復積を同一視する（BM §1）。
方針：入力数の等式を消去する。
規約：テンソル冪の次数移送を明示する。
使われ方：連結の再帰での arity 移送。 -/
@[reassoc]
lemma powerProduct_index {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (power X) h) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X m := by
  subst n
  simp

/-- 概要：一入力の反復積は一因子比較（BM §1）。
方針：モノイド対象の右単位則。
規約：単位のテンソル因子を含む実際の射。
使われ方：Com 代数の単位演算の公理。 -/
lemma powerProduct_one : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X 1 = (oneIso X).hom := MonObj.mul_one X

/-- 概要：入力を二ブロックに分けても反復積は同じ（BM §1）。
方針：先頭ブロックの長さに帰納し、単位則と結合則を用いる。
規約：空のブロックも含む。
使われ方：任意の位置への演算の代入の積を計算する。 -/
lemma powerProduct_append (m n : ℕ) :
    (appendIso X m n).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X (m + n) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n) ≫ μ[X] := by
  induction m with
  | zero =>
    rw [appendIso_zero_left, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_index X (Nat.zero_add n).symm]
    change (λ_ (power X n)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n =
      (η[X] ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n) ≫ μ[X]
    simp only [tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
  | succ m ih =>
    simp only [appendIso, Iso.trans_hom, eqToIso.hom, whiskerLeftIso_hom,
      Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_index X (Nat.succ_add m n).symm]
    change (α_ X (power X m) (power X n)).hom ≫
      (X ◁ (appendIso X m n).hom) ≫ (X ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X (m + n)) ≫ μ[X] = _
    rw [← whiskerLeft_comp_assoc, ih]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct, mon_tauto]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
