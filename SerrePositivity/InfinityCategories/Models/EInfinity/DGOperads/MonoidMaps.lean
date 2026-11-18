module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MonoidPowers

/-!
模型。文献の定義との比較は後で
# モノイド対象の射は反復積を保つ

概要：BM §1 の全入力の作用保存を二項積と単位の保存から得る。
方針：入力数に帰納して既存のテンソル冪の射の再帰と比較する。
規約：零入力も含む。
使われ方：離散可換代数から E 代数への関手の射成分。
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

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {X Y : C} [MonObj X] [MonObj Y]

/-- 概要：モノイド対象の射は全入力の反復積を保つ（BM §1）。
方針：単位保存と二項積保存を入力数の帰納に適用する。
規約：零入力は単位の保存そのもの。
使われ方：Com 代数の射の作用保存を与える。 -/
lemma powerProduct_map (f : X ⟶ Y) [IsMonHom f] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n ≫ f = _root_.SerrePositivity.TensorPowers.map f n ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct Y n := by
  induction n with
  | zero =>
    exact (IsMonHom.one_hom f).trans (Category.id_comp _).symm
  | succ n ih =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct, _root_.SerrePositivity.TensorPowers.map, Category.assoc, IsMonHom.mul_hom,
      ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
    rw [ih]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
