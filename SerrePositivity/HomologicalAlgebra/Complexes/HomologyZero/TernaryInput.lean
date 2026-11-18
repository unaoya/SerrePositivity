module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero

/-!
# 二段の二項作用を三入力の反復冪で比較する

概要：BF §1・BM §1 の部分合成を通常の二項積の結合則の図式へ移す。
方針：三因子テンソルを反復冪へ移し、位置 0・1 の代入の構造同型を簡約する。
規約：演算の結合性は仮定せず、単位因子と既存の括弧付けを保つ。
使われ方：E 代数の H⁰ の積の結合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：通常の三因子テンソルを右括弧の三乗冪へ移す（BF §1）。
方針：結合子の後で末尾の単位因子を挿入する。
規約：始域は左に括った三因子テンソル。
使われ方：結合性の二つの部分合成の共通の入力。 -/
def ternaryInput (X : Complex A) : (X ⊗ X) ⊗ X ⟶ power X 3 :=
  (α_ X X X).hom ≫ (X ◁ (X ◁ (oneIso X).inv))

/-- 概要：先頭への二項作用の代入は左に括った二段の積（BF §1、BM §1）。
方針：先頭代入の公式を三因子の入力へ前合成し、構造同型を簡約する。
規約：演算自体の結合性は使わない。
使われ方：E の部分合成から二項積の結合性へ移す。 -/
lemma binaryAssociativityLeftInput (X : Complex A) (ν : power X 2 ⟶ X) :
    _root_.SerrePositivity.HomologyZero.ternaryInput X ≫ (λ_ (power X 3)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (𝟙_ (Complex A)) 1 2 0 ((λ_ (power X 2)).hom ≫ ν) ≫ ν =
    (((X ◁ (oneIso X).inv) ≫ ν) ▷ X) ≫ (X ◁ (oneIso X).inv) ≫ ν := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero]
  simp only [_root_.SerrePositivity.HomologyZero.ternaryInput, appendIso, power, oneIso, Iso.trans_inv,
    whiskerLeftIso_inv, eqToIso.inv, eqToHom_refl, Category.id_comp,
    whiskerLeft_id, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

/-- 概要：第二位置への二項作用の代入は右に括った二段の積（BF §1、BM §1）。
方針：代入を展開し、単位係数の交換と構造同型を簡約する。
規約：演算自体の結合性は使わない。
使われ方：E の二つの部分合成の作用を比較する。 -/
lemma binaryAssociativityRightInput (X : Complex A) (ν : power X 2 ⟶ X) :
    _root_.SerrePositivity.HomologyZero.ternaryInput X ≫ (λ_ (power X 3)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (𝟙_ (Complex A)) 1 2 1 ((λ_ (power X 2)).hom ≫ ν) ≫ ν =
    (α_ X X X).hom ≫ (X ◁ ((X ◁ (oneIso X).inv) ≫ ν)) ≫
      (X ◁ (oneIso X).inv) ≫ ν := by
  simp only [_root_.SerrePositivity.HomologyZero.ternaryInput, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction, Fin.val_one,
    appendIso, power, oneIso, Iso.trans_inv, Iso.trans_hom, whiskerLeftIso_inv, whiskerLeftIso_hom,
    eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [braiding_tensorUnit_left]
  monoidal

end SerrePositivity.HomologyZero
