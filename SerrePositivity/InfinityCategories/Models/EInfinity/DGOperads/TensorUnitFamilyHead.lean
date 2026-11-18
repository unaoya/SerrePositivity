module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorUnitFamily
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 単位族の縮約の先頭からの計算

概要：Berger–Moerdijk §1 の右単位則に用いる単位族の縮約を、先頭からの再帰で表す。
方針：最後からの縮約の定義と結合子・単位子の整合性を比較する。
規約：縮約の同型そのものは変更しない。
使われ方：有限テンソル対の係数・入力の分離と単位族の縮約を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

private lemma unitHeadZero (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    (ρ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom := by
  monoidal

private lemma unitHeadStep {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {V : C} (a : V ⟶ 𝟙_ C) :
    (α_ (𝟙_ C) V (𝟙_ C)).inv ≫
      ((((𝟙_ C) ◁ a) ≫ (λ_ (𝟙_ C)).hom) ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom =
    ((𝟙_ C) ◁ ((a ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom)) ≫ (λ_ (𝟙_ C)).hom := by
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：単位族の縮約は先頭を残して尾を縮約する式でも計算できる（Berger–Moerdijk §1）。
方針：最後からの縮約を先頭に関して帰納的に比較し、単位子の整合性を使う。
規約：空の尾の縮約は恒等射。
使われ方：有限テンソル対の分離の先頭に関する再帰と単位族の縮約を揃える。 -/
lemma tensorUnitFamilyIso_succ_head (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A (n + 1)).hom =
      ((𝟙_ (Complex A)) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).hom) ≫ (λ_ (𝟙_ (Complex A))).hom := by
  induction n with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, Iso.trans_hom,
      Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id,
      id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.assoc]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.unitHeadZero (Complex A)
  | succ n ih =>
    conv_lhs => rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso_succ_hom]
    conv_rhs => rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso_succ_hom]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, Category.assoc]
    rw [ih, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.unitHeadStep]
    simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
