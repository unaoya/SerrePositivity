module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalAction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterComposition

/-!
# 中断した任意モデル源への一般化：OrdinaryBarDiagonalClosedAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Diagonal word action valued in the actual small internal Hom。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0155][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0155
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Diagonal word action valued in the actual small internal Hom

The whole map is valued in the universe lift of the native small internal
Hom. Native small parameter families use the standard closed composition.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarDiagonalAction
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

def mapping (X Y : D C) : P ⊗ OrdinaryBarFixedWordResolution.hom C X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  curry (action hcof hfib P X Y) ≫
    (UniverseLiftParameterHom.closedIso (small hcof hfib X) (small hcof hfib Y)).inv

lemma mapping_uncurry (X Y : D C) :
    uncurry (mapping hcof hfib P X Y ≫
      (UniverseLiftParameterHom.closedIso (small hcof hfib X) (small hcof hfib Y)).hom) =
      action hcof hfib P X Y := by
  rw [mapping, Category.assoc, Iso.inv_hom_id, Category.comp_id, uncurry_curry]

lemma mapping_family {T : SSet.{max u v}} {X Y : D C} (j : T ⟶ P)
    (f : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    lift j f ≫ mapping hcof hfib P X Y =
      curry (largeFamily hcof hfib P j f) ≫
        (UniverseLiftParameterHom.closedIso (small hcof hfib X) (small hcof hfib Y)).inv := by
  rw [mapping, ← Category.assoc, ← curry_natural_left]
  rfl

def nativeFamily {T : SSet.{v}} {X Y : D C} (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    T ⟶ (ihom (small hcof hfib X)).obj (small hcof hfib Y) :=
  curry (OrdinaryBarDiagonalEvaluation.family hcof hfib P j f)

lemma nativeFamily_substitute {T U : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) (i : U ⟶ T) :
    nativeFamily hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) =
      i ≫ nativeFamily hcof hfib P j f := by
  rw [nativeFamily, OrdinaryBarDiagonalEvaluation.family_substitute]
  exact curry_natural_left _ _

lemma nativeFamily_identity {T : SSet.{v}} (X : D C)
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P) :
    nativeFamily hcof hfib P j
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C X) =
      toUnit T ≫ MonoidalClosed.id (small hcof hfib X) := by
  rw [nativeFamily, OrdinaryBarDiagonalEvaluation.family_identity,
    ClosedParameterComposition.curry_fst]

lemma nativeFamily_comp {T : SSet.{v}} {X Y Z : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    nativeFamily hcof hfib P j (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) =
      lift (nativeFamily hcof hfib P j f) (nativeFamily hcof hfib P j g) ≫
        MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) := by
  rw [nativeFamily, ← OrdinaryBarDiagonalEvaluation.family_comp,
    ClosedParameterComposition.curry_comp]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction
