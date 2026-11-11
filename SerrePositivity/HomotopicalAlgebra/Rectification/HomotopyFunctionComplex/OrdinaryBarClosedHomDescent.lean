module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarHomSections
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SplitLocalizedDescent
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom

/-!
# 中断した任意モデル源への一般化：OrdinaryBarClosedHomDescent

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual descent of each whole parameterized action to the original Hom。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0146][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0146
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual descent of each whole parameterized action to the original Hom

These maps land in lifts of the actual small internal Hom, and restriction
recovers the original action up to an actual interval homotopy. This does
not assert strict composition of the descended maps.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

lemma target_kan (X Y : D C) : SSet.modelCategoryQuillen.J.rlp (terminal.from
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)))) :=
  UniverseLift.horn_terminal_map (SimplexParameterHom.native_kan
    (small hcof hfib X) (small hcof hfib Y) (OrdinaryBarSmallReference.value_kan hcof hfib Y))

def mapping (X Y : D C) : P ⊗ baseHom C X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  SplitLocalizedDescent.descend
    (SplitLocalizedDescent.tensorSplit (OrdinaryBarHomSections.small C X Y) P)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)

lemma restriction_homotopy (X Y : D C) : Nonempty (SSet.Homotopy
    ((P ◁ smallAugmentation C X Y) ≫ mapping hcof hfib P X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)) :=
  SplitLocalizedDescent.tensor_descend_homotopy (OrdinaryBarHomSections.small C X Y)
    (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y) P
    (target_kan hcof hfib X Y) (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)

lemma lifts_homotopy {T : SSet.{max u v}} {X Y : D C} (j : T ⟶ P)
    (f g : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (hfg : f ≫ smallAugmentation C X Y = g ≫ smallAugmentation C X Y) :
    Nonempty (SSet.Homotopy
      (lift j f ≫ OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)
      (lift j g ≫ OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)) := by
  have h : lift j f ≫ (P ◁ smallAugmentation C X Y) =
      lift j g ≫ (P ◁ smallAugmentation C X Y) := by
    rw [lift_whiskerLeft, lift_whiskerLeft, hfg]
  exact SplitLocalizedDescent.lifts_homotopy
    (AnodyneHomotopy.whiskerLeft_anodyneQ_isIso _
      (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y) P)
    (target_kan hcof hfib X Y) (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)
    (lift j f) (lift j g) h

lemma native_lifts_homotopy {T : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (hfg : f ≫ smallAugmentation C X Y = g ≫ smallAugmentation C X Y) :
    Nonempty (SSet.Homotopy
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j f)
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j g)) := by
  obtain ⟨H⟩ := lifts_homotopy hcof hfib P j f g hfg
  have h := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) H
  rw [OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily,
    OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily] at h
  exact (UniverseLift.localized_map_eq_iff_homotopy AnodyneHomotopy.anodyneQ T
    ((ihom (small hcof hfib X)).obj (small hcof hfib Y))
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Y))
    _ _).mp h

def nativeFamily {T : SSet.{v}} {X Y : D C} (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ baseHom C X Y) :
    T ⟶ (ihom (small hcof hfib X)).obj (small hcof hfib Y) :=
  OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j
    (f ≫ (OrdinaryBarHomSections.small C X Y).section_)

lemma nativeFamily_substitute {T U : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ baseHom C X Y) (i : U ⟶ T) :
    nativeFamily hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) =
      i ≫ nativeFamily hcof hfib P j f := by
  unfold nativeFamily
  rw [Category.assoc, OrdinaryBarDiagonalClosedAction.nativeFamily_substitute]

lemma native_restriction_homotopy {T : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    Nonempty (SSet.Homotopy
      (nativeFamily hcof hfib P j (f ≫ smallAugmentation C X Y))
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j f)) := by
  apply native_lifts_homotopy hcof hfib P
  rw [Category.assoc, Category.assoc, (OrdinaryBarHomSections.small C X Y).id,
    Category.comp_id]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
