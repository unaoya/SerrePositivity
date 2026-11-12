module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReplacementComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSmallReference

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual weak maps from the large bar to small Kan reference values。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0222][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0222
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual weak maps from the large bar to small Kan reference values

The choices retain the exact localized comparison. No naturality of the
chosen actual maps, or strict simplicial action on the selected values, is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallReference
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev value (X : Cᵒᵖ × C) : SSet.{v} :=
  (ReplacementMapping.uncurried hcof hfib).obj (ReplacementMapping.ofBase X)

lemma value_kan (X : Cᵒᵖ × C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (value hcof hfib X)) :=
  (SSet.modelCategoryQuillen.fibration_iff _).mp
    (ReplacementMapping.kanComplex hcof hfib
      (ReplacementMapping.ofBase X).1 (ReplacementMapping.ofBase X).2)

def comparisonIso (X : Cᵒᵖ × C) :
    AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (value hcof hfib X)) ≅
      AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj X) :=
  OrdinaryBarReplacementComparison.presentationIso hcof hfib AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)
    (ReplacementMapping.ofBase X)

/-- This is an actual map, chosen to represent the original comparison inverse. -/
def toReference (X : Cᵒᵖ × C) : OrdinaryResolutionBar.functor.obj X ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (value hcof hfib X) :=
  KanLocalizedRepresentatives.representative AnodyneHomotopy.anodyneQ
    (UniverseLift.horn_terminal_map (value_kan hcof hfib X))
    (comparisonIso hcof hfib X).inv

lemma toReference_map (X : Cᵒᵖ × C) :
    AnodyneHomotopy.anodyneQ.map (toReference hcof hfib X) =
      (comparisonIso hcof hfib X).inv :=
  KanLocalizedRepresentatives.representative_map _ _ _

lemma toReference_isIso (X : Cᵒᵖ × C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toReference hcof hfib X)) := by
  rw [toReference_map]
  infer_instance

/-- Any other representative of that same inverse is connected by an actual interval. -/
lemma toReference_homotopy (X : Cᵒᵖ × C)
    (f : OrdinaryResolutionBar.functor.obj X ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (value hcof hfib X))
    (hf : AnodyneHomotopy.anodyneQ.map f = (comparisonIso hcof hfib X).inv) :
    Nonempty (SSet.Homotopy (toReference hcof hfib X) f) :=
  (KanLocalizedRepresentatives.map_eq_iff_homotopy AnodyneHomotopy.anodyneQ
    (UniverseLift.horn_terminal_map (value_kan hcof hfib X)) _ _).mp
    ((toReference_map hcof hfib X).trans hf.symm)

def homEquiv (X Y : Cᵒᵖ × C) :
    HomotopyClasses.obj (value hcof hfib X) (value hcof hfib Y) ≃
      (AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj X) ⟶
        AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj Y)) :=
  (UniverseLift.smallLocalizedHomEquiv AnodyneHomotopy.anodyneQ _ _
    (value_kan hcof hfib Y)).trans
      (Iso.homCongr (comparisonIso hcof hfib X) (comparisonIso hcof hfib Y))

include hcof hfib in
lemma small_localizedHom (X Y : Cᵒᵖ × C) :
    Small.{v} (AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj X) ⟶
      AnodyneHomotopy.anodyneQ.obj (OrdinaryResolutionBar.functor.obj Y)) :=
  small_map (homEquiv hcof hfib X Y).symm

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallReference
