module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallReference

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSmallAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual small arrow representatives for the strict large bar action。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0219][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0219
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual small arrow representatives for the strict large bar action

The unit, composition and comparison square are supplied by actual interval
homotopies. These are not strict functor laws or a claim of higher coherence.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallAction
open OrdinaryBarSmallReference
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def transported {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (value hcof hfib X)) ⟶
      AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (value hcof hfib Y)) :=
  (comparisonIso hcof hfib X).hom ≫
    AnodyneHomotopy.anodyneQ.map (OrdinaryResolutionBar.functor.map f) ≫
      (comparisonIso hcof hfib Y).inv

lemma transported_id (X : Cᵒᵖ × C) : transported hcof hfib (𝟙 X) = 𝟙 _ := by
  simp [transported]

lemma transported_comp {X Y Z : Cᵒᵖ × C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    transported hcof hfib (f ≫ g) = transported hcof hfib f ≫ transported hcof hfib g := by
  dsimp only [transported]
  rw [(OrdinaryResolutionBar.functor (C := C)).map_comp f g,
    AnodyneHomotopy.anodyneQ.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Every base arrow has a small actual representative; strict laws are not asserted. -/
def arrow {X Y : Cᵒᵖ × C} (f : X ⟶ Y) : value hcof hfib X ⟶ value hcof hfib Y :=
  UniverseLift.localizedRepresentative AnodyneHomotopy.anodyneQ _ _
    (value_kan hcof hfib Y) (transported hcof hfib f)

lemma arrow_map {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} (arrow hcof hfib f)) =
      transported hcof hfib f :=
  UniverseLift.localizedRepresentative_map _ _ _ _ _

lemma arrow_id_homotopy (X : Cᵒᵖ × C) :
    Nonempty (SSet.Homotopy (arrow hcof hfib (𝟙 X)) (𝟙 (value hcof hfib X))) := by
  apply (UniverseLift.localized_map_eq_iff_homotopy AnodyneHomotopy.anodyneQ _ _
    (value_kan hcof hfib X) _ _).mp
  rw [arrow_map, transported_id]
  change 𝟙 _ = AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.map (𝟙 _))
  simp only [CategoryTheory.Functor.map_id]

lemma arrow_comp_homotopy {X Y Z : Cᵒᵖ × C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Nonempty (SSet.Homotopy (arrow hcof hfib (f ≫ g))
      (arrow hcof hfib f ≫ arrow hcof hfib g)) := by
  apply (UniverseLift.localized_map_eq_iff_homotopy AnodyneHomotopy.anodyneQ _ _
    (value_kan hcof hfib Z) _ _).mp
  change AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.map _) =
    AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.map (_ ≫ _))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    arrow_map, arrow_map, arrow_map, transported_comp]

/-- The chosen actual value comparisons commute with every base arrow up to
one actual interval, retaining both original composite maps as endpoints. -/
lemma square_homotopy {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    Nonempty (SSet.Homotopy
      (OrdinaryResolutionBar.functor.map f ≫ toReference hcof hfib Y)
      (toReference hcof hfib X ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} (arrow hcof hfib f))) := by
  apply (KanLocalizedRepresentatives.map_eq_iff_homotopy AnodyneHomotopy.anodyneQ
    (UniverseLift.horn_terminal_map (value_kan hcof hfib Y)) _ _).mp
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    toReference_map, toReference_map, arrow_map]
  simp only [transported, Iso.inv_hom_id_assoc]

include hcof hfib in
lemma arrow_weakEquivalence {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    weakEquivalences SSet.{v} (arrow hcof hfib f) := by
  apply (UniverseLift.weakEquivalences_iff_lift_anodyneQ_isIso
    hcof hfib (arrow hcof hfib f)).mpr
  have := OrdinaryBarBaseInvariance.localized_map_isIso hcof hfib f hs ht
  rw [arrow_map]
  dsimp only [transported]
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallAction
