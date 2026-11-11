module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeAmbientFamilies

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Coherent ambient families with the original objects as literal endpoints。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0171][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0171
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Coherent ambient families with the original objects as literal endpoints

The augmentation identifies the choice objects with the original labels.
Transporting evaluation along these proved equalities yields functors whose
object functions are the specified ambient objects in every degree.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeResolutionSeed
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma augmentation_obj (n : ℕ) (X : D C) :
    (OrdinaryBarFreeResolutionChoices.augmentation (C := C) n).obj X = X := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma choice_base (n : ℕ) (X : D C) :
    ((OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n).obj X).base = X := by
  have hh := congrArg (fun F => F.obj X)
    (OrdinaryBarFreeResolutionChoices.projection_eq_augmentation (C := C) hcof hfib P n)
  exact hh.trans (augmentation_obj n X)

def evaluated (n : ℕ) : degree (D C) (n + 1) ⥤ ParameterCategory.Object (parameters P n) :=
  OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n ⋙
    OrdinaryBarChoiceCategory.evaluation hcof hfib (parameters P n)

def ambientObject (n : ℕ) (X : D C) : ParameterCategory.Object (parameters P n) :=
  ⟨OrdinaryBarRetractSystem.ambient hcof hfib X⟩

lemma evaluated_obj (n : ℕ) (X : D C) :
    (evaluated hcof hfib P n).obj X = ambientObject hcof hfib P n X :=
  congrArg (ambientObject hcof hfib P n) (choice_base hcof hfib P n X)

def fixedAction (n : ℕ) : degree (D C) (n + 1) ⥤ ParameterCategory.Object (parameters P n) where
  obj X := ambientObject hcof hfib P n X
  map {X Y} f := eqToHom (evaluated_obj hcof hfib P n X).symm ≫
    (evaluated hcof hfib P n).map f ≫ eqToHom (evaluated_obj hcof hfib P n Y)
  map_id _ := by simp
  map_comp f g := by simp [Category.assoc]

lemma fixedAction_eq (n : ℕ) : fixedAction (C := C) hcof hfib P n = evaluated hcof hfib P n := by
  refine CategoryTheory.Functor.ext (fun X => (evaluated_obj hcof hfib P n X).symm) ?_
  intro X Y f
  simp [fixedAction]

lemma fixedAction_face (n : ℕ) (i : Fin (n + 2)) : fixedAction (C := C) hcof hfib P (n + 1) ⋙
    ParameterCategory.reindex (P ◁ SSet.stdSimplex.δ i) =
      fixedFace (D C) (n + 1) i ⋙ fixedAction hcof hfib P n := by
  rw [fixedAction_eq, fixedAction_eq, evaluated, evaluated, CategoryTheory.Functor.assoc,
    ← OrdinaryBarChoiceCategory.reindex_evaluation, ← CategoryTheory.Functor.assoc,
    OrdinaryBarFreeResolutionChoices.diagram_face, CategoryTheory.Functor.assoc]

lemma fixedAction_degeneracy (n : ℕ) (i : Fin (n + 1)) : degeneracyFunctor (D C) n i ⋙
    fixedAction hcof hfib P (n + 1) = fixedAction hcof hfib P n ⋙
      ParameterCategory.reindex (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) := by
  rw [fixedAction_eq, fixedAction_eq, evaluated, evaluated, ← CategoryTheory.Functor.assoc,
    OrdinaryBarFreeResolutionChoices.diagram_degeneracy, CategoryTheory.Functor.assoc,
    OrdinaryBarChoiceCategory.reindex_evaluation, ← CategoryTheory.Functor.assoc]

/-- The literal ambient-to-ambient family on the original two endpoints. -/
def family (n : ℕ) {X Y : D C} (f : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    OrdinaryBarRetractSystem.ambient hcof hfib X ⊗ parameters P n ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib Y := (fixedAction hcof hfib P n).map f

lemma family_id (n : ℕ) (X : D C) :
    family hcof hfib P n (FreeGeneratorCategories.identity (D C) (n + 1) X) =
      ParameterComposition.const (parameters P n)
        (𝟙 (OrdinaryBarRetractSystem.ambient hcof hfib X)) :=
  (fixedAction hcof hfib P n).map_id X

lemma family_comp (n : ℕ) {X Y Z : degree (D C) (n + 1)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    family hcof hfib P n (f ≫ g) =
      ParameterComposition.comp (family hcof hfib P n f) (family hcof hfib P n g) :=
  (fixedAction hcof hfib P n).map_comp f g

lemma family_face (n : ℕ) (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (f : X ⟶ Y) :
    ParameterComposition.substitute (P ◁ SSet.stdSimplex.δ i) (family hcof hfib P (n + 1) f) =
      family hcof hfib P n ((fixedFace (D C) (n + 1) i).map f) :=
  congr($(fixedAction_face (C := C) hcof hfib P n i).map f)

lemma family_degeneracy (n : ℕ) (i : Fin (n + 1)) {X Y : degree (D C) (n + 1)} (f : X ⟶ Y) :
    family hcof hfib P (n + 1) ((degeneracyFunctor (D C) n i).map f) =
      ParameterComposition.substitute (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) (family hcof hfib P n f) :=
  congr($(fixedAction_degeneracy (C := C) hcof hfib P n i).map f)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies
