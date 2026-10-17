module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeResolutionAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual ambient arrow families on the entire free resolution。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0178][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0178
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual ambient arrow families on the entire free resolution

Evaluation of the constructed choices is strictly compatible with every
simplex substitution. The native parameter-category functors preserve
composition and identity, and the underlying base functors are the original
augmentation. No descent to a strict small action on the base is asserted.
-/

@[expose] public section
universe v u r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction

abbrev parameters (P : SSet.{r}) (n : SimplexCategoryᵒᵖ) := P ⊗ SSet.stdSimplex.obj n.unop

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev source := OrdinaryBarFreeResolutionNaturalChoice.source (C := C)

def choicesAt (n : SimplexCategoryᵒᵖ) : (source (C := C)).obj n ⥤
    OrdinaryBarChoiceCategory.Object (C := C) hcof hfib (parameters P n) :=
  ((OrdinaryBarFreeResolutionNaturalChoice.choices hcof hfib P).app n).toFunctor

def action (n : SimplexCategoryᵒᵖ) : (source (C := C)).obj n ⥤
    ParameterCategory.Object (parameters P n) :=
  choicesAt hcof hfib P n ⋙ OrdinaryBarChoiceCategory.evaluation hcof hfib (parameters P n)

lemma action_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((source (C := C)).map θ).toFunctor ⋙ action hcof hfib P m =
      action hcof hfib P n ⋙ ParameterCategory.reindex (P ◁ SSet.stdSimplex.map θ.unop) := by
  have hh := congrArg Cat.Hom.toFunctor
    ((OrdinaryBarFreeResolutionNaturalChoice.choices (C := C) hcof hfib P).naturality θ)
  simp only [Cat.Hom.comp_toFunctor] at hh
  change ((source (C := C)).map θ).toFunctor ⋙ choicesAt hcof hfib P m =
    choicesAt hcof hfib P n ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ SSet.stdSimplex.map θ.unop) at hh
  rw [action, ← CategoryTheory.Functor.assoc, hh, CategoryTheory.Functor.assoc,
    OrdinaryBarChoiceCategory.reindex_evaluation, ← CategoryTheory.Functor.assoc]
  rfl

/-- The actual ambient object at a source object, without a change of parameter universe. -/
def object (n : SimplexCategoryᵒᵖ) (X : (source (C := C)).obj n) : SSet.{max u v} :=
  ((action hcof hfib P n).obj X).value

/-- Evaluate the whole choice extension, retaining the entire P times simplex parameter. -/
def family (n : SimplexCategoryᵒᵖ) {X Y : (source (C := C)).obj n} (f : X ⟶ Y) :
    object hcof hfib P n X ⊗ parameters P n ⟶ object hcof hfib P n Y :=
  (action hcof hfib P n).map f

lemma family_eq (n : SimplexCategoryᵒᵖ) {X Y : (source (C := C)).obj n} (f : X ⟶ Y) :
    family hcof hfib P n f = RelativeChoiceSpace.family _ _
      (((choicesAt hcof hfib P n).map f).extension) := rfl

lemma family_id (n : SimplexCategoryᵒᵖ) (X : (source (C := C)).obj n) :
    family hcof hfib P n (𝟙 X) = ParameterComposition.const (parameters P n)
      (𝟙 (object hcof hfib P n X)) := (action hcof hfib P n).map_id X

lemma family_comp (n : SimplexCategoryᵒᵖ) {X Y Z : (source (C := C)).obj n}
    (f : X ⟶ Y) (g : Y ⟶ Z) : family hcof hfib P n (f ≫ g) =
      ParameterComposition.comp (family hcof hfib P n f) (family hcof hfib P n g) :=
  (action hcof hfib P n).map_comp f g

/-- The base functor is the existing free-resolution augmentation followed by down. -/
def baseProjection (n : SimplexCategoryᵒᵖ) : (source (C := C)).obj n ⥤ Cᵒᵖ × C :=
  ((FreePathSimplicialResolution.augmentation (Cᵒᵖ × C)).app
    (SimplexCategory.rev.op.obj n)).toFunctor ⋙ ULiftHom.down.{v, u, u}
      (C := Cᵒᵖ × C)

lemma choicesAt_projection (n : SimplexCategoryᵒᵖ) :
    choicesAt hcof hfib P n ⋙ OrdinaryBarChoiceCategory.projection hcof hfib (parameters P n) =
      baseProjection (C := C) n := by
  have hh := congr($(OrdinaryBarFreeResolutionNaturalChoice.augmentation_eq_standard
    (C := C) hcof hfib P).app n)
  have hdown := congrArg
    (fun F : (source (C := C)).obj n ⟶ FreePathResolutionPresentation.base (Cᵒᵖ × C) =>
      F.toFunctor ⋙ ULiftHom.down.{v, u, u} (C := Cᵒᵖ × C)) hh
  change choicesAt hcof hfib P n ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib (parameters P n) = baseProjection n at hdown
  exact hdown

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction
