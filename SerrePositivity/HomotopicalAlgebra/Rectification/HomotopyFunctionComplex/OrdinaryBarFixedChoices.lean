module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedSource

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFixedChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual coherent choices on the ordinary simplex diagram with fixed objects。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0166][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0166
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual coherent choices on the ordinary simplex diagram with fixed objects
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedChoices
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev target := OrdinaryBarParameterChoiceCategory.diagram (C := C) hcof hfib P

def transported : diagram C ⟶ target (C := C) hcof hfib P :=
  (comparisonIso C).hom ≫ OrdinaryBarFreeResolutionNaturalChoice.choices hcof hfib P

lemma transported_app (n : SimplexCategoryᵒᵖ) : (transported (C := C) hcof hfib P).app n =
    (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len).toCatHom := by
  rw [transported, NatTrans.comp_app, OrdinaryBarFreeResolutionNaturalChoice.choices_app]
  change comparison C n ≫ (eqToHom (degree_power (D C) (n.unop.len + 1)).symm ≫ _) = _
  simp [comparison]

def choices : literal C ⟶ target (C := C) hcof hfib P where
  app n := (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len).toCatHom
  naturality {n m} θ := by
    have h := (transported (C := C) hcof hfib P).naturality θ
    rw [transported_app, transported_app] at h
    change (literalMap C θ).toCatHom ≫ _ = _
    rw [show (literalMap C θ).toCatHom = (diagram C).map θ from Cat.Hom.ext (literalMap_eq C θ)]
    exact h

def action (n : SimplexCategoryᵒᵖ) : (literal C).obj n ⥤
    ParameterCategory.Object (OrdinaryBarFreeResolutionAction.parameters P n) :=
  OrdinaryBarFreeAmbientFamilies.fixedAction hcof hfib P n.unop.len

lemma action_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    literalMap C θ ⋙ action hcof hfib P m =
      action hcof hfib P n ⋙ ParameterCategory.reindex (P ◁ SSet.stdSimplex.map θ.unop) := by
  have h := congrArg Cat.Hom.toFunctor ((choices (C := C) hcof hfib P).naturality θ)
  change literalMap C θ ⋙ OrdinaryBarFreeResolutionChoices.diagram hcof hfib P m.unop.len =
    OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.map θ.unop) at h
  unfold action
  rw [OrdinaryBarFreeAmbientFamilies.fixedAction_eq, OrdinaryBarFreeAmbientFamilies.fixedAction_eq]
  unfold OrdinaryBarFreeAmbientFamilies.evaluated
  rw [← CategoryTheory.Functor.assoc, h, CategoryTheory.Functor.assoc,
    OrdinaryBarChoiceCategory.reindex_evaluation]
  rfl

lemma action_obj (n : SimplexCategoryᵒᵖ) (X : D C) : (action hcof hfib P n).obj X =
    OrdinaryBarFreeAmbientFamilies.ambientObject hcof hfib P n.unop.len X := rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedChoices
