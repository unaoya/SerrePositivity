module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordResolution
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFixedSource

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual free resolution with the original base as its literal object set。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0168][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0168
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual free resolution with the original base as its literal object set

The category in every degree is the existing generator category. The
ordinary simplex maps are transported from the proved free-path resolution;
the augmentation proves their object maps are identities.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedSource
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
variable (C : Type u) [Category.{v} C]

abbrev source := OrdinaryBarWordResolution.source C

def comparison (n : SimplexCategoryᵒᵖ) : degree (D C) (n.unop.len + 1) ⟶ (source C).obj n :=
  eqToHom (degree_power (D C) (n.unop.len + 1))

instance comparison_isIso (n : SimplexCategoryᵒᵖ) : IsIso (comparison C n) := by
  unfold comparison
  infer_instance

def diagram : SimplicialObject Cat.{max u v, u} where
  obj n := degree (D C) (n.unop.len + 1)
  map {n m} θ := comparison C n ≫ (source C).map θ ≫ inv (comparison C m)
  map_id n := by simp
  map_comp f g := by simp [Category.assoc]

def comparisonIso : diagram C ≅ source C :=
  NatIso.ofComponents (fun n => asIso (comparison C n)) (by
    intro n m θ
    change (_ ≫ _ ≫ inv _) ≫ _ = _
    simp [Category.assoc])

def augmentation : diagram C ⟶ (Functor.const _).obj (OrdinaryBarWordResolution.base C) :=
  (comparisonIso C).hom ≫ OrdinaryBarWordResolution.sourceAugmentation C

def projection (n : SimplexCategoryᵒᵖ) : (diagram C).obj n ⥤ D C :=
  ((augmentation C).app n).toFunctor ⋙ ULiftHom.down.{v, u, u} (C := D C)

lemma projection_eq (n : SimplexCategoryᵒᵖ) : projection C n =
    OrdinaryBarFreeResolutionChoices.augmentation (C := C) n.unop.len := by
  have h := OrdinaryBarFreeResolutionNaturalChoice.augmentation_comparison (C := C) n.unop.len
  have hh := congrArg
    (fun f : degree (D C) (n.unop.len + 1) ⟶ OrdinaryBarWordResolution.base C =>
      f.toFunctor ⋙ ULiftHom.down.{v, u, u} (C := D C)) h
  change OrdinaryBarFreeResolutionChoices.augmentation (C := C) n.unop.len = projection C n at hh
  exact hh.symm

lemma projection_obj (n : SimplexCategoryᵒᵖ) (X : D C) : (projection C n).obj X = X := by
  rw [projection_eq]
  exact OrdinaryBarFreeAmbientFamilies.augmentation_obj n.unop.len X

lemma projection_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((diagram C).map θ).toFunctor ⋙ projection C m = projection C n := by
  have h := congrArg Cat.Hom.toFunctor ((augmentation C).naturality θ)
  change ((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor =
    ((augmentation C).app n).toFunctor ⋙ 𝟭 _ at h
  change (((diagram C).map θ).toFunctor ⋙ ((augmentation C).app m).toFunctor) ⋙
    ULiftHom.down.{v, u, u} (C := D C) = _
  rw [h, CategoryTheory.Functor.comp_id]
  rfl

lemma map_obj {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : D C) :
    ((diagram C).map θ).toFunctor.obj X = X := by
  have h := congr($(projection_naturality C θ).obj X)
  change (projection C m).obj (((diagram C).map θ).toFunctor.obj X) =
    (projection C n).obj X at h
  rw [projection_obj, projection_obj] at h
  exact h

def literalMap {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) : (diagram C).obj n ⥤ (diagram C).obj m where
  obj X := X
  map {X Y} f := eqToHom (map_obj C θ X).symm ≫ ((diagram C).map θ).toFunctor.map f ≫
    eqToHom (map_obj C θ Y)
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

lemma literalMap_eq {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    literalMap C θ = ((diagram C).map θ).toFunctor := by
  refine CategoryTheory.Functor.ext (fun X => (map_obj C θ X).symm) ?_
  intro X Y f
  simp [literalMap]

def literal : SimplicialObject Cat.{max u v, u} where
  obj n := (diagram C).obj n
  map θ := (literalMap C θ).toCatHom
  map_id n := by
    apply Cat.Hom.ext
    rw [literalMap_eq]
    exact congrArg Cat.Hom.toFunctor ((diagram C).map_id n)
  map_comp f g := by
    apply Cat.Hom.ext
    change literalMap C (f ≫ g) = literalMap C f ⋙ literalMap C g
    rw [literalMap_eq, literalMap_eq, literalMap_eq]
    exact congrArg Cat.Hom.toFunctor ((diagram C).map_comp f g)

lemma literal_eq : literal C = diagram C := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m θ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Cat.Hom.ext (literalMap_eq C θ)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedSource
