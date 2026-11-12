module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant

/-!
# 中断した任意モデル源への一般化：ResolutionCategoryHom

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual mapping spaces on all resolutions and fibrant targets。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0300][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0300
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual mapping spaces on all resolutions and fibrant targets

Strict functoriality is in resolution morphisms, not in independent chosen
lifts of base morphisms. The source is an arbitrary model category. No
functorial factorization, presentability, or enrichment is assumed.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionObject
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The n-simplices are actual maps from the resolution's n-th term. -/
abbrev hom : (ResolutionObject C)ᵒᵖ ⥤ FibrantObject C ⥤ SSet.{v} :=
  diagrams.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
    (Functor.whiskeringLeft (FibrantObject C) C SSet.{v}).obj FibrantObject.ι

@[simp]
lemma hom_obj (X : (ResolutionObject C)ᵒᵖ) (Y : FibrantObject C)
    (n : SimplexCategoryᵒᵖ) :
    (((hom.obj X).obj Y).obj n) = (X.unop.resolution.obj.obj n.unop ⟶ Y.obj) := rfl

lemma hom_kanComplex (X : (ResolutionObject C)ᵒᵖ) (Y : FibrantObject C) :
    SSet.KanComplex ((hom.obj X).obj Y) :=
  cosimplicialHom_kanComplex _ X.unop.resolution.cofibrant
    X.unop.resolution.homotopicallyConstant Y.obj

section WeakEquivalences
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma hom_map_source_weakEquivalence {X X' : (ResolutionObject C)ᵒᵖ}
    (f : X ⟶ X') (hf : weakEquivalences C f.unop.base) (Y : FibrantObject C) :
    weakEquivalences SSet.{v} ((hom.map f).app Y) :=
  cosimplicialHomMap_weakEquivalence hcof f.unop.diagram
    X'.unop.resolution.cofibrant X.unop.resolution.cofibrant
    (diagram_weakEquivalence f.unop hf) Y.obj

include hcof in
lemma hom_map_target_weakEquivalence (X : (ResolutionObject C)ᵒᵖ)
    {Y Y' : FibrantObject C} (f : Y ⟶ Y') (hf : weakEquivalences C f.hom) :
    weakEquivalences SSet.{v} ((hom.obj X).map f) := by
  have : WeakEquivalence f.hom := ⟨hf⟩
  exact cosimplicialHom_weakEquivalence_of_fibrant hcof _
    X.unop.resolution.cofibrant f.hom

end WeakEquivalences

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

/-- Components identify with morphisms in any ordinary localization. -/
def piZeroEquiv (X : (ResolutionObject C)ᵒᵖ) (Y : FibrantObject C) :
    SSet.π₀ ((hom.obj X).obj Y) ≃ (Q.obj X.unop.base ⟶ Q.obj Y.obj) :=
  resolutionPiZeroLocalizationEquiv Q X.unop.resolution Y.obj

@[simp]
lemma piZeroEquiv_mk (X : (ResolutionObject C)ᵒᵖ) (Y : FibrantObject C)
    (f : X.unop.resolution.obj.obj (SimplexCategory.mk 0) ⟶ Y.obj) :
    piZeroEquiv Q X Y (SSet.π₀.mk f) =
      (resolutionZeroLocalizationIso Q X.unop.resolution).inv ≫ Q.map f :=
  resolutionPiZeroLocalizationEquiv_mk Q X.unop.resolution f

lemma piZeroEquiv_naturality_source {X X' : (ResolutionObject C)ᵒᵖ}
    (f : X ⟶ X') (Y : FibrantObject C) (z : SSet.π₀ ((hom.obj X).obj Y)) :
    piZeroEquiv Q X' Y (SSet.mapπ₀ ((hom.map f).app Y) z) =
      Q.map f.unop.base ≫ piZeroEquiv Q X Y z := by
  obtain ⟨g, rfl⟩ := SSet.π₀.mk_surjective z
  change X.unop.resolution.obj.obj (SimplexCategory.mk 0) ⟶ Y.obj at g
  change piZeroEquiv Q X' Y
    (SSet.π₀.mk (f.unop.diagram.app (SimplexCategory.mk 0) ≫ g)) = _
  rw [piZeroEquiv_mk, piZeroEquiv_mk, Q.map_comp]
  have h := congr_app f.unop.over (SimplexCategory.mk 0)
  change f.unop.diagram.app (SimplexCategory.mk 0) ≫
      X.unop.resolution.augmentation.app (SimplexCategory.mk 0) =
      X'.unop.resolution.augmentation.app (SimplexCategory.mk 0) ≫ f.unop.base at h
  have hn : Q.map (f.unop.diagram.app (SimplexCategory.mk 0)) ≫
      (resolutionZeroLocalizationIso Q X.unop.resolution).hom =
      (resolutionZeroLocalizationIso Q X'.unop.resolution).hom ≫ Q.map f.unop.base := by
    change Q.map (f.unop.diagram.app (SimplexCategory.mk 0)) ≫
        Q.map (X.unop.resolution.augmentation.app (SimplexCategory.mk 0)) =
      Q.map (X'.unop.resolution.augmentation.app (SimplexCategory.mk 0)) ≫ Q.map f.unop.base
    simpa only [Functor.map_comp] using congrArg Q.map h
  have hi : (resolutionZeroLocalizationIso Q X'.unop.resolution).inv ≫
      Q.map (f.unop.diagram.app (SimplexCategory.mk 0)) =
      Q.map f.unop.base ≫ (resolutionZeroLocalizationIso Q X.unop.resolution).inv := by
    apply (cancel_mono (resolutionZeroLocalizationIso Q X.unop.resolution).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hi, Category.assoc]

lemma piZeroEquiv_naturality_target (X : (ResolutionObject C)ᵒᵖ)
    {Y Y' : FibrantObject C} (f : Y ⟶ Y') (z : SSet.π₀ ((hom.obj X).obj Y)) :
    piZeroEquiv Q X Y' (SSet.mapπ₀ ((hom.obj X).map f) z) =
      piZeroEquiv Q X Y z ≫ Q.map f.hom := by
  obtain ⟨g, rfl⟩ := SSet.π₀.mk_surjective z
  change X.unop.resolution.obj.obj (SimplexCategory.mk 0) ⟶ Y.obj at g
  change piZeroEquiv Q X Y' (SSet.π₀.mk (g ≫ f.hom)) = _
  rw [piZeroEquiv_mk, piZeroEquiv_mk, Q.map_comp, Category.assoc]

include Q in
/-- At the component level all lifts of the same base map act identically. -/
lemma map_piZero_eq_of_base_eq {X X' : (ResolutionObject C)ᵒᵖ}
    (f g : X ⟶ X') (h : f.unop.base = g.unop.base) (Y : FibrantObject C) :
    SSet.mapπ₀ ((hom.map f).app Y) = SSet.mapπ₀ ((hom.map g).app Y) := by
  funext z
  apply (piZeroEquiv Q X' Y).injective
  rw [piZeroEquiv_naturality_source, piZeroEquiv_naturality_source, h]

end SerrePositivity.HomotopyFunctionComplex.ResolutionObject
