module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FramedResolutionCategory
public import SerrePositivity.HomotopicalAlgebra.Replacement.FibrantCategory
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# 中断した任意モデル源への一般化：DualResolutionTargets

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual fibrant target presentations from resolutions in the opposite model。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0084][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0084
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual fibrant target presentations from resolutions in the opposite model

The index categories reuse the existing resolution categories by duality.
Every degree supplies a genuine fibrant replacement presentation, naturally
in all actual comparison maps. No functorial choice on the base is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open SerrePositivity.ModelReplacement

namespace SerrePositivity.HomotopyFunctionComplex.DualResolutionTargets
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev Index := (ResolutionObject Cᵒᵖ)ᵒᵖ
abbrev FramedIndex := (FramedResolution Cᵒᵖ)ᵒᵖ

abbrev base : Index C ⥤ C := ResolutionObject.projection.op ⋙ unopUnop C
abbrev framedForget : FramedIndex C ⥤ Index C := FramedResolution.forget.op
abbrev framedBase : FramedIndex C ⥤ C := framedForget C ⋙ base C

def diagram (Y : Index C) : SimplexCategoryᵒᵖ ⥤ C where
  obj n := (Y.unop.resolution.obj.obj n.unop).unop
  map f := (Y.unop.resolution.obj.map f.unop).unop
  map_id _ := by simp
  map_comp _ _ := by simp

def coaugmentation (Y : Index C) : (Functor.const SimplexCategoryᵒᵖ).obj ((base C).obj Y) ⟶
    diagram C Y where
  app n := (Y.unop.resolution.augmentation.app n.unop).unop
  naturality {n m} f := by
    apply Quiver.Hom.op_inj
    have h := Y.unop.resolution.augmentation.naturality f.unop
    change Y.unop.resolution.obj.map f.unop ≫
      Y.unop.resolution.augmentation.app n.unop =
        Y.unop.resolution.augmentation.app m.unop ≫ 𝟙 _ at h
    change Y.unop.resolution.augmentation.app m.unop ≫ 𝟙 _ =
      Y.unop.resolution.obj.map f.unop ≫ Y.unop.resolution.augmentation.app n.unop
    exact h.symm

lemma isFibrant_obj (Y : Index C) (n : SimplexCategoryᵒᵖ) :
    IsFibrant ((diagram C Y).obj n) := by
  have : IsCofibrant (Y.unop.resolution.obj.obj n.unop) :=
    Y.unop.resolution.isCofibrant_obj n.unop
  exact (isFibrant_iff_of_isTerminal (initial.to (Y.unop.resolution.obj.obj n.unop)).unop
    (terminalUnopOfInitial initialIsInitial)).mpr inferInstance

lemma coaugmentation_trivial (Y : Index C) (n : SimplexCategoryᵒᵖ) :
    trivialCofibrations C ((coaugmentation C Y).app n) := by
  have h := Reedy.trivialFibration_app Reedy.simplex Y.unop.resolution.augmentation
    Y.unop.resolution.trivial n.unop
  rw [trivialFibrations_op] at h
  exact h

/-- Every simplicial degree is an actual object of the existing replacement category. -/
def presentation (n : SimplexCategoryᵒᵖ) : Index C ⥤ FibrantReplacementObject C where
  obj Y := ⟨(base C).obj Y, (diagram C Y).obj n, (coaugmentation C Y).app n,
    coaugmentation_trivial C Y n, isFibrant_obj C Y n⟩
  map f :=
    { base := f.unop.base.unop
      map := (f.unop.diagram.app n.unop).unop
      under := by
        apply Quiver.Hom.op_inj
        change f.unop.diagram.app n.unop ≫ _ = _ ≫ f.unop.base
        exact congr_app f.unop.over n.unop }
  map_id _ := by apply FibrantReplacementObject.Hom.ext <;> rfl
  map_comp _ _ := by apply FibrantReplacementObject.Hom.ext <;> rfl

lemma presentation_projection (n : SimplexCategoryᵒᵖ) :
    presentation C n ⋙ FibrantReplacementObject.projection = base C := rfl

/-- Retain every target simplicial operator as an actual replacement comparison. -/
def presentations : SimplexCategoryᵒᵖ ⥤ Index C ⥤ FibrantReplacementObject C where
  obj n := presentation C n
  map f :=
    { app Y :=
        { base := 𝟙 _
          map := (diagram C Y).map f
          under := ((coaugmentation C Y).naturality f).symm }
      naturality {Y Z} g := by
        apply FibrantReplacementObject.Hom.ext
        · change g.unop.base.unop ≫ 𝟙 _ = 𝟙 _ ≫ g.unop.base.unop
          simp
        · apply Quiver.Hom.op_inj
          change Z.unop.resolution.obj.map f.unop ≫ g.unop.diagram.app _ =
            g.unop.diagram.app _ ≫ Y.unop.resolution.obj.map f.unop
          exact g.unop.diagram.naturality f.unop }
  map_id n := by
    apply NatTrans.ext
    funext Y
    apply FibrantReplacementObject.Hom.ext
    · rfl
    · exact (diagram C Y).map_id n
  map_comp f g := by
    apply NatTrans.ext
    funext Y
    apply FibrantReplacementObject.Hom.ext
    · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      simp
    · exact (diagram C Y).map_comp f g

lemma operator_weakEquivalence {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (Y : Index C) :
    weakEquivalences C (((presentations C).map f).app Y).map :=
  (FibrantReplacementObject.map_weakEquivalence_iff _).mpr ((weakEquivalences C).id_mem _)

abbrev framedPresentation (n : SimplexCategoryᵒᵖ) :
    FramedIndex C ⥤ FibrantReplacementObject C := framedForget C ⋙ presentation C n

/-- Objectwise existence is independent of a functorial replacement on C. -/
abbrev ofObject (Y : C) : FramedIndex C := op (FramedResolution.ofObject (op Y))

@[simp] lemma ofObject_base (Y : C) : (framedBase C).obj (ofObject C Y) = Y := rfl

def liftBase {Y Z : FramedIndex C}
    (f : (framedBase C).obj Y ⟶ (framedBase C).obj Z) : Y ⟶ Z :=
  (FramedResolution.liftBase f.op).op

@[simp] lemma liftBase_base {Y Z : FramedIndex C}
    (f : (framedBase C).obj Y ⟶ (framedBase C).obj Z) :
    (framedBase C).map (liftBase C f) = f := rfl

instance : (framedBase C).Full where
  map_surjective f := ⟨liftBase C f, rfl⟩

end SerrePositivity.HomotopyFunctionComplex.DualResolutionTargets
