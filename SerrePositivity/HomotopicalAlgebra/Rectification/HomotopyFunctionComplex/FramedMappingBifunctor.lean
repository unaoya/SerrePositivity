module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FramedResolutionCategory

/-!
# 中断した任意モデル源への一般化：FramedMappingBifunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A strict Kan-valued bifunctor on actual framed resolutions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0087][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0087
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A strict Kan-valued bifunctor on actual framed resolutions

The source variable retains actual frame maps. Its unit and composition
laws hold strictly, with values in the original Hom universe. This does
not assert descent to the undecorated base category.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.FramedResolution
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev raw : (FramedResolution C)ᵒᵖ ⥤ C ⥤ SSet.{v} :=
  innerDiagrams.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

/-- Source change is the actual previously constructed Kan source map. -/
def hom : (FramedResolution C)ᵒᵖ ⥤ C ⥤ SSet.{v} where
  obj X := KanLiftAction.targetFunctor hcof hfib X.unop.inner
  map f := ResolutionLiftPrecomposition.kanTargetNatTrans hcof hfib f.unop.map (frameMap f.unop)
  map_id X := by
    apply NatTrans.ext
    funext Z
    exact ResolutionLiftPrecomposition.kanTargetMap_identity hcof hfib X.unop.inner Z
  map_comp f g := by
    apply NatTrans.ext
    funext Z
    exact ResolutionLiftPrecomposition.kanTargetMap_compose hcof hfib g.unop.map f.unop.map
      (frameMap g.unop) (frameMap f.unop) Z

/-- A natural comparison in both variables, on all actual framed morphisms. -/
def comparison : raw (C := C) ⟶ hom hcof hfib where
  app X := KanLiftAction.comparisonNatTrans hcof hfib X.unop.inner
  naturality {X Y} f := by
    apply NatTrans.ext
    funext Z
    exact ResolutionLiftPrecomposition.kan_comparison hcof hfib f.unop.map (frameMap f.unop) Z

@[simp]
lemma hom_map_source {X Y : (FramedResolution C)ᵒᵖ} (f : X ⟶ Y) (Z : C) :
    ((hom hcof hfib).map f).app Z =
      ResolutionLiftPrecomposition.kanTargetMap hcof hfib f.unop.map (frameMap f.unop) Z := rfl

lemma hom_kanComplex (X : (FramedResolution C)ᵒᵖ) (Z : C) :
    SSet.KanComplex (((hom hcof hfib).obj X).obj Z) :=
  KanLiftAction.target_kanComplex hcof hfib X.unop.inner Z

lemma comparison_weakEquivalence (X : (FramedResolution C)ᵒᵖ) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (((comparison hcof hfib).app X).app Z) :=
  KanLiftAction.comparison_weakEquivalence hcof hfib X.unop.inner Z

lemma hom_source_weakEquivalence {X Y : (FramedResolution C)ᵒᵖ} (f : X ⟶ Y)
    (hf : weakEquivalences C f.unop.map.base) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (((hom hcof hfib).map f).app Z) :=
  ResolutionLiftPrecomposition.kanTargetMap_weakEquivalence hcof hfib f.unop.map
    (frameMap f.unop) hf Z

lemma hom_target_weakEquivalence (X : (FramedResolution C)ᵒᵖ) {Z Z' : C}
    [IsFibrant Z] [IsFibrant Z'] (f : Z ⟶ Z') (hf : weakEquivalences C f) :
    weakEquivalences SSet.{v} (((hom hcof hfib).obj X).map f) :=
  KanLiftAction.target_map_weakEquivalence hcof hfib X.unop.inner f hf

/-- Restriction of the comparison to fibrant targets retains both-variable naturality. -/
abbrev fibrantHom : (FramedResolution C)ᵒᵖ ⥤ FibrantObject C ⥤ SSet.{v} :=
  hom hcof hfib ⋙ (Functor.whiskeringLeft (FibrantObject C) C SSet.{v}).obj FibrantObject.ι

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

/-- The strict framed bifunctor has the required ordinary localized components. -/
def piZeroEquiv (X : (FramedResolution C)ᵒᵖ) (Z : C) [IsFibrant Z] :
    SSet.π₀ (((hom hcof hfib).obj X).obj Z) ≃
      (Q.obj X.unop.inner.base ⟶ Q.obj Z) :=
  KanLiftAction.piZeroLocalizationEquiv hcof hfib Q X.unop.inner Z

lemma piZero_naturality_source {X Y : (FramedResolution C)ᵒᵖ} (f : X ⟶ Y)
    (Z : C) [IsFibrant Z] (z : SSet.π₀ (((hom hcof hfib).obj X).obj Z)) :
    piZeroEquiv hcof hfib Q Y Z (SSet.mapπ₀ (((hom hcof hfib).map f).app Z) z) =
      Q.map f.unop.map.base ≫ piZeroEquiv hcof hfib Q X Z z :=
  ResolutionLiftPrecomposition.piZero_naturality_source hcof hfib Q f.unop.map
    (frameMap f.unop) Z z

lemma piZero_naturality_target (X : (FramedResolution C)ᵒᵖ) {Z Z' : FibrantObject C}
    (f : Z ⟶ Z') (z : SSet.π₀ (((hom hcof hfib).obj X).obj Z.obj)) :
    piZeroEquiv hcof hfib Q X Z'.obj (SSet.mapπ₀ (((hom hcof hfib).obj X).map f.hom) z) =
      piZeroEquiv hcof hfib Q X Z.obj z ≫ Q.map f.hom := by
  obtain ⟨x, rfl⟩ :=
    (KanLiftAction.comparison_piZero_bijective hcof hfib X.unop.inner Z.obj).surjective z
  have hc := congrArg (fun q => SSet.mapπ₀ q x)
    ((KanLiftAction.comparisonNatTrans hcof hfib X.unop.inner).naturality f.hom)
  have h := ResolutionObject.piZeroEquiv_naturality_target Q
    (Opposite.op X.unop.inner) f x
  have hZ := ResolutionLiftPrecomposition.piZero_comparison hcof hfib Q X.unop.inner Z.obj x
  have hZ' := ResolutionLiftPrecomposition.piZero_comparison hcof hfib Q X.unop.inner Z'.obj
    (SSet.mapπ₀ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom X.unop.inner.resolution.obj).map f.hom) x)
  simp only [SSet.mapπ₀_comp_apply] at hc
  exact (congrArg (piZeroEquiv hcof hfib Q X Z'.obj) hc.symm).trans
    (hZ'.trans (h.trans (congrArg (fun q => q ≫ Q.map f.hom) hZ.symm)))

include Q in
/-- At π₀ the actual frame choices act identically whenever the base maps agree. -/
lemma piZero_map_eq_of_base_eq {X Y : (FramedResolution C)ᵒᵖ} (f g : X ⟶ Y)
    (h : f.unop.map.base = g.unop.map.base) (Z : C) [IsFibrant Z] :
    SSet.mapπ₀ (((hom hcof hfib).map f).app Z) =
      SSet.mapπ₀ (((hom hcof hfib).map g).app Z) := by
  funext z
  apply (piZeroEquiv hcof hfib Q Y Z).injective
  rw [piZero_naturality_source, piZero_naturality_source, h]

end SerrePositivity.HomotopyFunctionComplex.FramedResolution
