module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftIndependence

/-!
# 中断した任意モデル源への一般化：FramedMappingLocalization

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Natural localization comparison for the framed Kan bifunctor。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0088][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0088
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Natural localization comparison for the framed Kan bifunctor

The comparison is an isomorphism of the entire two-variable functors after
localizing spaces. Equality of parallel source choices is proved on full
localized mapping spaces, rather than only their components. Strict descent
with values in SSet is still a separate construction.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.FramedResolution
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{v})]

abbrev localizedRaw : (FramedResolution C)ᵒᵖ ⥤ FibrantObject C ⥤ H :=
  forget.op ⋙ ResolutionObject.hom ⋙ (Functor.whiskeringRight _ SSet.{v} H).obj L

abbrev localizedHom : (FramedResolution C)ᵒᵖ ⥤ FibrantObject C ⥤ H :=
  fibrantHom hcof hfib ⋙ (Functor.whiskeringRight _ SSet.{v} H).obj L

def localizedComparison : localizedRaw (C := C) L ⟶ localizedHom (C := C) hcof hfib L where
  app X := Functor.whiskerRight
    (Functor.whiskerLeft FibrantObject.ι ((comparison hcof hfib).app X)) L
  naturality {X Y} f := by
    apply NatTrans.ext
    funext Z
    exact (L.map_comp _ _).symm.trans
      ((congrArg L.map (ResolutionLiftPrecomposition.kan_comparison hcof hfib
        f.unop.map (frameMap f.unop) Z.obj)).trans (L.map_comp _ _))

instance localizedComparison_isIso : IsIso (localizedComparison (C := C) hcof hfib L) := by
  have : ∀ X, IsIso ((localizedComparison (C := C) hcof hfib L).app X) := by
    intro X
    have : ∀ Z, IsIso (((localizedComparison (C := C) hcof hfib L).app X).app Z) := by
      intro Z
      exact Localization.inverts L (weakEquivalences SSet.{v}) _
        (comparison_weakEquivalence hcof hfib X Z.obj)
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- A natural isomorphism in both variables, with the actual comparison maps as components. -/
abbrev localizedComparisonIso : localizedRaw (C := C) L ≅ localizedHom (C := C) hcof hfib L :=
  asIso (localizedComparison (C := C) hcof hfib L)

lemma localized_map_eq_of_base_eq {X Y : (FramedResolution C)ᵒᵖ} (f g : X ⟶ Y)
    (h : f.unop.map.base = g.unop.map.base) (Z : FibrantObject C) :
    L.map (((hom hcof hfib).map f).app Z.obj) =
      L.map (((hom hcof hfib).map g).app Z.obj) := by
  have : IsIso (((localizedComparison (C := C) hcof hfib L).app X).app Z) := inferInstance
  apply (cancel_epi (((localizedComparison (C := C) hcof hfib L).app X).app Z)).mp
  have he := ResolutionObject.hom_map_eq_of_base_eq hcof L
    (Quiver.Hom.op f.unop.map) (Quiver.Hom.op g.unop.map) h Z
  have hf := congr_app ((localizedComparison (C := C) hcof hfib L).naturality f) Z
  have hg := congr_app ((localizedComparison (C := C) hcof hfib L).naturality g) Z
  exact hf.symm.trans ((congrArg
    (fun q => q ≫ ((localizedComparison (C := C) hcof hfib L).app Y).app Z) he).trans hg)

end SerrePositivity.HomotopyFunctionComplex.FramedResolution
