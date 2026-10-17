module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization
public import SerrePositivity.HomotopicalAlgebra.Replacement.FibrantLocalization

/-!
# 中断した任意モデル源への一般化：ReplacementMappingLocalization

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Independence of both actual replacement maps on full localized mapping spaces。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0275][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0275
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Independence of both actual replacement maps on full localized mapping spaces
-/

@[expose] public section
universe v u vS uS vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.ModelReplacement

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {S : Type uS} [Category.{vS} S] (L : SSet.{v} ⥤ S)
  [L.IsLocalization (weakEquivalences SSet.{v})]

lemma localized_source_map_eq {X X' : (FramedResolution C)ᵒᵖ} (f g : X ⟶ X')
    (h : f.unop.map.base = g.unop.map.base) (Y : FibrantReplacementObject C) :
    L.map (((hom hcof hfib).map f).app Y) = L.map (((hom hcof hfib).map g).app Y) :=
  FramedResolution.localized_map_eq_of_base_eq hcof hfib L f g h (FibrantObject.mk Y.obj)

lemma fibrantHom_inverts (X : (FramedResolution C)ᵒᵖ) :
    (weakEquivalences (FibrantObject C)).IsInvertedBy
      ((FramedResolution.fibrantHom hcof hfib).obj X ⋙ L) := by
  intro Y Y' f hf
  exact Localization.inverts L (weakEquivalences SSet.{v}) _
    (FramedResolution.hom_target_weakEquivalence hcof hfib X f.hom hf)

/-- Target comparison choices agree on the entire localized space, not just on components. -/
lemma localized_target_map_eq (X : (FramedResolution C)ᵒᵖ)
    {Y Y' : FibrantReplacementObject C} (f g : Y ⟶ Y') (h : f.base = g.base) :
    L.map (((hom hcof hfib).obj X).map f) = L.map (((hom hcof hfib).obj X).map g) :=
  FibrantReplacementObject.homotopical_map_eq_of_base_eq (weakEquivalences C).Q
    ((FramedResolution.fibrantHom hcof hfib).obj X ⋙ L)
    (fibrantHom_inverts hcof hfib L X) f g h

abbrev uncurried : ((FramedResolution C)ᵒᵖ × FibrantReplacementObject C) ⥤ SSet.{v} :=
  Functor.uncurry.obj (hom hcof hfib)

lemma uncurried_weakEquivalence
    {X X' : (FramedResolution C)ᵒᵖ × FibrantReplacementObject C} (f : X ⟶ X')
    (hs : weakEquivalences C f.1.unop.map.base) (ht : weakEquivalences C f.2.base) :
    weakEquivalences SSet.{v} ((uncurried hcof hfib).map f) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (source_weakEquivalence hcof hfib f.1 hs X.2)
    (target_weakEquivalence hcof hfib X'.1 f.2 ht)

lemma localized_uncurried_map_eq
    {X X' : (FramedResolution C)ᵒᵖ × FibrantReplacementObject C} (f g : X ⟶ X')
    (hs : f.1.unop.map.base = g.1.unop.map.base) (ht : f.2.base = g.2.base) :
    L.map ((uncurried hcof hfib).map f) = L.map ((uncurried hcof hfib).map g) := by
  change L.map ((((hom hcof hfib).map f.1).app X.2) ≫
    ((hom hcof hfib).obj X'.1).map f.2) =
    L.map ((((hom hcof hfib).map g.1).app X.2) ≫ ((hom hcof hfib).obj X'.1).map g.2)
  rw [L.map_comp, L.map_comp, localized_source_map_eq hcof hfib L f.1 g.1 hs,
    localized_target_map_eq hcof hfib L X'.1 f.2 g.2 ht]

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
