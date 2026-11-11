module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarRowPresentations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftPadding
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LargeParameterSquare

/-!
# 中断した任意モデル源への一般化：ResolutionBarRowHomotopy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual bar homotopies from the reference to each row presentation。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0295][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0295
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual bar homotopies from the reference to each row presentation

The homotopy uses the same chosen augmentation arrow inside the existing
bar. No compatibility of independently chosen outer-frame lifts is assumed.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowHomotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ)

def sectionMap : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u}
    ((MixedBiresolutionComparison.functor (C := C)).obj
      (ResolutionBarRowPresentations.pair R n)) ⟶
      ResolutionBarEvaluation.bar R where
  app m := ↾fun x => (Functor.const (Fin (m.unop.len + 1))).obj
    (BarConstruction.sectionPoint (RightResolutionMapping.projection (C := C))
      MixedBiresolutionComparison.functor (d := ResolutionBarRowPresentations.pair R n)
      (𝟙 _) m x.down)
  naturality {_ _} _ := rfl

lemma padded_reference :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.paddingIso.{v, u}.app
      ((MixedBiresolutionComparison.functor (C := C)).obj R)).hom ≫
      BarConstruction.commaSection (RightResolutionMapping.projection (C := C))
        MixedBiresolutionComparison.functor
        (𝟙 ((RightResolutionMapping.projection (C := C)).obj R)) =
      ResolutionBarReference.sectionMap R := by
  ext m x
  rfl

/-- Both endpoints are the original maps into the same actual bar. -/
def homotopy : SSet.Homotopy (ResolutionBarReference.sectionMap R)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionRowMixedMapping.rowComparison n).app R) ≫
      sectionMap R n) := by
  let H := BarConstruction.commaSectionHomotopy (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor (d := R) (e := ResolutionBarRowPresentations.pair R n)
    (𝟙 ((RightResolutionMapping.projection (C := C)).obj R))
    (𝟙 ((RightResolutionMapping.projection (C := C)).obj R))
    (ResolutionBarRowPresentations.arrow R n) (by
      rw [ResolutionBarRowPresentations.arrow_base, Category.id_comp])
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.paddingIso.{v, u}.app
      ((MixedBiresolutionComparison.functor (C := C)).obj R)).hom
      (𝟙 _) H)
    (by ext m x; rfl) (by ext m x; rfl)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma image_eq : L.map (ResolutionBarReference.sectionMap R) =
    L.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionRowMixedMapping.rowComparison n).app R)) ≫
      L.map (sectionMap R n) :=
  (AnodyneHomotopy.map_homotopy_eq L hL (homotopy R n)).trans (L.map_comp _ _)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma section_isIso_iff : IsIso (AnodyneHomotopy.anodyneQ.map
    (ResolutionBarReference.sectionMap R)) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map (sectionMap R n)) := by
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionRowMixedMapping.rowComparison n).app R))) :=
    (UniverseLift.weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib _).mp
      (ResolutionRowMixedMapping.rowComparison_weakEquivalence hcof hfib R n)
  rw [image_eq R n AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)]
  exact isIso_comp_left_iff _ _

include hcof hfib in
lemma right_isIso_iff_row : IsIso (AnodyneHomotopy.anodyneQ.map
    ((BarConstruction.spanRight (RightResolutionMapping.projection (C := C))
      MixedBiresolutionComparison.functor).app R)) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map (sectionMap R n)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have h := BarConstruction.spanRight_isIso_iff_section
    (RightResolutionMapping.projection (C := C)) MixedBiresolutionComparison.functor Q
    (Localization.inverts Q SSet.anodyneExtensions) R
  have hpad : IsIso (Q.map (BarConstruction.commaSection
      (RightResolutionMapping.projection (C := C)) MixedBiresolutionComparison.functor
      (𝟙 ((RightResolutionMapping.projection (C := C)).obj R)))) ↔
      IsIso (Q.map (ResolutionBarReference.sectionMap R)) := by
    have := Functor.map_isIso (F := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.paddingIso.{v, u}.app
        ((MixedBiresolutionComparison.functor (C := C)).obj R)).hom
    rw [← padded_reference, Q.map_comp]
    exact (isIso_comp_left_iff _ _).symm
  exact h.trans (hpad.trans (section_isIso_iff R n hcof hfib))

include hcof hfib in
lemma natural_right_isIso_iff_rows :
    IsIso (Functor.whiskerRight
      (BarConstruction.spanRight (RightResolutionMapping.projection (C := C))
        MixedBiresolutionComparison.functor) AnodyneHomotopy.anodyneQ) ↔
      ∀ R' : RightResolutionMapping.Index C, IsIso (AnodyneHomotopy.anodyneQ.map
        (sectionMap R' (op (SimplexCategory.mk 0)))) := by
  let α := Functor.whiskerRight
    (BarConstruction.spanRight (RightResolutionMapping.projection (C := C))
      MixedBiresolutionComparison.functor) AnodyneHomotopy.anodyneQ
  constructor
  · intro h R'
    have : IsIso α := h
    exact (right_isIso_iff_row R' (op (SimplexCategory.mk 0)) hcof hfib).mp
      (inferInstanceAs (IsIso (α.app R')))
  · intro h
    have (R' : RightResolutionMapping.Index C) : IsIso (α.app R') :=
      (right_isIso_iff_row R' (op (SimplexCategory.mk 0)) hcof hfib).mpr (h R')
    exact NatIso.isIso_of_isIso_app α

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowHomotopy
