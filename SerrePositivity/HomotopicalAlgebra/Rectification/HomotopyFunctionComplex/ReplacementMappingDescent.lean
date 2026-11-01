module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementMappingLocalization

/-!
# 中断した任意モデル源への一般化：ReplacementMappingDescent

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Simultaneous ordinary descent of actual small replacement mapping spaces。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0274][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0274
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Simultaneous ordinary descent of actual small replacement mapping spaces

The selected values are small Kan complexes. The functor laws and natural
comparison are proved after localizing spaces, not in simplicial sets.
-/

@[expose] public section
universe v u vS uS
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.ModelReplacement

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev Index (C : Type u) [Category.{v} C] [ModelCategory C] :=
  (FramedResolution C)ᵒᵖ × FibrantReplacementObject C

abbrev projection : Index C ⥤ Cᵒᵖ × C :=
  FramedResolution.projection.op.prod FibrantReplacementObject.projection

/-- These are object choices, with no source or target functorial replacement assumed. -/
abbrev ofBase (X : Cᵒᵖ × C) : Index C :=
  (Opposite.op (FramedResolution.ofObject X.1.unop), FibrantReplacementObject.ofObject X.2)

def liftBase {X Y : Index C}
    (f : (projection (C := C)).obj X ⟶ (projection (C := C)).obj Y) : X ⟶ Y :=
  ((FramedResolution.liftBase f.1.unop).op, FibrantReplacementObject.liftBase f.2)

@[simp]
lemma projection_liftBase {X Y : Index C}
    (f : (projection (C := C)).obj X ⟶ (projection (C := C)).obj Y) :
    (projection (C := C)).map (liftBase f) = f := rfl

instance : (projection (C := C)).Full where
  map_surjective f := ⟨liftBase f, rfl⟩

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- An actual weak equivalence from the selected presentation value to any given one. -/
def presentationMap (X : Index C) :
    (uncurried hcof hfib).obj (ofBase ((projection (C := C)).obj X)) ⟶
      (uncurried hcof hfib).obj X :=
  (uncurried hcof hfib).map (liftBase (X := ofBase ((projection (C := C)).obj X))
    (Y := X) (𝟙 ((projection (C := C)).obj X)))

lemma presentationMap_weakEquivalence (X : Index C) :
    weakEquivalences SSet.{v} (presentationMap hcof hfib X) :=
  uncurried_weakEquivalence hcof hfib _
    ((weakEquivalences C).id_mem _) ((weakEquivalences C).id_mem _)

variable {S : Type uS} [Category.{vS} S] (L : SSet.{v} ⥤ S)
  [L.IsLocalization (weakEquivalences SSet.{v})]

/-- Both variables descend at once, using the actual selected small Kan values. -/
def descended : (Cᵒᵖ × C) ⥤ S where
  obj X := L.obj ((uncurried hcof hfib).obj (ofBase X))
  map {X Y} f := L.map ((uncurried hcof hfib).map
    (liftBase (X := ofBase X) (Y := ofBase Y) f))
  map_id X := by
    trans L.map ((uncurried hcof hfib).map (𝟙 (ofBase X)))
    · exact localized_uncurried_map_eq hcof hfib L _ _ rfl rfl
    · rw [(uncurried hcof hfib).map_id, L.map_id]
  map_comp {X Y Z} f g := by
    trans L.map ((uncurried hcof hfib).map
      (liftBase (X := ofBase X) (Y := ofBase Y) f ≫
        liftBase (X := ofBase Y) (Y := ofBase Z) g))
    · exact localized_uncurried_map_eq hcof hfib L _ _ rfl rfl
    · rw [(uncurried hcof hfib).map_comp, L.map_comp]

lemma descended_map_isIso {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso ((descended hcof hfib L).map f) :=
  Localization.inverts L (weakEquivalences SSet.{v}) _
    (uncurried_weakEquivalence hcof hfib _ hs ht)

/-- This comparison is natural only after localization of the spaces. -/
def descentComparison :
    projection (C := C) ⋙ descended hcof hfib L ⟶ uncurried hcof hfib ⋙ L where
  app X := L.map (presentationMap hcof hfib X)
  naturality {X Y} f := by
    change L.map ((uncurried hcof hfib).map _) ≫
      L.map ((uncurried hcof hfib).map _) =
      L.map ((uncurried hcof hfib).map _) ≫ L.map ((uncurried hcof hfib).map _)
    rw [← L.map_comp, ← L.map_comp, ← (uncurried hcof hfib).map_comp,
      ← (uncurried hcof hfib).map_comp]
    exact localized_uncurried_map_eq hcof hfib L _ _
      (Category.id_comp _ |>.trans (Category.comp_id _).symm)
      (Category.comp_id _ |>.trans (Category.id_comp _).symm)

instance descentComparison_isIso : IsIso (descentComparison (C := C) hcof hfib L) := by
  have : ∀ X, IsIso ((descentComparison (C := C) hcof hfib L).app X) := fun X =>
    Localization.inverts L (weakEquivalences SSet.{v}) _
      (presentationMap_weakEquivalence hcof hfib X)
  exact NatIso.isIso_of_isIso_app _

abbrev descentComparisonIso :
    projection (C := C) ⋙ descended hcof hfib L ≅ uncurried hcof hfib ⋙ L :=
  asIso (descentComparison (C := C) hcof hfib L)

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
