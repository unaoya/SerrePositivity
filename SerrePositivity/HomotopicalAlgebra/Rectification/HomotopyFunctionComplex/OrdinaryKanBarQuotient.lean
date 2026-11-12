module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.UniverseLiftPiZero

/-!
# 中断した任意モデル源への一般化：OrdinaryKanBarQuotient

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The complete output of a small finite-boundary quotient of the Kan bar。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0249][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0249
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The complete output of a small finite-boundary quotient of the Kan bar

The input certificate has not been constructed here. Given it, Kan values,
natural localized comparisons, weak invariance, and the actual component
comparison all follow. Label preservation is derived, not a further input.
-/

@[expose] public section
universe v u vH uH vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarQuotient
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The remaining existence problem is to supply this certificate for every source model. -/
structure QuotientData where
  relation : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence (OrdinaryKanBarMappingClasses.functor (C := C))
  small : ∀ b n, Small.{v} (Quotient (relation.rel b n))
  boundary : ∀ b, SSet.modelCategoryQuillen.I.rlp
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection relation).app b)

variable (d : QuotientData (C := C))

abbrev functor : Cᵒᵖ × C ⥤ SSet.{v} := SmallDiagramQuotient.functor d.relation d.small

abbrev curried : Cᵒᵖ ⥤ C ⥤ SSet.{v} := Functor.curry.obj (functor d)

abbrev projection : OrdinaryKanBarMappingClasses.functor (C := C) ⟶
    functor d ⋙ SSet.uliftFunctor.{max u v, v} :=
  SmallDiagramQuotient.projection d.relation d.small

def comparison : OrdinaryResolutionBar.functor (C := C) ⟶
    functor d ⋙ SSet.uliftFunctor.{max u v, v} :=
  OrdinaryKanBarMappingClasses.unit ≫ projection d

lemma projection_localized_isIso (b : Cᵒᵖ × C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((projection d).app b)) :=
  MonoRightLiftingContraction.image_isIso _
    (SmallDiagramQuotient.projection_mono_rlp d.relation d.small d.boundary b)
    AnodyneHomotopy.anodyneQ (Localization.inverts AnodyneHomotopy.anodyneQ _)

lemma terminal_rlp (b : Cᵒᵖ × C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((functor d).obj b)) :=
  SmallDiagramQuotient.kan d.relation d.small d.boundary b
    (OrdinaryKanBarMappingClasses.terminal_rlp b)

def imageIso {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    OrdinaryResolutionBar.functor (C := C) ⋙ L ≅
      (functor d ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L := by
  have (b : Cᵒᵖ × C) : IsIso ((Functor.whiskerRight
      (OrdinaryKanBarMappingClasses.unit (C := C)) L).app b) :=
    hL _ (AnodyneKanReplacement.unit_anodyne _)
  have : IsIso (Functor.whiskerRight (OrdinaryKanBarMappingClasses.unit (C := C)) L) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight OrdinaryKanBarMappingClasses.unit L) ≪≫
    SmallDiagramQuotient.imageIso d.relation d.small d.boundary L hL

def changeQuotientIso (e : QuotientData (C := C))
    {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    (functor d ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
      (functor e ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L :=
  (imageIso d L hL).symm ≪≫ imageIso e L hL

lemma projection_piZero_bijective (b : Cᵒᵖ × C) :
    Function.Bijective (SSet.mapπ₀ ((projection d).app b)) :=
  PiZeroLocalization.piZero_bijective _ (projection_localized_isIso d b)

def componentEquiv (b : Cᵒᵖ × C) :
    SSet.π₀ ((functor d).obj b) ≃ SSet.π₀ (OrdinaryKanBarMappingClasses.functor.obj b) :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.equiv.{v, max u v} _).symm.trans
    (Equiv.ofBijective _ (projection_piZero_bijective d b)).symm

lemma componentEquiv_projection (b : Cᵒᵖ × C)
    (z : SSet.π₀ (OrdinaryKanBarMappingClasses.functor.obj b)) :
    componentEquiv d b (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _
      (SSet.mapπ₀ ((projection d).app b) z)) = z := by
  change (Equiv.ofBijective _ (projection_piZero_bijective d b)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.up _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _ _)) = z
  rw [show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.up _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _
      (SSet.mapπ₀ ((projection d).app b) z)) = SSet.mapπ₀ ((projection d).app b) z from
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.equiv _).symm_apply_apply _]
  exact (Equiv.ofBijective _ (projection_piZero_bijective d b)).symm_apply_apply z

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

def augmentation : functor d ⋙ SSet.uliftFunctor.{max u v, v} ⟶
    LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v} :=
  DiscreteLocalizedExtension.descend (projection d) (projection_localized_isIso d)
    (T := LocalizedHomDiagram.types Q ⋙ CategoryTheory.uliftFunctor.{max u v, v})
    (OrdinaryKanBarMappingClasses.augmentation Q)

lemma augmentation_fac : projection d ≫ augmentation d Q =
    OrdinaryKanBarMappingClasses.augmentation Q :=
  DiscreteLocalizedExtension.descend_fac _ _ _

lemma augmentation_unique
    (a : functor d ⋙ SSet.uliftFunctor.{max u v, v} ⟶
      LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v})
    (ha : projection d ≫ a = OrdinaryKanBarMappingClasses.augmentation Q) :
    a = augmentation d Q :=
  DiscreteLocalizedExtension.descend_unique (projection d) (projection_localized_isIso d)
    (T := LocalizedHomDiagram.types Q ⋙ CategoryTheory.uliftFunctor.{max u v, v}) _ a ha

lemma comparison_augmentation : comparison d ≫ augmentation d Q =
    OrdinaryBarMappingClasses.augmentation Q := by
  rw [comparison, Category.assoc, augmentation_fac,
    OrdinaryKanBarMappingClasses.unit_augmentation]

lemma relation_preserves_labels (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    {x y : (OrdinaryKanBarMappingClasses.functor.obj b).obj n}
    (h : (d.relation.rel b n).r x y) :
    ((OrdinaryKanBarMappingClasses.augmentation Q).app b).app n x =
      ((OrdinaryKanBarMappingClasses.augmentation Q).app b).app n y := by
  have hp : ((projection d).app b).app n x = ((projection d).app b).app n y :=
    congrArg (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.diagramLiftIso
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.functor d.relation) d.small).inv.app b).app n) (Quotient.sound h)
  have hx := types_congr_hom (congr_app (congr_app (augmentation_fac d Q) b) n) x
  have hy := types_congr_hom (congr_app (congr_app (augmentation_fac d Q) b) n) y
  exact hx.symm.trans ((congrArg (((augmentation d Q).app b).app n) hp).trans hy)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma map_weakEquivalence {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    weakEquivalences SSet.{v} ((functor d).map f) :=
  SmallDiagramQuotient.map_weakEquivalence d.relation d.small d.boundary hcof hfib f
    (OrdinaryKanBarMappingClasses.map_localized_isIso hcof hfib f hs ht)

def piZeroEquiv (b : Cᵒᵖ × C) :
    SSet.π₀ ((functor d).obj b) ≃ (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  (componentEquiv d b).trans (OrdinaryKanBarMappingClasses.piZeroEquiv Q hcof hfib b)

lemma piZeroEquiv_projection (b : Cᵒᵖ × C)
    (z : SSet.π₀ (OrdinaryKanBarMappingClasses.functor.obj b)) :
    piZeroEquiv d Q hcof hfib b (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _
        (SSet.mapπ₀ ((projection d).app b) z)) =
      OrdinaryKanBarMappingClasses.piZeroEquiv Q hcof hfib b z :=
  congrArg (OrdinaryKanBarMappingClasses.piZeroEquiv Q hcof hfib b)
    (componentEquiv_projection d b z)

lemma piZeroEquiv_comparison (b : Cᵒᵖ × C)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    piZeroEquiv d Q hcof hfib b (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _
        (SSet.mapπ₀ ((comparison d).app b) z)) =
      OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b z := by
  change piZeroEquiv d Q hcof hfib b (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _
    (SSet.mapπ₀ (OrdinaryKanBarMappingClasses.unit.app b ≫ (projection d).app b) z)) = _
  rw [SSet.mapπ₀_comp_apply, piZeroEquiv_projection,
    OrdinaryKanBarMappingClasses.piZeroEquiv_unit]

lemma piZeroEquiv_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ ((functor d).obj b)) :
    piZeroEquiv d Q hcof hfib c (SSet.mapπ₀ ((functor d).map f) z) =
      Q.map f.1.unop ≫ piZeroEquiv d Q hcof hfib b z ≫ Q.map f.2 := by
  obtain ⟨z, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.equiv _).surjective z
  obtain ⟨z, rfl⟩ := (projection_piZero_bijective d b).surjective z
  have hn : (projection d).app b ≫ SSet.uliftFunctor.{max u v, v}.map ((functor d).map f) =
      OrdinaryKanBarMappingClasses.functor.map f ≫ (projection d).app c :=
    ((projection d).naturality f).symm
  change piZeroEquiv d Q hcof hfib c (SSet.mapπ₀ ((functor d).map f)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _ (SSet.mapπ₀ ((projection d).app b) z))) =
    Q.map f.1.unop ≫ piZeroEquiv d Q hcof hfib b
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down _ (SSet.mapπ₀ ((projection d).app b) z)) ≫ Q.map f.2
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.down_naturality, ← SSet.mapπ₀_comp_apply,
    hn, SSet.mapπ₀_comp_apply, piZeroEquiv_projection, piZeroEquiv_projection]
  exact OrdinaryKanBarMappingClasses.piZeroEquiv_naturality Q hcof hfib f z

end SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarQuotient
