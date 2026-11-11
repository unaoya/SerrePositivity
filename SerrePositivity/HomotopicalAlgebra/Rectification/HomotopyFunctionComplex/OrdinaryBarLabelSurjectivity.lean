module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarMappingClasses
public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-!
# 中断した任意モデル源への一般化：OrdinaryBarLabelSurjectivity

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Every ordinary localized morphism is represented by an actual bar simplex。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0198][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0198
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Every ordinary localized morphism is represented by an actual bar simplex

This uses only the source model category. It does not assert injectivity on
components or preservation of higher homotopy by the mapping-class quotient.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

lemma raw_label_surjective (R : OrdinaryResolutionPairs.Index (C := C))
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (OrdinaryMappingClassLabel.label Q R n) := by
  have : IsCofibrant (R.1.unop.resolution.obj.obj n.unop) :=
    R.1.unop.resolution.isCofibrant_obj n.unop
  have : IsFibrant (R.2.unop.resolution.obj.obj n.unop).unop :=
    DualResolutionTargets.isFibrant_obj C R.2 n
  intro z
  let a := OrdinaryMappingClassLabel.sourceIso Q R n.unop
  let b := OrdinaryMappingClassLabel.targetIso Q R n.unop
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization Q
    (R.1.unop.resolution.obj.obj n.unop) (R.2.unop.resolution.obj.obj n.unop).unop
    (a.hom ≫ LocalizedHomDiagram.equiv Q _ z ≫ b.hom)
  refine ⟨f, (LocalizedHomDiagram.equiv Q _).injective ?_⟩
  rw [OrdinaryMappingClassLabel.label_equiv, hf]
  change a.inv ≫ (a.hom ≫ _) ≫ b.inv = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Objectwise existence is used to supply vertices, without a functorial section. -/
abbrev ofBase (b : Cᵒᵖ × C) : OrdinaryResolutionPairs.Index (C := C) :=
  (op (ResolutionObject.ofObject b.1.unop), op (ResolutionObject.ofObject (op b.2)))

lemma label_surjective (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (OrdinaryBarMappingClasses.label Q b n) := by
  intro z
  obtain ⟨f, hf⟩ := raw_label_surjective Q (ofBase b) n z
  exact ⟨(OrdinaryBarMappingClasses.entry (ofBase b)).app n ⟨f⟩,
    (OrdinaryBarMappingClasses.entry_label Q (ofBase b) n f).trans hf⟩

lemma piZeroLabel_surjective (b : Cᵒᵖ × C) :
    Function.Surjective (OrdinaryBarMappingClasses.piZeroLabel Q b) := by
  intro z
  obtain ⟨x, hx⟩ := label_surjective Q b (op (SimplexCategory.mk 0)) z
  exact ⟨SSet.π₀.mk x, hx⟩

lemma augmentation_surjective (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (((OrdinaryBarMappingClasses.augmentation Q).app b).app n) := by
  intro z
  obtain ⟨x, hx⟩ := label_surjective Q b n z.down
  exact ⟨x, ULift.ext hx⟩

/-- The coarse quotient is exactly the discrete ordinary mapping-class diagram
after the explicit universe lift; no higher-homotopy equivalence is asserted. -/
def coarseLiftIso :
    OrdinaryBarMappingClasses.coarseQuotient Q ⋙ SSet.uliftFunctor.{max u v, v} ≅
      LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v} := by
  have := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernelComparison_isIso
    (OrdinaryBarMappingClasses.augmentation Q) (augmentation_surjective Q)
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.diagramLiftIso
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.functor (OrdinaryBarMappingClasses.kernel Q))
    (OrdinaryBarMappingClasses.kernel_small Q) ≪≫
      asIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernelComparison (OrdinaryBarMappingClasses.augmentation Q))

lemma coarseProjection_comparison :
    OrdinaryBarMappingClasses.coarseProjection Q ≫ (coarseLiftIso Q).hom =
      OrdinaryBarMappingClasses.augmentation Q := by
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection _ ≫ _) ≫ (_ ≫ _) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.kernel_factorization _

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity
