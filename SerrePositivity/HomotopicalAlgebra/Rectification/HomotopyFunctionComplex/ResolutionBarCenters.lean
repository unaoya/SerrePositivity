module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveFirstChoice
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarConstruction

/-!
# 中断した任意モデル源への一般化：ResolutionBarCenters

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual contravariant lift centers on a resolution bar comma category。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0288][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0288
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual contravariant lift centers on a resolution bar comma category

The reference pair is fixed. Every comma arrow supplies both central base
maps; morphisms use their actual resolution maps. No strict section of the
base projection or independent replacement of comma morphisms is used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarCenters
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev Comma := CostructuredArrow (RightResolutionMapping.projection (C := C))
  ((RightResolutionMapping.projection (C := C)).obj R)

def center (d : Comma R) : MixedResolutionCenters.Index C :=
  ((ResolutionArrowDiagram.baseMaps C).elementsMk
      (R.1, d.left.1.unop.inner) d.hom.1.unop,
    (ResolutionArrowDiagram.baseMaps Cᵒᵖ).elementsMk
      (R.2, d.left.2.unop.inner) d.hom.2.op)

def centers : (Comma R)ᵒᵖ ⥤ MixedResolutionCenters.Index C where
  obj d := center R d.unop
  map {d e} k :=
    ({ hom := (𝟙 R.1, k.unop.left.1.unop.map)
       map_val := by
         have h := congrArg (fun t => t.1.unop) (CostructuredArrow.w k.unop)
         change ((𝟙 _) ≫ d.unop.hom.1.unop) ≫ k.unop.left.1.unop.map.base = e.unop.hom.1.unop
         change d.unop.hom.1.unop ≫ k.unop.left.1.unop.map.base = e.unop.hom.1.unop at h
         simpa only [Category.id_comp] using h },
     { hom := (𝟙 R.2, k.unop.left.2.unop.map)
       map_val := by
         have h := congrArg (fun t => t.2.op) (CostructuredArrow.w k.unop)
         change ((𝟙 _) ≫ d.unop.hom.2.op) ≫ k.unop.left.2.unop.map.base = e.unop.hom.2.op
         change d.unop.hom.2.op ≫ k.unop.left.2.unop.map.base = e.unop.hom.2.op at h
         simpa only [Category.id_comp] using h })
  map_id d := by rfl
  map_comp k l := by
    apply Prod.ext
    · apply Functor.Elements.hom_ext
      apply Prod.ext
      · exact (Category.id_comp _).symm
      · rfl
    · apply Functor.Elements.hom_ext
      apply Prod.ext
      · exact (Category.id_comp _).symm
      · rfl

abbrev leftChoices : (Comma R)ᵒᵖ ⥤ SSet.{v} := centers R ⋙ MixedResolutionCenters.leftChoices C
abbrev rightChoices : (Comma R)ᵒᵖ ⥤ SSet.{v} := centers R ⋙ MixedResolutionCenters.rightChoices C

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

abbrev leftSystem : NerveFirstChoice.System (leftChoices R) :=
  NerveFirstChoice.extendVertices (leftChoices R)
    (fun d => ResolutionArrowDiagram.fillers C hcof (center R d.unop).1)
    (fun d => ResolutionArrowDiagram.selectedPoint C (center R d).1)

abbrev rightSystem : NerveFirstChoice.System (rightChoices R) :=
  NerveFirstChoice.extendVertices (rightChoices R)
    (fun d => ResolutionArrowDiagram.fillers Cᵒᵖ hcof (center R d.unop).2)
    (fun d => ResolutionArrowDiagram.selectedPoint Cᵒᵖ (center R d).2)

lemma leftSystem_point (d : Comma R) :
    (leftSystem R hcof).app (NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ d)) =
      ResolutionArrowDiagram.selectedPoint C (center R d).1 :=
  NerveFirstChoice.extendVertices_point _ _ _ d

lemma rightSystem_point (d : Comma R) :
    (rightSystem R hcof).app (NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ d)) =
      ResolutionArrowDiagram.selectedPoint Cᵒᵖ (center R d).2 :=
  NerveFirstChoice.extendVertices_point _ _ _ d

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarCenters
