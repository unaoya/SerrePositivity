module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowActionTransport
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FramedMappingBifunctor

/-!
# 中断した任意モデル源への一般化：ResolutionArrowActionFunctors

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The two strict endpoint functors underlying actual resolution-lift actions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0276][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0276
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The two strict endpoint functors underlying actual resolution-lift actions
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex ResolutionArrowDiagram

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionFunctors
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev targetResolution : Index C ⥤ ResolutionObject C :=
  forget C ⋙ CategoryTheory.Prod.snd _ _
abbrev sourceResolution : Index C ⥤ (FramedResolution C)ᵒᵖ :=
  forget C ⋙ CategoryTheory.Prod.fst _ _

/-- Contravariant input transport is the actual resolution Hom functor. -/
abbrev input (Z : C) : (Index C)ᵒᵖ ⥤ SSet.{v} :=
  (targetResolution C).op ⋙ ResolutionObject.diagrams.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
    (evaluation C SSet.{v}).obj Z

lemma input_map {q r : Index C} (f : q ⟶ r) (Z : C) :
    (input C Z).map f.op = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.hom.2.diagram).app Z := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- Covariant output transport uses the same existing strict framed Kan Hom functor. -/
abbrev output (Z : C) : Index C ⥤ SSet.{v} :=
  sourceResolution C ⋙ FramedResolution.hom hcof hfib ⋙ (evaluation C SSet.{v}).obj Z

lemma output_map {q r : Index C} (f : q ⟶ r) (Z : C) :
    (output C hcof hfib Z).map f =
    ResolutionLiftPrecomposition.kanTargetMap hcof hfib f.hom.1.unop.map
      (FramedResolution.frameMap f.hom.1.unop) Z := rfl

/-- Both endpoint transports in the action are actual functor maps, with strict unit/composition. -/
lemma transport {q r : Index C} (f : q ⟶ r) (Z : C) {T : SSet.{v}}
    (s : T ⟶ (fibers C).obj q) (t : T ⟶ (input C Z).obj (Opposite.op r)) :
    ResolutionArrowActionTransport.kan C hcof hfib r Z (s ≫ (fibers C).map f) t =
    ResolutionArrowActionTransport.kan C hcof hfib q Z s (t ≫ (input C Z).map f.op) ≫
      (output C hcof hfib Z).map f :=
  ResolutionArrowActionTransport.kan_transport C hcof hfib f Z s t

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionFunctors
