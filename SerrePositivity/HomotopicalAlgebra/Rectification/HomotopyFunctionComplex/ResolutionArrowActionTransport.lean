module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowDiagram
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.KanLiftAction

/-!
# 中断した任意モデル源への一般化：ResolutionArrowActionTransport

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual action transport along arbitrary simultaneous changes of centers and resolutions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0277][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0277
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual action transport along arbitrary simultaneous changes of centers and resolutions
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowDiagram

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionTransport
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev raw (q : Index C) (Z : C) {T : SSet.{v}} (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (target C q).resolution.obj).obj Z) :=
  ResolutionLiftAction.parameterized (source C q).inner (target C q) (arrow C q) Z s t

/-- Every actual cube map transports the action by its two real resolution maps. -/
lemma raw_transport {q r : Index C} (f : q ⟶ r) (Z : C) {T : SSet.{v}}
    (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (target C r).resolution.obj).obj Z) :
    raw C r Z (s ≫ (fibers C).map f) t =
    raw C q Z s (t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.hom.2.diagram).app Z) ≫
      ResolutionLiftPrecomposition.rawTargetMap f.hom.1.unop.map
        (FramedResolution.frameMap f.hom.1.unop) Z := by
  change DiagonalHom.pairing _ _ _ ((s ≫ (fibers C).map f) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection C) (basepoint C)).app r) t = _
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  change DiagonalHom.pairing _ _ _
    (((s ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection C) (basepoint C)).app q) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.hom.1.unop.frame).app (target C q).resolution.obj) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame (source C r).inner).obj).map
          f.hom.2.diagram) t = _
  rw [DiagonalHom.pairing_middle_naturality, DiagonalHom.pairing_source_naturality]
  rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev kan (q : Index C) (Z : C) {T : SSet.{v}} (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (target C q).resolution.obj).obj Z) :=
  KanLiftAction.parameterized hcof hfib (source C q).inner (target C q) (arrow C q) Z s t

lemma kan_transport {q r : Index C} (f : q ⟶ r) (Z : C) {T : SSet.{v}}
    (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (target C r).resolution.obj).obj Z) :
    kan C hcof hfib r Z (s ≫ (fibers C).map f) t =
    kan C hcof hfib q Z s (t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.hom.2.diagram).app Z) ≫
      ResolutionLiftPrecomposition.kanTargetMap hcof hfib f.hom.1.unop.map
        (FramedResolution.frameMap f.hom.1.unop) Z := by
  have hu := (KanReplacement.unit hcof hfib).naturality
    (ResolutionLiftPrecomposition.rawTargetMap f.hom.1.unop.map
      (FramedResolution.frameMap f.hom.1.unop) Z)
  change ResolutionLiftPrecomposition.rawTargetMap f.hom.1.unop.map
      (FramedResolution.frameMap f.hom.1.unop) Z ≫
      (KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target (source C r).inner Z) =
    (KanReplacement.unit hcof hfib).app (ResolutionLiftAction.target (source C q).inner Z) ≫
      ResolutionLiftPrecomposition.kanTargetMap hcof hfib f.hom.1.unop.map
        (FramedResolution.frameMap f.hom.1.unop) Z at hu
  change raw C r Z (s ≫ (fibers C).map f) t ≫ _ = (raw C q Z s _ ≫ _) ≫ _
  rw [raw_transport, Category.assoc, hu, ← Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionTransport
