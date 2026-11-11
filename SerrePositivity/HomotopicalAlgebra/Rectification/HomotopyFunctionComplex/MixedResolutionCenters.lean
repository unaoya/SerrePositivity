module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionLiftAction
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalHomTransport

/-!
# 中断した任意モデル源への一般化：MixedResolutionCenters

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual input, output, and lift families over both changing centers。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0124][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0124
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual input, output, and lift families over both changing centers
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.MixedResolutionCenters
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

def family (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) :
    CosimplicialMapFamily T
      ((FramedResolution.diagonal (C := C)).obj (ResolutionArrowDiagram.source C q))
      (ResolutionArrowDiagram.target C q).resolution.obj :=
  CosimplicialMapFamily.ofDoubleHom
    (s ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (ResolutionArrowDiagram.rawProjection C)
      (ResolutionArrowDiagram.basepoint C)).app q)

lemma family_recovery (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) :
    family C q s = MixedResolutionLiftAction.family (ResolutionArrowDiagram.source C q).inner
      (ResolutionArrowDiagram.target C q) (ResolutionArrowDiagram.arrow C q)
      (s ≫ (ResolutionArrowDiagram.fiberIso C q).hom) := by
  unfold family MixedResolutionLiftAction.family
  rw [Category.assoc, ResolutionArrowDiagram.fiberIso_inclusion]

lemma family_transport {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (family C r (s ≫ (ResolutionArrowDiagram.fibers C).map f)).app n x =
      ((FramedResolution.diagonal (C := C)).map f.hom.1.unop).app n.unop ≫
        (family C q s).app n x ≫ f.hom.2.diagram.app n.unop := by
  have h := congrArg (fun k => (k.app n x).app n.unop)
    ((Category.assoc s ((ResolutionArrowDiagram.fibers C).map f) _).trans
      (congrArg (fun k => s ≫ k) (ResolutionArrowDiagram.map_inclusion C f)))
  change (family C r (s ≫ (ResolutionArrowDiagram.fibers C).map f)).app n x =
    (((f.hom.1.unop.frame.app n.unop).app n.unop) ≫ (family C q s).app n x) ≫
      f.hom.2.diagram.app n.unop at h
  exact h.trans (Category.assoc _ _ _)

abbrev Index := ResolutionArrowDiagram.Index C × ResolutionArrowDiagram.Index Cᵒᵖ
abbrev leftChoices : Index C ⥤ SSet.{v} :=
  CategoryTheory.Prod.fst _ _ ⋙ ResolutionArrowDiagram.fibers C
abbrev rightChoices : Index C ⥤ SSet.{v} :=
  CategoryTheory.Prod.snd _ _ ⋙ ResolutionArrowDiagram.fibers Cᵒᵖ

def input : (Index C)ᵒᵖ ⥤ SSet.{v} where
  obj q := MixedDiagonalHom.obj (ResolutionArrowDiagram.target C q.unop.1).resolution.obj
    (ResolutionArrowDiagram.target Cᵒᵖ q.unop.2).resolution.obj
  map f := MixedDiagonalHom.map f.unop.1.hom.2.diagram f.unop.2.hom.2.diagram
  map_id _ := MixedDiagonalHom.map_id _ _
  map_comp _ _ := MixedDiagonalHom.map_comp _ _ _ _

def output : Index C ⥤ SSet.{v} where
  obj q := MixedDiagonalHom.obj
    ((FramedResolution.diagonal (C := C)).obj (ResolutionArrowDiagram.source C q.1))
    ((FramedResolution.diagonal (C := Cᵒᵖ)).obj (ResolutionArrowDiagram.source Cᵒᵖ q.2))
  map f := MixedDiagonalHom.map ((FramedResolution.diagonal (C := C)).map f.1.hom.1.unop)
    ((FramedResolution.diagonal (C := Cᵒᵖ)).map f.2.hom.1.unop)
  map_id q := by
    change MixedDiagonalHom.map ((FramedResolution.diagonal (C := C)).map (𝟙 _))
      ((FramedResolution.diagonal (C := Cᵒᵖ)).map (𝟙 _)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact MixedDiagonalHom.map_id _ _
  map_comp f g := by
    change MixedDiagonalHom.map
      ((FramedResolution.diagonal (C := C)).map (g.1.hom.1.unop ≫ f.1.hom.1.unop))
      ((FramedResolution.diagonal (C := Cᵒᵖ)).map (g.2.hom.1.unop ≫ f.2.hom.1.unop)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    exact MixedDiagonalHom.map_comp _ _ _ _

def action (q : Index C) {T : SSet.{v}} (s : T ⟶ (leftChoices C).obj q)
    (r : T ⟶ (rightChoices C).obj q) (t : T ⟶ (input C).obj (op q)) :
    T ⟶ (output C).obj q :=
  MixedDiagonalHom.action (family C q.1 s) (family Cᵒᵖ q.2 r) t

lemma action_parameter (q : Index C) {T U : SSet.{v}} (a : U ⟶ T)
    (s : T ⟶ (leftChoices C).obj q) (r : T ⟶ (rightChoices C).obj q)
    (t : T ⟶ (input C).obj (op q)) :
    a ≫ action C q s r t = action C q (a ≫ s) (a ≫ r) (a ≫ t) := by
  ext n x
  rfl

/-- Both centers, both actual frame maps, and both target resolution maps move together. -/
lemma action_transport {q p : Index C} (f : q ⟶ p) {T : SSet.{v}}
    (s : T ⟶ (leftChoices C).obj q) (r : T ⟶ (rightChoices C).obj q)
    (t : T ⟶ (input C).obj (op p)) :
    action C p (s ≫ (leftChoices C).map f) (r ≫ (rightChoices C).map f) t =
      action C q s r (t ≫ (input C).map f.op) ≫ (output C).map f :=
  MixedDiagonalHom.action_transport _ _ _ _ _ _ _ _
    (family_transport C f.1 s) (family_transport Cᵒᵖ f.2 r) t

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev kanOutput : Index C ⥤ SSet.{v} := output C ⋙ KanReplacement.functor hcof hfib

def kanAction (q : Index C) {T : SSet.{v}} (s : T ⟶ (leftChoices C).obj q)
    (r : T ⟶ (rightChoices C).obj q) (t : T ⟶ (input C).obj (op q)) :
    T ⟶ (kanOutput C hcof hfib).obj q :=
  action C q s r t ≫ (KanReplacement.unit hcof hfib).app _

lemma kan_action_parameter (q : Index C) {T U : SSet.{v}} (a : U ⟶ T)
    (s : T ⟶ (leftChoices C).obj q) (r : T ⟶ (rightChoices C).obj q)
    (t : T ⟶ (input C).obj (op q)) :
    a ≫ kanAction C hcof hfib q s r t =
      kanAction C hcof hfib q (a ≫ s) (a ≫ r) (a ≫ t) := by
  change a ≫ (action C q s r t ≫ _) = _
  rw [← Category.assoc, action_parameter]
  rfl

lemma kan_action_transport {q p : Index C} (f : q ⟶ p) {T : SSet.{v}}
    (s : T ⟶ (leftChoices C).obj q) (r : T ⟶ (rightChoices C).obj q)
    (t : T ⟶ (input C).obj (op p)) :
    kanAction C hcof hfib p (s ≫ (leftChoices C).map f) (r ≫ (rightChoices C).map f) t =
      kanAction C hcof hfib q s r (t ≫ (input C).map f.op) ≫ (kanOutput C hcof hfib).map f := by
  have hu : (output C).map f ≫ (KanReplacement.unit hcof hfib).app ((output C).obj p) =
      (KanReplacement.unit hcof hfib).app ((output C).obj q) ≫
        (KanReplacement.functor hcof hfib).map ((output C).map f) :=
    (KanReplacement.unit hcof hfib).naturality ((output C).map f)
  change action C p (s ≫ (leftChoices C).map f) (r ≫ (rightChoices C).map f) t ≫
      (KanReplacement.unit hcof hfib).app ((output C).obj p) =
    (action C q s r (t ≫ (input C).map f.op) ≫
      (KanReplacement.unit hcof hfib).app ((output C).obj q)) ≫
        (KanReplacement.functor hcof hfib).map ((output C).map f)
  rw [action_transport, Category.assoc, hu, ← Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.MixedResolutionCenters
