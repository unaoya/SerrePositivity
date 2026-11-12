module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftRows
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionFrameRowFunctor
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionCenters

/-!
# 中断した任意モデル源への一般化：ResolutionCenterRowLifts

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Full row lifts from the same actual changing-center fiber diagram。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0302][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0302
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Full row lifts from the same actual changing-center fiber diagram
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLifts
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

def map (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    ResolutionFrameRows.row (ResolutionArrowDiagram.source C q).inner n.unop ⟶
      ResolutionArrowDiagram.target C q :=
  ResolutionLiftRows.map _ _ _ (s ≫ (ResolutionArrowDiagram.fiberIso C q).hom) n x

lemma diagram (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (map C q s n x).diagram =
      ((s ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (ResolutionArrowDiagram.rawProjection C)
        (ResolutionArrowDiagram.basepoint C)).app q).app n x) := by
  change (((s ≫ (ResolutionArrowDiagram.fiberIso C q).hom) ≫
    ResolutionLiftSpace.inclusion _ _ _).app n x) = _
  rw [Category.assoc, ResolutionArrowDiagram.fiberIso_inclusion]
  rfl

lemma naturality (q : ResolutionArrowDiagram.Index C) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : T.obj n) :
    ResolutionFrameRows.rowMap (ResolutionArrowDiagram.source C q).inner θ.unop ≫
        map C q s n x = map C q s m (T.map θ x) :=
  ResolutionLiftRows.naturality _ _ _ _ θ x

lemma transport {q r : ResolutionArrowDiagram.Index C} (k : q ⟶ r) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    map C r (s ≫ (ResolutionArrowDiagram.fibers C).map k) n x =
      (ResolutionFrameRowFunctor.component k.hom.1.unop n.unop ≫ map C q s n x) ≫ k.hom.2 := by
  apply ResolutionObject.Hom.ext
  · exact (ResolutionArrowDiagram.equation C k).symm
  · change (map C r (s ≫ (ResolutionArrowDiagram.fibers C).map k) n x).diagram =
      (k.hom.1.unop.frame.app n.unop ≫ (map C q s n x).diagram) ≫ k.hom.2.diagram
    rw [diagram, diagram]
    have h := congrArg (fun f => f.app n x)
      ((Category.assoc s ((ResolutionArrowDiagram.fibers C).map k) _).trans
        (congrArg (fun f => s ≫ f) (ResolutionArrowDiagram.map_inclusion C k)))
    exact h

end SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLifts
