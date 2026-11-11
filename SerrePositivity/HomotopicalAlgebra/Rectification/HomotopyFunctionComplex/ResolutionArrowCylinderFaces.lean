module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary

/-!
# 中断した任意モデル源への一般化：ResolutionArrowCylinderFaces

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual standard faces of the glued all-center cylinder boundary。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0280][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0280
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual standard faces of the glued all-center cylinder boundary
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowComparisonEndpoints ResolutionArrowCylinderBoundary NerveCylinderBoundary

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFaces
variable (C : Type u) [Category.{v} C] [ModelCategory C]

lemma zero : zeroInclusion C ≫ inclusion C =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (parameter C) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.zero (parameter C) ≫
    endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}) ≫
      NerveCylinderBoundary.inclusion (vertexParameter C) (parameter C)
        (vertexInclusion C) boundaryMap.{max u v} = _
  rw [Category.assoc, endpointInclusion_inclusion]
  apply NatTrans.ext
  funext e
  change (parameter C).obj e ◁ SSet.boundary.ι (1 : Fin 2) ≫
    (parameter C).obj e ◁ (SSet.boundary 1).ι = (parameter C).obj e ◁ SSet.stdSimplex.δ 1
  rw [← MonoidalCategory.whiskerLeft_comp, SSet.boundary.ι_ι]

lemma one : oneInclusion C ≫ inclusion C =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (parameter C) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.one (parameter C) ≫
    endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}) ≫
      NerveCylinderBoundary.inclusion (vertexParameter C) (parameter C)
        (vertexInclusion C) boundaryMap.{max u v} = _
  rw [Category.assoc, endpointInclusion_inclusion]
  apply NatTrans.ext
  funext e
  change (parameter C).obj e ◁ SSet.boundary.ι (0 : Fin 2) ≫
    (parameter C).obj e ◁ (SSet.boundary 1).ι = (parameter C).obj e ◁ SSet.stdSimplex.δ 0
  rw [← MonoidalCategory.whiskerLeft_comp, SSet.boundary.ι_ι]

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFaces
