module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedFaceSystems
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingBoundary

/-!
# 中断した任意モデル源への一般化：ResolutionMixedBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The two actual mixed triangle boundaries made from the same five whole edge systems。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0313][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0313
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The two actual mixed triangle boundaries made from the same five whole edge systems
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram NerveCylinderBoundary NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedBoundary
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev boundaryParameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C) (SSet.boundary.{max u v} 2).toSSet
abbrev fullParameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2))
abbrev inclusion : boundaryParameter C ⟶ fullParameter C :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary 2).ι (parameters C)
abbrev faceInclusion (k : Fin 3) : ResolutionMixedIntervalRestrictions.intervalParameters C ⟶
    boundaryParameter C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.boundary.ι k) (parameters C)

/-- Both genuine boundary systems retain the same original four edges and shared diagonal. -/
def system (side : Bool) : NerveMovingParameter.System.{u, v}
    (boundaryParameter C) (smallValues C) :=
  NerveMovingBoundary.boundary (parameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (ResolutionMixedFaceSystems.faces C hcof hfib side)
    (ResolutionMixedFaceSystems.compatible C hcof hfib side)

lemma system_face (side : Bool) (k : Fin 3) : system C hcof hfib side ≫
    restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (faceInclusion C k) =
    ResolutionMixedFaceSystems.faces C hcof hfib side k :=
  NerveMovingBoundary.boundary_face _ _ _ _ k

lemma shared_diagonal : system C hcof hfib true ≫
    restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (faceInclusion C 1) =
    system C hcof hfib false ≫
      restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (faceInclusion C 1) :=
  (system_face C hcof hfib true 1).trans
    ((ResolutionMixedFaceSystems.shared_diagonal C hcof hfib).trans
      (system_face C hcof hfib false 1).symm)

/-- The actual old whole triangle fits the glued boundary, not merely its three vertices. -/
lemma triangle_fit (side : Bool) (p : Index C) : (inclusion C).app p ≫
    ResolutionMixedTriangles.triangle C hcof hfib p side =
    NerveMovingParameter.evaluate (boundaryParameter C) (smallValues C)
      (system C hcof hfib side) p := by
  apply ProductBoundaryCotensor.parameter_hom_ext
  intro k
  change (parameters C).obj p ◁ SSet.boundary.ι k ≫
    (parameters C).obj p ◁ (SSet.boundary 2).ι ≫ _ = _
  rw [← whiskerLeft_comp_assoc, SSet.boundary.ι_ι]
  exact (ResolutionMixedFaceSystems.old_triangle_faces C hcof hfib side k p).trans
    (NerveEvaluationLaws.restriction (boundaryParameter C) (smallValues C) _
      (faceInclusion C k) (system C hcof hfib side)
      (ResolutionMixedFaceSystems.faces C hcof hfib side k)
      (system_face C hcof hfib side k) p).symm

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedBoundary
