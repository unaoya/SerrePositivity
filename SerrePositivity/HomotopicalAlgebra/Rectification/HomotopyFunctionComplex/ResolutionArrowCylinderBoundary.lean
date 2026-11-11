module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingIntervalBoundary
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveCylinderExtension

/-!
# 中断した任意モデル源への一般化：ResolutionArrowCylinderBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One actual all-center cylinder boundary with both original endpoint systems fixed。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0279][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0279
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One actual all-center cylinder boundary with both original endpoint systems fixed
-/

@[expose] public section
universe v u w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowComparisonEndpoints NerveCylinderBoundary NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

abbrev interval := SSet.stdSimplex.{w}.obj (SimplexCategory.mk 1)
abbrev ends := NerveMovingIntervalBoundary.ends.{w}
abbrev boundaryMap : ends.{w} ⟶ interval.{w} := (SSet.boundary 1).ι
abbrev fullParameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameter C) interval.{max u v}
abbrev boundaryParameter := NerveCylinderBoundary.boundary (vertexParameter C) (parameter C)
  (vertexInclusion C) boundaryMap.{max u v}
abbrev inclusion : boundaryParameter C ⟶ fullParameter C :=
  NerveCylinderBoundary.inclusion (vertexParameter C) (parameter C)
    (vertexInclusion C) boundaryMap.{max u v}

abbrev endpoints : NerveMovingParameter.System.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameter C) ends.{max u v}) (values C) :=
  NerveMovingIntervalBoundary.glue (parameter C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (left C hcof) (right C hcof)

abbrev vertices : NerveMovingParameter.System.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (vertexParameter C) interval.{max u v}) (values C) :=
  NerveNaturalBoundary.ofNatTrans _ _
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v} ≫ vertexBoundary C)

lemma compatible : endpoints C hcof ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameter C) (parameter C) (vertexInclusion C) ends.{max u v}) =
    vertices C ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical boundaryMap.{max u v} (vertexParameter C)) :=
  NerveMovingIntervalBoundary.common_boundary (parameter C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C)) (vertexParameter C) (vertexInclusion C)
    (vertexBoundary C) (left C hcof) (right C hcof)
    (left_vertices C hcof) (right_vertices C hcof) boundaryMap.{max u v}

/-- The whole common-boundary equality is proved from the old endpoint systems. -/
def system : NerveMovingParameter.System.{u, v} (boundaryParameter C) (values C) :=
  NerveCylinderBoundary.system (vertexParameter C) (parameter C) (vertexInclusion C)
    boundaryMap.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (endpoints C hcof) (vertices C) (compatible C hcof)

lemma system_endpoints : system C hcof ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (endpointInclusion (vertexParameter C) (parameter C)
      (vertexInclusion C) boundaryMap.{max u v}) = endpoints C hcof :=
  NerveCylinderBoundary.system_endpoints _ _ _ _ _ _ _ _

lemma system_vertices : system C hcof ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (NerveCylinderBoundary.vertexInclusion (vertexParameter C) (parameter C)
      (vertexInclusion C) boundaryMap.{max u v}) = vertices C :=
  NerveCylinderBoundary.system_vertices _ _ _ _ _ _ _ _

abbrev zeroInclusion : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameter C) NerveMovingIntervalBoundary.point ⟶
    boundaryParameter C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.zero (parameter C) ≫
      endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}

abbrev oneInclusion : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameter C) NerveMovingIntervalBoundary.point ⟶
    boundaryParameter C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.one (parameter C) ≫
      endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}

lemma system_zero : system C hcof ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (zeroInclusion C) = NerveProductParameter.expand _ _ _ (left C hcof) := by
  rw [show zeroInclusion C = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.zero (parameter C) ≫
    endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}
      from rfl, ← restriction_comp, ← Category.assoc, system_endpoints]
  exact NerveMovingIntervalBoundary.glue_zero _ _ _ _

lemma system_one : system C hcof ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (oneInclusion C) = NerveProductParameter.expand _ _ _ (right C hcof) := by
  rw [show oneInclusion C = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.one (parameter C) ≫
    endpointInclusion (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}
      from rfl, ← restriction_comp, ← Category.assoc, system_endpoints]
  exact NerveMovingIntervalBoundary.glue_one _ _ _ _

omit [ModelCategory SSet.{v}] in
lemma inclusion_mono (e : Arrow (ResolutionArrowDiagram.Index C)) : Mono ((inclusion C).app e) :=
  NerveCylinderBoundary.inclusion_mono (vertexParameter C) (parameter C) (vertexInclusion C)
    boundaryMap.{max u v} (fun e => ResolutionArrowTupleCoherence.bigInclusion_mono C e.left) e


variable (n : ℕ) (old : NerveMovingParameter.LowerSystem.{u, v} (fullParameter C) (values C) n)
  (hboundary : old ≫ Functor.whiskerLeft
      (Reedy.lowerInclusion (NerveCoherentFamily.reedy _) n)
        (NerveMovingParameterRelative.restriction (boundaryParameter C) (fullParameter C)
          (inclusion C) (values C)) =
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy _) n) (system C hcof))

/-- Extend the proved actual boundary, retaining the entire prescribed compatible lower system. -/
def extend : NerveMovingParameter.System.{u, v} (fullParameter C) (values C) :=
  NerveMovingParameterRelative.extend (boundaryParameter C) (fullParameter C) (inclusion C)
    (values C) (fun e => ResolutionArrowDiagram.fillers C hcof e.right) (inclusion_mono C)
    (system C hcof) n old hboundary

lemma extend_boundary : extend C hcof n old hboundary ≫
    NerveMovingParameterRelative.restriction (boundaryParameter C) (fullParameter C)
      (inclusion C) (values C) = system C hcof :=
  NerveMovingParameterRelative.extend_boundary _ _ _ _ _ _ _ _ _ _

lemma extend_restrict : Functor.whiskerLeft
    (Reedy.lowerInclusion (NerveCoherentFamily.reedy _) n) (extend C hcof n old hboundary) = old :=
  NerveMovingParameterRelative.extend_restrict _ _ _ _ _ _ _ _ _ _

lemma extend_zero : extend C hcof n old hboundary ≫
    restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C)) (zeroInclusion C ≫ inclusion C) =
      NerveProductParameter.expand _ _ _ (left C hcof) := by
  rw [← restriction_comp, ← Category.assoc]
  exact (congrArg (fun a => a ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (zeroInclusion C)) (extend_boundary C hcof n old hboundary)).trans (system_zero C hcof)

lemma extend_one : extend C hcof n old hboundary ≫
    restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C)) (oneInclusion C ≫ inclusion C) =
      NerveProductParameter.expand _ _ _ (right C hcof) := by
  rw [← restriction_comp, ← Category.assoc]
  exact (congrArg (fun a => a ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (oneInclusion C)) (extend_boundary C hcof n old hboundary)).trans (system_one C hcof)

lemma extend_vertices : extend C hcof n old hboundary ≫
    restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameter C) (parameter C) (vertexInclusion C) interval.{max u v}) =
        vertices C := by
  rw [← NerveCylinderBoundary.vertexInclusion_inclusion
    (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v},
    ← restriction_comp, ← Category.assoc]
  exact (congrArg (fun a => a ≫ restriction _ _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
    (NerveCylinderBoundary.vertexInclusion (vertexParameter C) (parameter C)
      (vertexInclusion C) boundaryMap.{max u v}))
        (extend_boundary C hcof n old hboundary)).trans (system_vertices C hcof)

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary
