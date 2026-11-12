module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveEvaluationLaws
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingFamilyFit

/-!
# 中断した任意モデル源への一般化：ResolutionArrowCylinderFamilyFit

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole cylinder fit derived from the actual two endpoints and entire vertex restriction。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0281][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0281
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole cylinder fit derived from the actual two endpoints and entire vertex restriction
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowComparisonEndpoints ResolutionArrowCylinderBoundary NerveCylinderBoundary

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

lemma zero_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (zeroInclusion C).app e ≫ NerveMovingParameter.evaluate (boundaryParameter C) (values C)
      (system C hcof) e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e :=
  (NerveEvaluationLaws.restriction _ _ _ _ _ _ (system_zero C hcof) e).trans
    (NerveEvaluationLaws.expand _ _ _ _ e)

lemma one_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (oneInclusion C).app e ≫ NerveMovingParameter.evaluate (boundaryParameter C) (values C)
      (system C hcof) e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e :=
  (NerveEvaluationLaws.restriction _ _ _ _ _ _ (system_one C hcof) e).trans
    (NerveEvaluationLaws.expand _ _ _ _ e)

lemma vertex_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (NerveCylinderBoundary.vertexInclusion (vertexParameter C) (parameter C)
      (vertexInclusion C) boundaryMap.{max u v}).app e ≫
        NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app e ≫
      (vertexBoundary C).app e :=
  (NerveEvaluationLaws.restriction _ _ _ _ _ _ (system_vertices C hcof) e).trans
    (NerveEvaluationLaws.natural _ _ _ e)

variable (e : Arrow (ResolutionArrowDiagram.Index C))
  (H : (fullParameter C).obj e ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((values C).obj e))
  (hzero : (zeroInclusion C ≫ inclusion C).app e ≫ H =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e)
  (hone : (oneInclusion C ≫ inclusion C).app e ≫ H =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e)
  (hvertex : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameter C) (parameter C) (vertexInclusion C)
      interval.{max u v}).app e ≫ H =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app e ≫
      (vertexBoundary C).app e)

include hzero hone hvertex in
lemma pointwise_fit : (inclusion C).app e ≫ H =
    NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e := by
  apply (NervePushoutBoundary.square
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (vertexParameter C) ends.{max u v}) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameter C) ends.{max u v})
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (vertexParameter C) interval.{max u v})
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameter C) (parameter C) (vertexInclusion C) ends.{max u v})
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical boundaryMap.{max u v} (vertexParameter C)) e).hom_ext
  · apply (NerveMovingIntervalBoundary.coproduct (parameter C) e).hom_ext
    intro j
    rcases j with ⟨j⟩
    cases j
    · change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.zero (parameter C)).app e ≫
        (endpointInclusion (vertexParameter C) (parameter C)
          (vertexInclusion C) boundaryMap.{max u v}).app e ≫
            (inclusion C).app e ≫ H =
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.zero (parameter C)).app e ≫
          (endpointInclusion (vertexParameter C) (parameter C)
            (vertexInclusion C) boundaryMap.{max u v}).app e ≫
              NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e
      simpa only [NatTrans.comp_app, zeroInclusion, Category.assoc] using
        hzero.trans (zero_evaluate C hcof e).symm
    · change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.one (parameter C)).app e ≫
        (endpointInclusion (vertexParameter C) (parameter C)
          (vertexInclusion C) boundaryMap.{max u v}).app e ≫
            (inclusion C).app e ≫ H =
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical NerveMovingIntervalBoundary.one (parameter C)).app e ≫
          (endpointInclusion (vertexParameter C) (parameter C)
            (vertexInclusion C) boundaryMap.{max u v}).app e ≫
              NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e
      simpa only [NatTrans.comp_app, oneInclusion, Category.assoc] using
        hone.trans (one_evaluate C hcof e).symm
  · have hfac := congr_app (NerveCylinderBoundary.vertexInclusion_inclusion
      (vertexParameter C) (parameter C) (vertexInclusion C) boundaryMap.{max u v}) e
    exact ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ H) hfac)).trans
      (hvertex.trans (vertex_evaluate C hcof e).symm)


/-- Independent entire interval maps with their actual two endpoint and whole vertex equations. -/
structure Data where
  family : ∀ e, (fullParameter C).obj e ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((values C).obj e)
  zero : ∀ e, (zeroInclusion C ≫ inclusion C).app e ≫ family e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e
  one : ∀ e, (oneInclusion C ≫ inclusion C).app e ≫ family e =
    (NerveProductParameter.projection (parameter C) NerveMovingIntervalBoundary.point).app e ≫
      NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e
  vertex : ∀ e, (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (vertexParameter C) (parameter C) (vertexInclusion C)
      interval.{max u v}).app e ≫ family e =
    (NerveProductParameter.projection (vertexParameter C) interval.{max u v}).app e ≫
      (vertexBoundary C).app e

variable (d : Data C hcof)

lemma family_fit (e : Arrow (ResolutionArrowDiagram.Index C)) :
    (inclusion C).app e ≫ d.family e =
      NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e :=
  pointwise_fit C hcof e (d.family e) (d.zero e) (d.one e) (d.vertex e)

/-- Preserve every original whole interval map and the entire fixed coherent boundary together. -/
def extendFamilies : NerveMovingParameter.System.{u, v} (fullParameter C) (values C) :=
  NerveMovingFamilyFit.extend (fullParameter C) (values C) (boundaryParameter C)
    (inclusion C) d.family (system C hcof) (family_fit C hcof d)
    (fun e => ResolutionArrowDiagram.fillers C hcof e.right)
    (ResolutionArrowCylinderBoundary.inclusion_mono C)

lemma extendFamilies_evaluate (e : Arrow (ResolutionArrowDiagram.Index C)) :
    NerveMovingParameter.evaluate (fullParameter C) (values C) (extendFamilies C hcof d) e =
      d.family e := NerveMovingFamilyFit.extend_evaluate _ _ _ _ _ _ _ _ _ e

lemma extendFamilies_boundary : extendFamilies C hcof d ≫
    NerveMovingParameterRelative.restriction (boundaryParameter C) (fullParameter C)
      (inclusion C) (values C) = system C hcof :=
  NerveMovingFamilyFit.extend_boundary _ _ _ _ _ _ _ _ _

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit
