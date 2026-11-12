module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals
public import Mathlib.CategoryTheory.InducedCategory

/-!
# 中断した任意モデル源への一般化：SelectedIntervalDiagram

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One coherent system retaining all originally selected pre/post interval families。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0333][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0333
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One coherent system retaining all originally selected pre/post interval families
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowComparisonEndpoints ResolutionArrowCylinderBoundary

namespace SerrePositivity.HomotopyFunctionComplex.SelectedIntervalDiagram
variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-- Retain every actual pre/post presentation, even when their underlying arrows coincide. -/
inductive Presentation where
  | post (X : FramedResolution C) (Y W : ResolutionObject C)
      (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W)
  | pre (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
      (g : Y.inner.base ⟶ W.base)

def toArrow : Presentation C → Arrow (ResolutionArrowDiagram.Index C)
  | .post X Y W f g => Arrow.mk (ResolutionArrowElementary.post X Y W f g)
  | .pre X Y W f g => Arrow.mk (ResolutionArrowElementary.pre X Y W f g)

abbrev Index := InducedCategory (Arrow (ResolutionArrowDiagram.Index C)) (toArrow C)
abbrev forget : Index C ⥤ Arrow (ResolutionArrowDiagram.Index C) := inducedFunctor (toArrow C)
abbrev parameters := forget C ⋙ fullParameter C
abbrev boundaries := forget C ⋙ boundaryParameter C
abbrev smallValues := forget C ⋙ values C
abbrev boundaryInclusion : boundaries C ⟶ parameters C :=
  Functor.whiskerLeft (forget C) (inclusion C)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev fixedBoundary : NerveMovingParameter.System.{u, v} (boundaries C) (smallValues C) :=
  NerveBiparameterMaps.reindex _ _ (forget C) (system C hcof)

/-- Each object uses precisely its previously selected edge family. -/
def family : ∀ p : Index C, (parameters C).obj p ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((smallValues C).obj p)
  | .post X Y W f g => ResolutionArrowSelectedIntervals.postFamily hcof hfib X Y W f g
  | .pre X Y W f g => ResolutionArrowSelectedIntervals.preFamily hcof hfib X Y W f g

lemma family_fit (p : Index C) : (boundaryInclusion C).app p ≫ family C hcof hfib p =
    NerveMovingParameter.evaluate (boundaries C) (smallValues C) (fixedBoundary C hcof) p := by
  apply Eq.trans ?_ (NerveBiparameterMaps.evaluate_reindex
    (boundaryParameter C) (values C) (system C hcof) (forget C) p).symm
  cases p with
  | post X Y W f g => exact ResolutionArrowSelectedIntervals.post_fit hcof hfib X Y W f g
  | pre X Y W f g => exact ResolutionArrowSelectedIntervals.pre_fit hcof hfib X Y W f g

/-- Keep all old full intervals and the same reindexed whole Q-boundary at once. -/
def coherent : NerveMovingParameter.System.{u, v} (parameters C) (smallValues C) :=
  NerveMovingFamilyFit.extend (parameters C) (smallValues C) (boundaries C) (boundaryInclusion C)
    (family C hcof hfib) (fixedBoundary C hcof) (family_fit C hcof hfib)
    (fun p => ResolutionArrowDiagram.fillers C hcof (toArrow C p).right)
    (fun p => ResolutionArrowCylinderBoundary.inclusion_mono C (toArrow C p))

lemma coherent_evaluate (p : Index C) :
    NerveMovingParameter.evaluate (parameters C) (smallValues C) (coherent C hcof hfib) p =
      family C hcof hfib p := NerveMovingFamilyFit.extend_evaluate _ _ _ _ _ _ _ _ _ p

lemma coherent_boundary : coherent C hcof hfib ≫
    NerveMovingParameterRelative.restriction (boundaries C) (parameters C)
      (boundaryInclusion C) (smallValues C) = fixedBoundary C hcof :=
  NerveMovingFamilyFit.extend_boundary _ _ _ _ _ _ _ _ _

/-- Recover the original small whole postcomparison interval, including every tuple degree. -/
lemma post_recover (X : FramedResolution C) (Y W : ResolutionObject C)
    (f : X.inner.base ⟶ Y.base) (g : Y ⟶ W) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor
    (NerveMovingParameter.evaluate (parameters C) (smallValues C) (coherent C hcof hfib)
      (Presentation.post X Y W f g)) =
    RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X.inner Y f)
      (CoherentLiftRelative.postBoundary X.inner Y W f g)
      (CoherentLiftRelative.postEdge hcof hfib X.inner Y W f g) := by
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor
    (coherent_evaluate C hcof hfib (Presentation.post X Y W f g))).trans
      (ResolutionArrowSelectedIntervals.post_recover hcof hfib X Y W f g)

/-- Recover the original small whole precomparison for the actual given frame map. -/
lemma pre_recover (X Y : FramedResolution C) (W : ResolutionObject C) (f : X ⟶ Y)
    (g : Y.inner.base ⟶ W.base) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor
    (NerveMovingParameter.evaluate (parameters C) (smallValues C) (coherent C hcof hfib)
      (Presentation.pre X Y W f g)) =
    RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion Y.inner W g)
      (CoherentLiftRelative.preBoundary X.inner Y.inner W f.map g)
      (CoherentLiftRelative.preEdge hcof hfib X.inner Y.inner W f.map g
        (FramedResolution.frameMap f)) := by
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor
    (coherent_evaluate C hcof hfib (Presentation.pre X Y W f g))).trans
      (ResolutionArrowSelectedIntervals.pre_recover hcof hfib X Y W f g)

end SerrePositivity.HomotopyFunctionComplex.SelectedIntervalDiagram
