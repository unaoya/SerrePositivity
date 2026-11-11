module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.BiresolutionRightMapping
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowActionFunctors

/-!
# 中断した任意モデル源への一般化：BiresolutionRightAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual opposite-model lift choices act on the right rows of the double Hom。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0062][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0062
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual opposite-model lift choices act on the right rows of the double Hom

The source simplex operator and changes of the entire lift center retain
the same actual parameter family. All values remain in SSet[v].
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.BiresolutionRightAction
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev Centers := ResolutionArrowDiagram.Index Cᵒᵖ
abbrev choices : Centers C ⥤ SSet.{v} := ResolutionArrowDiagram.fibers Cᵒᵖ

abbrev inputPair (q : Centers C) (A : (FramedResolution C)ᵒᵖ) :
    RightResolutionMapping.Index C :=
  (A, op (FramedResolution.ofResolution (ResolutionArrowDiagram.target Cᵒᵖ q)))
abbrev outputPair (q : Centers C) (A : (FramedResolution C)ᵒᵖ) :
    RightResolutionMapping.Index C := (A, op (ResolutionArrowDiagram.source Cᵒᵖ q))

abbrev sourcePoint (A : (FramedResolution C)ᵒᵖ) (m : SimplexCategoryᵒᵖ) : Cᵒᵖ :=
  ((BiresolutionRightMapping.sourcePoints (C := C)).obj m).obj A

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof in
lemma choice_fillers (q : Centers C) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers ((choices C).obj q) :=
  ResolutionArrowDiagram.fillers Cᵒᵖ hcof q

/-- All old point choices in the opposite model extend to one coherent system. -/
abbrev coherent : SimplicialModel.NerveCoherentFamily.System (choices C) :=
  ResolutionArrowDiagram.selectedSystem Cᵒᵖ hcof

include hcof in
lemma coherent_point (q : Centers C) :
    (coherent C hcof).app
        (SerrePositivity.NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ q)) =
      ResolutionArrowDiagram.selectedPoint Cᵒᵖ q :=
  ResolutionArrowDiagram.selectedSystem_point Cᵒᵖ hcof q

/-- The output is exactly the right mapping row used in the balanced comparison. -/
def action (q : Centers C) (A : (FramedResolution C)ᵒᵖ) (m : SimplexCategoryᵒᵖ)
    {T : SSet.{v}} (s : T ⟶ (choices C).obj q)
    (t : T ⟶ ((BiresolutionRightMapping.rawRows.obj m).obj (inputPair C q A))) :
    T ⟶ ((BiresolutionRightMapping.rows hcof hfib).obj m).obj (outputPair C q A) :=
  ResolutionArrowActionTransport.kan Cᵒᵖ hcof hfib q (sourcePoint C A m) s t

lemma action_selectedPoint (q : Centers C) (A : (FramedResolution C)ᵒᵖ)
    (m : SimplexCategoryᵒᵖ) {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (t : T ⟶ (BiresolutionRightMapping.rawRows.obj m).obj (inputPair C q A)) :
    action C hcof hfib q A m (d ≫ ResolutionArrowDiagram.selectedPoint Cᵒᵖ q) t =
      t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap
          (ResolutionObject.lift (ResolutionArrowDiagram.arrow Cᵒᵖ q)).diagram).app
            (sourcePoint C A m) ≫
        KanLiftAction.comparison hcof hfib (ResolutionArrowDiagram.source Cᵒᵖ q).inner
          (sourcePoint C A m) :=
  KanLiftAction.ofLift hcof hfib
    (ResolutionObject.lift (ResolutionArrowDiagram.arrow Cᵒᵖ q)) (sourcePoint C A m) d t

lemma action_parameter (q : Centers C) (A : (FramedResolution C)ᵒᵖ)
    (m : SimplexCategoryᵒᵖ) {T U : SSet.{v}} (a : U ⟶ T)
    (s : T ⟶ (choices C).obj q)
    (t : T ⟶ (BiresolutionRightMapping.rawRows.obj m).obj (inputPair C q A)) :
    a ≫ action C hcof hfib q A m s t = action C hcof hfib q A m (a ≫ s) (a ≫ t) :=
  KanLiftAction.parameterized_naturality hcof hfib _ _ _ _ a s t

lemma action_source_operator (q : Centers C) (A : (FramedResolution C)ᵒᵖ)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {T : SSet.{v}}
    (s : T ⟶ (choices C).obj q)
    (t : T ⟶ (BiresolutionRightMapping.rawRows.obj n).obj (inputPair C q A)) :
    action C hcof hfib q A m s
        (t ≫ ((BiresolutionRightMapping.rawRows.map θ).app (inputPair C q A))) =
      action C hcof hfib q A n s t ≫
        (((BiresolutionRightMapping.rows hcof hfib).map θ).app (outputPair C q A)) := by
  rw [BiresolutionRightMapping.raw_operator, BiresolutionRightMapping.hom_operator]
  exact KanLiftAction.parameterized_target_naturality hcof hfib _ _ _
    ((BiresolutionRightMapping.sourcePoints.map θ).app A) s t

lemma action_center {q r : Centers C} (f : q ⟶ r) (A : (FramedResolution C)ᵒᵖ)
    (m : SimplexCategoryᵒᵖ) {T : SSet.{v}} (s : T ⟶ (choices C).obj q)
    (t : T ⟶ (BiresolutionRightMapping.rawRows.obj m).obj (inputPair C r A)) :
    action C hcof hfib r A m (s ≫ (choices C).map f) t =
      action C hcof hfib q A m s
          (t ≫ (ResolutionArrowActionFunctors.input Cᵒᵖ (sourcePoint C A m)).map f.op) ≫
        (ResolutionArrowActionFunctors.output Cᵒᵖ hcof hfib (sourcePoint C A m)).map f :=
  ResolutionArrowActionTransport.kan_transport Cᵒᵖ hcof hfib f (sourcePoint C A m) s t

end SerrePositivity.HomotopyFunctionComplex.BiresolutionRightAction
