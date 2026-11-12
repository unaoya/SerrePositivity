module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowDiagram
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameterRelative

/-!
# 中断した任意モデル源への一般化：ResolutionArrowParameters

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All-center coherent families with the actual moving factorization parameter。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0284][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0284
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All-center coherent families with the actual moving factorization parameter

Parameters change with each central arrow. A chain's parameter comes from
its first center and its small value from the last center. No constant
parameter or model structure on large auxiliary values is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowParameters
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev parameters : ResolutionArrowDiagram.Index C ⥤ SSet.{max u v} :=
  ResolutionArrowDiagram.baseIndex C ⋙ ArrowContext.parameters C

lemma parameter_map {q r : ResolutionArrowDiagram.Index C} (f : q ⟶ r) :
    (parameters C).map f = AnchoredChain.mapFunctor
      (ArrowContext.factorizationMap ((ResolutionArrowDiagram.baseIndex C).map f)) := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (families : ∀ q, (parameters C).obj q ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((ResolutionArrowDiagram.fibers C).obj q))

/-- Retain every whole original family on its moving central-arrow parameter. -/
def system : NerveMovingParameter.System.{u, v} (parameters C)
    (ResolutionArrowDiagram.fibers C) :=
  NerveMovingParameter.extendFamilies.{u, v} (parameters C) (ResolutionArrowDiagram.fibers C)
    (ResolutionArrowDiagram.fillers C hcof) families

lemma system_evaluate (q : ResolutionArrowDiagram.Index C) :
    NerveMovingParameter.evaluate.{u, v} (parameters C) (ResolutionArrowDiagram.fibers C)
      (system C hcof families) q = families q :=
  NerveMovingParameter.extendFamilies_evaluate _ _ _ _ q

lemma system_compatibility {s t : Index (ResolutionArrowDiagram.Index C)} (f : s ⟶ t) :
    SSet.stdSimplex.map (operator f) ≫ (system C hcof families).app t =
      (system C hcof families).app s ≫
        (CategoryTheory.MonoidalClosed.pre ((parameters C).map (NerveSimplexStart.startMap f))).app
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} ((ResolutionArrowDiagram.fibers C).obj (endpoint s))) ≫
        (CategoryTheory.ihom ((parameters C).obj (NerveSimplexStart.start t))).map
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionArrowDiagram.fibers C).map (endpointMap f))) :=
  NerveBiparameter.compatibility _ _ _ f

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowParameters
