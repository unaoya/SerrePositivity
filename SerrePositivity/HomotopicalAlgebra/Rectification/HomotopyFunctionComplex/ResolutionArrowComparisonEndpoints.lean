module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowTupleCoherence
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveArrowComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterEvaluation

/-!
# 中断した任意モデル源への一般化：ResolutionArrowComparisonEndpoints

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual all-center comparison endpoints retaining the old whole tuple interpolations。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0278][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0278
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual all-center comparison endpoints retaining the old whole tuple interpolations
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionArrowDiagram ResolutionArrowTuples ResolutionArrowTupleCoherence

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

abbrev parameter := NerveArrowComparison.source (bigTuples C)
abbrev values := NerveArrowComparison.target (fibers C)
abbrev vertexParameter := NerveArrowComparison.source (bigVertices C)
abbrev vertexInclusion : vertexParameter C ⟶ parameter C :=
  NerveArrowComparison.sourceMap (bigInclusion C)
abbrev vertexBoundary : vertexParameter C ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (values C) :=
  NerveArrowComparison.boundary (bigVertices C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (fibers C))
    (bigBoundary C)

/-- Both endpoints are transported restrictions of the same existing whole all-center system. -/
def left : NerveMovingParameter.System.{u, v} (parameter C) (values C) :=
  NerveArrowComparison.left (bigTuples C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (fibers C))
    (system C hcof)

def right : NerveMovingParameter.System.{u, v} (parameter C) (values C) :=
  NerveArrowComparison.right (bigTuples C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (fibers C))
    (system C hcof)

lemma left_vertices : left C hcof ≫ NerveBiparameterMaps.restriction
    (vertexParameter C) (parameter C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
      (vertexInclusion C) = NerveNaturalBoundary.ofNatTrans
        (vertexParameter C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C)) (vertexBoundary C) :=
  NerveArrowComparison.left_boundary _ _ _ (bigInclusion C) (bigBoundary C)
    (system C hcof) (vertices_fixed C hcof)

lemma right_vertices : right C hcof ≫ NerveBiparameterMaps.restriction
    (vertexParameter C) (parameter C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C))
      (vertexInclusion C) = NerveNaturalBoundary.ofNatTrans
        (vertexParameter C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (values C)) (vertexBoundary C) :=
  NerveArrowComparison.right_boundary _ _ _ (bigInclusion C) (bigBoundary C)
    (system C hcof) (vertices_fixed C hcof)

lemma left_evaluate (e : Arrow (Index C)) :
    NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e =
      oldFamily C hcof e.left ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((fibers C).map e.hom) := by
  change NerveMovingParameter.evaluate (parameter C) (values C)
    (NerveBiparameterMaps.mapTarget _ _ _
      (Functor.whiskerRight (NerveArrowComparison.transport (fibers C))
        SSet.uliftFunctor.{u, v})
      (NerveBiparameterMaps.reindex _ _ Arrow.leftFunc (system C hcof))) e = _
  rw [NerveBiparameterMaps.evaluate_mapTarget, NerveBiparameterMaps.evaluate_reindex,
    system_evaluate]
  rfl

lemma right_evaluate (e : Arrow (Index C)) :
    NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e =
      (bigTuples C).map e.hom ≫ oldFamily C hcof e.right := by
  change NerveMovingParameter.evaluate (parameter C) (values C)
    (NerveBiparameterMaps.restrict _ _ _ (NerveArrowComparison.transport (bigTuples C))
      (NerveBiparameterMaps.reindex _ _ Arrow.rightFunc (system C hcof))) e = _
  rw [NerveBiparameterMaps.evaluate_restrict, NerveBiparameterMaps.evaluate_reindex,
    system_evaluate]
  rfl

/-- Recover the actual original small interpolation followed by actual fiber transport. -/
lemma left_recover (e : Arrow (Index C)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (NerveMovingParameter.evaluate (parameter C) (values C) (left C hcof) e) =
    CoherentLiftTuples.interpolation hcof (source C e.left).inner (target C e.left)
      (arrow C e.left) ≫ (fibers C).map e.hom := by
  rw [left_evaluate, ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower_map _

/-- Recover actual tuple transport followed by the actual original small interpolation. -/
lemma right_recover (e : Arrow (Index C)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (NerveMovingParameter.evaluate (parameter C) (values C) (right C hcof) e) =
    (tuples C).map e.hom ≫ CoherentLiftTuples.interpolation hcof
      (source C e.right).inner (target C e.right) (arrow C e.right) := by
  rw [right_evaluate]
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((tuples C).map e.hom) ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (CoherentLiftTuples.interpolation hcof _ _ _)) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower_map _

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints
