module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedReassociation

/-!
# 中断した任意モデル源への一般化：ResolutionMixedIntervalRestrictions

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual restrictions of the same selected interval system to mixed square edges。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0321][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0321
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual restrictions of the same selected interval system to mixed square edges
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedReassociation

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions
variable (C : Type u) [Category.{v} C] [ModelCategory C]

def preAB : Index C ⥤ SelectedIntervalDiagram.Index C where
  obj p := .pre p.source p.middle p.target p.pre p.center
  map k := InducedCategory.homMk
    (Arrow.homMk ((cornerA C).map k) ((cornerB C).map k) ((edgeAB C).naturality k))
  map_id _ := rfl
  map_comp _ _ := rfl

def postAC : Index C ⥤ SelectedIntervalDiagram.Index C where
  obj p := .post p.middle p.target p.final p.center p.post
  map k := InducedCategory.homMk
    (Arrow.homMk ((cornerA C).map k) ((cornerC C).map k) ((edgeAC C).naturality k))
  map_id _ := rfl
  map_comp _ _ := rfl

def preCD : Index C ⥤ SelectedIntervalDiagram.Index C where
  obj p := .pre p.source p.middle p.final p.pre (p.center ≫ p.post.base)
  map k := InducedCategory.homMk
    (Arrow.homMk ((cornerC C).map k) ((cornerD C).map k) ((edgeCD C).naturality k))
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev intervalParameters := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1))
abbrev cParameters := cornerC C ⋙ ResolutionArrowTupleCoherence.bigTuples C
abbrev cIntervalParameters := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (cParameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1))
abbrev bValues := cornerB C ⋙ ResolutionArrowDiagram.fibers C
abbrev cValues := cornerC C ⋙ ResolutionArrowDiagram.fibers C

abbrev bParameters := cornerB C ⋙ ResolutionArrowTupleCoherence.bigTuples C
abbrev bIntervalParameters := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (bParameters C)
  (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1))
abbrev leftFinalValues := finalLeft C ⋙ ResolutionArrowDiagram.fibers C

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev preABSystem : NerveMovingParameter.System.{u, v} (intervalParameters C) (bValues C) :=
  NerveBiparameterMaps.reindex _ _ (preAB C) (SelectedIntervalDiagram.coherent C hcof hfib)
abbrev postACSystem : NerveMovingParameter.System.{u, v} (intervalParameters C) (cValues C) :=
  NerveBiparameterMaps.reindex _ _ (postAC C) (SelectedIntervalDiagram.coherent C hcof hfib)
abbrev preCDSystem : NerveMovingParameter.System.{u, v} (cIntervalParameters C) (smallValues C) :=
  NerveBiparameterMaps.reindex _ _ (preCD C) (SelectedIntervalDiagram.coherent C hcof hfib)

/-- Use the same chosen whole preinterval system, with actual target transport to corner D. -/
def intervalAB : NerveMovingParameter.System.{u, v} (intervalParameters C) (smallValues C) :=
  NerveBiparameterMaps.mapTarget _ _ _
    (Functor.whiskerRight (Functor.whiskerRight (edgeBD C) (ResolutionArrowDiagram.fibers C))
      SSet.uliftFunctor.{u, v}) (preABSystem C hcof hfib)

/-- Use the same chosen whole postinterval system, with actual target transport to corner D. -/
def intervalAC : NerveMovingParameter.System.{u, v} (intervalParameters C) (smallValues C) :=
  NerveBiparameterMaps.mapTarget _ _ _
    (Functor.whiskerRight (Functor.whiskerRight (edgeCD C) (ResolutionArrowDiagram.fibers C))
      SSet.uliftFunctor.{u, v}) (postACSystem C hcof hfib)

/-- Use the same chosen whole preinterval system, with actual tuple transport from corner A. -/
def intervalCD : NerveMovingParameter.System.{u, v} (intervalParameters C) (smallValues C) :=
  NerveBiparameterMaps.restrict _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (parameters C) (cParameters C)
      (Functor.whiskerRight (edgeAC C) (ResolutionArrowTupleCoherence.bigTuples C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 1))) (preCDSystem C hcof hfib)

abbrev postBDSystem : NerveMovingParameter.System.{u, v} (bIntervalParameters C)
    (leftFinalValues C) :=
  NerveBiparameterMaps.reindex _ _ (postBD C) (SelectedIntervalDiagram.coherent C hcof hfib)

abbrev castBDSystem : NerveMovingParameter.System.{u, v} (bIntervalParameters C) (smallValues C) :=
  NerveBiparameterMaps.mapTarget _ _ _
    (Functor.whiskerRight (Functor.whiskerRight (toFinal C).hom (ResolutionArrowDiagram.fibers C))
      SSet.uliftFunctor.{u, v}) (postBDSystem C hcof hfib)

/-- The fourth original whole interval uses the actual natural reassociation and tuple transport. -/
def intervalBD : NerveMovingParameter.System.{u, v} (intervalParameters C) (smallValues C) :=
  NerveBiparameterMaps.restrict _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (parameters C) (bParameters C)
      (Functor.whiskerRight (edgeAB C) (ResolutionArrowTupleCoherence.bigTuples C))
        (SSet.stdSimplex.obj (SimplexCategory.mk 1))) (castBDSystem C hcof hfib)

lemma preAB_evaluate (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C)
    (bValues C) (preABSystem C hcof hfib) p =
    ResolutionArrowSelectedIntervals.preFamily hcof hfib p.source p.middle p.target p.pre
      p.center :=
  (NerveBiparameterMaps.evaluate_reindex (SelectedIntervalDiagram.parameters C)
    (SelectedIntervalDiagram.smallValues C) (SelectedIntervalDiagram.coherent C hcof hfib)
      (preAB C) p).trans (SelectedIntervalDiagram.coherent_evaluate C hcof hfib _)

lemma postAC_evaluate (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C)
    (cValues C) (postACSystem C hcof hfib) p =
    ResolutionArrowSelectedIntervals.postFamily hcof hfib p.middle p.target p.final p.center
      p.post :=
  (NerveBiparameterMaps.evaluate_reindex (SelectedIntervalDiagram.parameters C)
    (SelectedIntervalDiagram.smallValues C) (SelectedIntervalDiagram.coherent C hcof hfib)
      (postAC C) p).trans (SelectedIntervalDiagram.coherent_evaluate C hcof hfib _)

lemma preCD_evaluate (p : Index C) : NerveMovingParameter.evaluate (cIntervalParameters C)
    (smallValues C) (preCDSystem C hcof hfib) p =
    ResolutionArrowSelectedIntervals.preFamily hcof hfib p.source p.middle p.final p.pre
      (p.center ≫ p.post.base) :=
  (NerveBiparameterMaps.evaluate_reindex (SelectedIntervalDiagram.parameters C)
    (SelectedIntervalDiagram.smallValues C) (SelectedIntervalDiagram.coherent C hcof hfib)
      (preCD C) p).trans (SelectedIntervalDiagram.coherent_evaluate C hcof hfib _)

lemma intervalAB_evaluate (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C)
    (smallValues C) (intervalAB C hcof hfib) p =
    ResolutionArrowSelectedIntervals.preFamily hcof hfib p.source p.middle p.target p.pre p.center ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionArrowDiagram.fibers C).map (bd C p)) := by
  change NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (NerveBiparameterMaps.mapTarget _ _ _ _ (preABSystem C hcof hfib)) p = _
  rw [NerveBiparameterMaps.evaluate_mapTarget, preAB_evaluate]
  rfl

lemma intervalAC_evaluate (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C)
    (smallValues C) (intervalAC C hcof hfib) p =
    ResolutionArrowSelectedIntervals.postFamily hcof hfib p.middle p.target p.final p.center
      p.post ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionArrowDiagram.fibers C).map (cd C p)) := by
  change NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (NerveBiparameterMaps.mapTarget _ _ _ _ (postACSystem C hcof hfib)) p = _
  rw [NerveBiparameterMaps.evaluate_mapTarget, postAC_evaluate]
  rfl

lemma intervalCD_evaluate (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C)
    (smallValues C) (intervalCD C hcof hfib) p =
    ((ResolutionArrowTupleCoherence.bigTuples C).map (ac C p) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        ResolutionArrowSelectedIntervals.preFamily hcof hfib p.source p.middle p.final p.pre
          (p.center ≫ p.post.base) := by
  change NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (NerveBiparameterMaps.restrict _ _ _ _ (preCDSystem C hcof hfib)) p = _
  rw [NerveBiparameterMaps.evaluate_restrict, preCD_evaluate]
  rfl

lemma postBD_evaluate (p : Index C) : NerveMovingParameter.evaluate (bIntervalParameters C)
    (leftFinalValues C) (postBDSystem C hcof hfib) p =
    ResolutionArrowSelectedIntervals.postFamily hcof hfib p.source p.target p.final
      (p.pre.map.base ≫ p.center) p.post :=
  (NerveBiparameterMaps.evaluate_reindex (SelectedIntervalDiagram.parameters C)
    (SelectedIntervalDiagram.smallValues C) (SelectedIntervalDiagram.coherent C hcof hfib)
      (postBD C) p).trans (SelectedIntervalDiagram.coherent_evaluate C hcof hfib _)

lemma castBD_evaluate (p : Index C) : NerveMovingParameter.evaluate (bIntervalParameters C)
    (smallValues C) (castBDSystem C hcof hfib) p =
    ResolutionArrowSelectedIntervals.postFamily hcof hfib p.source p.target p.final
      (p.pre.map.base ≫ p.center) p.post ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} ((ResolutionArrowDiagram.fibers C).map (finalIso C p).hom) := by
  change NerveMovingParameter.evaluate (bIntervalParameters C) (smallValues C)
    (NerveBiparameterMaps.mapTarget _ _ _ _ (postBDSystem C hcof hfib)) p = _
  rw [NerveBiparameterMaps.evaluate_mapTarget, postBD_evaluate]
  rfl

lemma intervalBD_evaluate (p : Index C) : NerveMovingParameter.evaluate (intervalParameters C)
    (smallValues C) (intervalBD C hcof hfib) p =
    ((ResolutionArrowTupleCoherence.bigTuples C).map (ab C p) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        ResolutionArrowSelectedIntervals.postFamily hcof hfib p.source p.target p.final
          (p.pre.map.base ≫ p.center) p.post ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
            (CoherentLiftMixedComparison.castMap p.source.inner p.middle.inner p.target p.final
              p.pre.map p.center p.post) := by
  change NerveMovingParameter.evaluate (intervalParameters C) (smallValues C)
    (NerveBiparameterMaps.restrict _ _ _ _ (castBDSystem C hcof hfib)) p = _
  rw [NerveBiparameterMaps.evaluate_restrict, castBD_evaluate]
  exact congrArg (fun k =>
    ((ResolutionArrowTupleCoherence.bigTuples C).map (ab C p) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        ResolutionArrowSelectedIntervals.postFamily hcof hfib p.source p.target p.final
          (p.pre.map.base ≫ p.center) p.post ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} k) (fiber_cast C p)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions
