module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedFaceSystems
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.SelectedIntervalVertices
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveNaturalBoundaryTransport

/-!
# 中断した任意モデル源への一般化：ResolutionMixedVertexRestrictions

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The same mixed interval systems fix the whole common vertex cylinder。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0329][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0329
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The same mixed interval systems fix the whole common vertex cylinder
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open HomotopicalAlgebra SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedIntervalRestrictions ResolutionMixedReassociation
open NerveBiparameterMaps NerveCylinderBoundary

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev V := ResolutionArrowTupleCoherence.bigVertices C
abbrev K := ResolutionArrowTupleCoherence.bigTuples C
abbrev F := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (ResolutionArrowDiagram.fibers C)
abbrev rawBoundary (H J : Index C ⥤ ResolutionArrowDiagram.Index C) (τ : H ⟶ J) :=
  Functor.whiskerLeft H (ResolutionArrowTupleCoherence.bigBoundary C) ≫
    Functor.whiskerRight τ (F C)
abbrev rawInclusion (H : Index C ⥤ ResolutionArrowDiagram.Index C) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal (H ⋙ V C) (H ⋙ K C)
    (Functor.whiskerLeft H (ResolutionArrowTupleCoherence.bigInclusion C))
      ResolutionArrowCylinderBoundary.interval.{max u v}
abbrev vertices := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (vertexParameters C) ResolutionArrowCylinderBoundary.interval.{max u v}
abbrev vertexMap := rawInclusion C (cornerA C)
abbrev fixedVertices := NerveNaturalBoundary.ofNatTrans (vertices C)
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
  (NerveProductParameter.projection (vertexParameters C)
    ResolutionArrowCylinderBoundary.interval.{max u v} ≫ vertexBoundary C)

lemma preAB_vertices : preABSystem C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C)) (rawInclusion C (cornerA C)) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection (cornerA C ⋙ V C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
        rawBoundary C (cornerA C) (cornerB C) (edgeAB C)) :=
  SelectedIntervalVertices.reindexed_vertices C hcof hfib (preAB C)

lemma postAC_vertices : postACSystem C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C)) (rawInclusion C (cornerA C)) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection (cornerA C ⋙ V C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
        rawBoundary C (cornerA C) (cornerC C) (edgeAC C)) :=
  SelectedIntervalVertices.reindexed_vertices C hcof hfib (postAC C)

lemma preCD_vertices : preCDSystem C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (rawInclusion C (cornerC C)) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection (cornerC C ⋙ V C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
        rawBoundary C (cornerC C) (cornerD C) (edgeCD C)) :=
  SelectedIntervalVertices.reindexed_vertices C hcof hfib (preCD C)

lemma postBD_vertices : postBDSystem C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C)) (rawInclusion C (cornerB C)) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection (cornerB C ⋙ V C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
        rawBoundary C (cornerB C) (finalLeft C) (edgeBDLeft C)) :=
by
  apply (SelectedIntervalVertices.reindexed_vertices C hcof hfib (postBD C)).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  apply NatTrans.ext
  funext p
  change fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (b C p) ≫
    (F C).map (ResolutionArrowElementary.post p.source p.target p.final
      (p.pre.map.base ≫ p.center) p.post)) =
    fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (b C p) ≫
      (F C).map ((edgeBDLeft C).app p))
  exact congrArg (fun k => fst _ _ ≫ (ResolutionArrowTupleCoherence.bigBoundary C).app
    (b C p) ≫ (F C).map k) (edgeBDLeft_app C p).symm

lemma AB_vertices : intervalAB C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (vertexMap C) = fixedVertices C := by
  change mapTarget _ _ _ _ (preABSystem C hcof hfib) ≫ _ = _
  rw [NerveProductEndpointTransport.mapTarget_restrict, preAB_vertices]
  apply (mapTarget_natural (vertices C) (cornerB C ⋙ F C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (Functor.whiskerRight (edgeBD C) (F C)) _).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  apply NatTrans.ext
  funext p
  change (fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (a C p) ≫
    (F C).map (ab C p))) ≫ (F C).map (bd C p) =
      fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (a C p) ≫
        (F C).map (ab C p ≫ bd C p))
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

lemma AC_vertices : intervalAC C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (vertexMap C) = fixedVertices C := by
  change mapTarget _ _ _ _ (postACSystem C hcof hfib) ≫ _ = _
  rw [NerveProductEndpointTransport.mapTarget_restrict, postAC_vertices]
  apply (mapTarget_natural (vertices C) (cornerC C ⋙ F C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (Functor.whiskerRight (edgeCD C) (F C)) _).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  apply NatTrans.ext
  funext p
  change (fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (a C p) ≫
    (F C).map (ac C p))) ≫ (F C).map (cd C p) =
      fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (a C p) ≫
        (F C).map (ab C p ≫ bd C p))
  rw [commutes C p, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

lemma CD_vertices : intervalCD C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (vertexMap C) = fixedVertices C := by
  have hs : Functor.whiskerLeft (cornerA C) (ResolutionArrowTupleCoherence.bigInclusion C) ≫
      Functor.whiskerRight (edgeAC C) (K C) =
      Functor.whiskerRight (edgeAC C) (V C) ≫
        Functor.whiskerLeft (cornerC C) (ResolutionArrowTupleCoherence.bigInclusion C) := by
    apply NatTrans.ext
    funext p
    exact ((ResolutionArrowTupleCoherence.bigInclusion C).naturality (ac C p)).symm
  apply (NerveNaturalBoundaryTransport.horizontal_fixed (cornerA C ⋙ V C) (parameters C)
    (cornerC C ⋙ V C) (cParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (Functor.whiskerLeft (cornerA C) (ResolutionArrowTupleCoherence.bigInclusion C))
    (Functor.whiskerLeft (cornerC C) (ResolutionArrowTupleCoherence.bigInclusion C))
    (Functor.whiskerRight (edgeAC C) (K C)) (Functor.whiskerRight (edgeAC C) (V C)) hs
    ResolutionArrowCylinderBoundary.interval.{max u v} (preCDSystem C hcof hfib) (rawBoundary C
      (cornerC C) (cornerD C) (edgeCD C))
    (preCD_vertices C hcof hfib)).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  have hn : Functor.whiskerRight (edgeAC C) (V C) ≫
      rawBoundary C (cornerC C) (cornerD C) (edgeCD C) = vertexBoundary C := by
    apply NatTrans.ext
    funext p
    change (V C).map (ac C p) ≫
      ((ResolutionArrowTupleCoherence.bigBoundary C).app (c C p) ≫ (F C).map (cd C p)) =
      (ResolutionArrowTupleCoherence.bigBoundary C).app (a C p) ≫
        (F C).map (ab C p ≫ bd C p)
    rw [← Category.assoc, (ResolutionArrowTupleCoherence.bigBoundary C).naturality,
      Category.assoc, ← CategoryTheory.Functor.map_comp, ← commutes C p]
  exact congrArg (fun b => NerveProductParameter.projection (vertexParameters C)
    ResolutionArrowCylinderBoundary.interval.{max u v} ≫ b) hn

lemma castBD_vertices : castBDSystem C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (rawInclusion C (cornerB C)) =
    NerveNaturalBoundary.ofNatTrans _ _
      (NerveProductParameter.projection (cornerB C ⋙ V C)
        ResolutionArrowCylinderBoundary.interval.{max u v} ≫
        rawBoundary C (cornerB C) (cornerD C) (edgeBD C)) := by
  change mapTarget _ _ _ _ (postBDSystem C hcof hfib) ≫ _ = _
  rw [NerveProductEndpointTransport.mapTarget_restrict, postBD_vertices]
  apply (mapTarget_natural (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (cornerB C ⋙ V C)
    ResolutionArrowCylinderBoundary.interval.{max u v}) (finalLeft C ⋙ F C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (Functor.whiskerRight (toFinal C).hom (F C)) _).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  apply NatTrans.ext
  funext p
  change (fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (b C p) ≫
    (F C).map ((edgeBDLeft C).app p))) ≫ (F C).map ((toFinal C).hom.app p) =
    fst _ _ ≫ ((ResolutionArrowTupleCoherence.bigBoundary C).app (b C p) ≫ (F C).map (bd C p))
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun k => fst _ _ ≫ (ResolutionArrowTupleCoherence.bigBoundary C).app
    (b C p) ≫ (F C).map k) (congr_app (ResolutionMixedEndpointCompatibility.bd_finish C) p)

lemma BD_vertices : intervalBD C hcof hfib ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (vertexMap C) = fixedVertices C := by
  have hs : Functor.whiskerLeft (cornerA C) (ResolutionArrowTupleCoherence.bigInclusion C) ≫
      Functor.whiskerRight (edgeAB C) (K C) =
      Functor.whiskerRight (edgeAB C) (V C) ≫
        Functor.whiskerLeft (cornerB C) (ResolutionArrowTupleCoherence.bigInclusion C) := by
    apply NatTrans.ext
    funext p
    exact ((ResolutionArrowTupleCoherence.bigInclusion C).naturality (ab C p)).symm
  apply (NerveNaturalBoundaryTransport.horizontal_fixed (cornerA C ⋙ V C) (parameters C)
    (cornerB C ⋙ V C) (bParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (Functor.whiskerLeft (cornerA C) (ResolutionArrowTupleCoherence.bigInclusion C))
    (Functor.whiskerLeft (cornerB C) (ResolutionArrowTupleCoherence.bigInclusion C))
    (Functor.whiskerRight (edgeAB C) (K C)) (Functor.whiskerRight (edgeAB C) (V C)) hs
    ResolutionArrowCylinderBoundary.interval.{max u v} (castBDSystem C hcof hfib) (rawBoundary C
      (cornerB C) (cornerD C) (edgeBD C))
    (castBD_vertices C hcof hfib)).trans
  apply congrArg (NerveNaturalBoundary.ofNatTrans _ _)
  have hn : Functor.whiskerRight (edgeAB C) (V C) ≫
      rawBoundary C (cornerB C) (cornerD C) (edgeBD C) = vertexBoundary C := by
    apply NatTrans.ext
    funext p
    change (V C).map (ab C p) ≫
      ((ResolutionArrowTupleCoherence.bigBoundary C).app (b C p) ≫ (F C).map (bd C p)) =
      (ResolutionArrowTupleCoherence.bigBoundary C).app (a C p) ≫
        (F C).map (ab C p ≫ bd C p)
    rw [← Category.assoc, (ResolutionArrowTupleCoherence.bigBoundary C).naturality,
      Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun b => NerveProductParameter.projection (vertexParameters C)
    ResolutionArrowCylinderBoundary.interval.{max u v} ≫ b) hn

lemma faces_vertices (side : Bool) (k : Fin 3) :
    ResolutionMixedFaceSystems.faces C hcof hfib side k ≫ restriction _ _
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (vertexMap C) = fixedVertices C := by
  cases side <;> fin_cases k
  · exact CD_vertices C hcof hfib
  · exact ResolutionMixedCoherentDiagonal.coherent_vertices C hcof hfib
  · exact AC_vertices C hcof hfib
  · exact BD_vertices C hcof hfib
  · exact ResolutionMixedCoherentDiagonal.coherent_vertices C hcof hfib
  · exact AB_vertices C hcof hfib

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions
