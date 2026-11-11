module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.SelectedIntervalEndpoints
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedReassociationEquality
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveProductEndpointTransport

/-!
# 中断した任意モデル源への一般化：ResolutionMixedRawEndpoints

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Exact whole endpoints before the final mixed parameter and value transports。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0322][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0322
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Exact whole endpoints before the final mixed parameter and value transports
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedReassociation ResolutionMixedIntervalRestrictions
open NerveBiparameterMaps NerveArrowComparisonComposition

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedRawEndpoints
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev K := ResolutionArrowTupleCoherence.bigTuples C
abbrev F := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (ResolutionArrowDiagram.fibers C)
abbrev chosen := ResolutionArrowTupleCoherence.system C hcof

abbrev leftAB := leftAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerB C) (edgeAB C)

abbrev rightAB := rightAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerB C) (edgeAB C)

lemma AB_zero : preABSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftAB C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (preAB C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_left C hcof (preAB C))

lemma AB_one : preABSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightAB C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (preAB C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_right C hcof (preAB C))

abbrev leftAC := leftAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerC C) (edgeAC C)

abbrev rightAC := rightAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerC C) (edgeAC C)

lemma AC_zero : postACSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftAC C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (postAC C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_left C hcof (postAC C))

lemma AC_one : postACSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (intervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (parameters C)) =
    NerveProductParameter.expand (parameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightAC C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (postAC C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_right C hcof (postAC C))

abbrev leftCD := leftAlong (K C) (F C) (chosen C hcof) (cornerC C) (cornerD C) (edgeCD C)

abbrev rightCD := rightAlong (K C) (F C) (chosen C hcof) (cornerC C) (cornerD C) (edgeCD C)

lemma CD_zero : preCDSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (cParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (cIntervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (cParameters C)) =
    NerveProductParameter.expand (cParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftCD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (preCD C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (cParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_left C hcof (preCD C))

lemma CD_one : preCDSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (cParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (cIntervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (cParameters C)) =
    NerveProductParameter.expand (cParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightCD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (preCD C)).trans
  exact congrArg (fun a => NerveProductParameter.expand (cParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) a)
      (SelectedIntervalEndpoints.reindex_right C hcof (preCD C))

abbrev leftBD := leftAlong (K C) (F C) (chosen C hcof) (cornerB C) (finalLeft C) (edgeBDLeft C)

abbrev rightBD := rightAlong (K C) (F C) (chosen C hcof) (cornerB C) (finalLeft C) (edgeBDLeft C)

lemma BD_zero : postBDSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (bParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (bIntervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (1 : Fin 2)) (bParameters C)) =
    NerveProductParameter.expand (bParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (leftBD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_zero C hcof hfib (postBD C)).trans
  have hτ : Functor.whiskerLeft (postBD C ⋙ SelectedIntervalDiagram.forget C)
      Arrow.leftToRight = edgeBDLeft C := by
    apply NatTrans.ext
    funext p
    exact (edgeBDLeft_app C p).symm
  have he := SelectedIntervalEndpoints.reindex_left C hcof (postBD C)
  rw [hτ] at he
  exact congrArg (fun a => NerveProductParameter.expand (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk
      0)) a) he

lemma BD_one : postBDSystem C hcof hfib ≫ restriction
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (bParameters C)
      (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0))) (bIntervalParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C))
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ (0 : Fin 2)) (bParameters C)) =
    NerveProductParameter.expand (bParameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C))
      (SSet.stdSimplex.obj (SimplexCategory.mk 0)) (rightBD C hcof) := by
  apply (SelectedIntervalEndpoints.reindexed_one C hcof hfib (postBD C)).trans
  have hτ : Functor.whiskerLeft (postBD C ⋙ SelectedIntervalDiagram.forget C)
      Arrow.leftToRight = edgeBDLeft C := by
    apply NatTrans.ext
    funext p
    exact (edgeBDLeft_app C p).symm
  have he := SelectedIntervalEndpoints.reindex_right C hcof (postBD C)
  rw [hτ] at he
  exact congrArg (fun a => NerveProductParameter.expand (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C)) (SSet.stdSimplex.obj (SimplexCategory.mk
      0)) a) he

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedRawEndpoints
