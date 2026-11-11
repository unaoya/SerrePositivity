module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedRawEndpoints

/-!
# 中断した任意モデル源への一般化：ResolutionMixedEndpointCompatibility

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The same four interval systems share exactly the same whole corner systems。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0319][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0319
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The same four interval systems share exactly the same whole corner systems
-/

@[expose] public section
universe v u w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedReassociation ResolutionMixedReassociationEquality
open ResolutionMixedIntervalRestrictions ResolutionMixedRawEndpoints
open NerveBiparameterMaps NerveArrowComparisonComposition

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev point := SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0)
abbrev pointParameters := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (parameters C) point.{max u v}
abbrev faceMap (ε : Fin 2) : pointParameters C ⟶ intervalParameters C :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ ε) (parameters C)
abbrev toB := Functor.whiskerRight (edgeAB C) (K C)
abbrev toC := Functor.whiskerRight (edgeAC C) (K C)
abbrev fromB := Functor.whiskerRight (edgeBD C) (F C)
abbrev fromC := Functor.whiskerRight (edgeCD C) (F C)
abbrev castFinal := Functor.whiskerRight (toFinal C).hom (F C)

abbrev corner0 := leftAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerD C)
  (ResolutionMixedDiagram.diagonal C)
abbrev corner1 := mapTarget (parameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C))
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (fromB C) (rightAB C hcof)
abbrev corner2 := restrict (parameters C) (cParameters C)
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (toC C) (leftCD C hcof)
abbrev corner3 := rightAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerD C)
  (ResolutionMixedDiagram.diagonal C)

abbrev expand (a : NerveMovingParameter.System.{u, v} (parameters C) (smallValues C)) :=
  NerveProductParameter.expand (parameters C) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    point.{max u v} a
abbrev endpoint (a : NerveMovingParameter.System.{u, v} (intervalParameters C) (smallValues C))
    (ε : Fin 2) := a ≫ restriction (pointParameters C) (intervalParameters C)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (faceMap C ε)

omit [ModelCategory SSet.{v}] in
lemma bd_finish : edgeBDLeft C ≫ (toFinal C).hom = edgeBD C := by
  change (edgeBD C ≫ (toFinal C).inv) ≫ (toFinal C).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [ModelCategory SSet.{v}] in
lemma bd_finish_eq : edgeBDLeft C ≫ eqToHom (finalLeft_eq C) = edgeBD C := by
  have hh : (toFinal C).hom = eqToHom (finalLeft_eq C) := congrArg Iso.hom (toFinal_eq C)
  exact (congrArg (fun k => edgeBDLeft C ≫ k) hh.symm).trans (bd_finish C)

lemma bd_left_finish : mapTarget _ _ _ (castFinal C) (leftBD C hcof) =
    leftAlong (K C) (F C) (chosen C hcof) (cornerB C) (cornerD C) (edgeBD C) :=
  (left_follow (K C) (F C) (chosen C hcof) (cornerB C) (finalLeft C) (cornerD C)
    (edgeBDLeft C) (toFinal C).hom).trans
      (congrArg (fun τ => leftAlong (K C) (F C) (chosen C hcof) (cornerB C) (cornerD C) τ)
        (bd_finish C))

lemma bd_right_finish : mapTarget _ _ _ (castFinal C) (rightBD C hcof) =
    rightAlong (K C) (F C) (chosen C hcof) (cornerB C) (cornerD C) (edgeBD C) := by
  have hh : (toFinal C).hom = eqToHom (finalLeft_eq C) := congrArg Iso.hom (toFinal_eq C)
  change mapTarget _ _ _ (Functor.whiskerRight (toFinal C).hom (F C)) (rightBD C hcof) = _
  rw [hh]
  exact (right_follow_eq (K C) (F C) (chosen C hcof) (cornerB C) (finalLeft C) (cornerD C)
    (edgeBDLeft C) (finalLeft_eq C)).trans
      (congrArg (fun τ => rightAlong (K C) (F C) (chosen C hcof) (cornerB C) (cornerD C) τ)
        (bd_finish_eq C))

lemma AB_zero : endpoint C (intervalAB C hcof hfib) 1 = expand C (corner0 C hcof) := by
  apply (NerveProductEndpointTransport.mapTarget_endpoint (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (fromB C) (SSet.stdSimplex.δ (1 : Fin 2)) (preABSystem C hcof hfib) (leftAB C hcof)
      (ResolutionMixedRawEndpoints.AB_zero C hcof hfib)).trans
  exact congrArg (expand C)
    (left_follow (K C) (F C) (chosen C hcof) (cornerA C) (cornerB C) (cornerD C)
      (edgeAB C) (edgeBD C))

lemma AB_one : endpoint C (intervalAB C hcof hfib) 0 = expand C (corner1 C hcof) :=
  NerveProductEndpointTransport.mapTarget_endpoint (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (bValues C)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (fromB C) (SSet.stdSimplex.δ (0 : Fin 2)) (preABSystem C hcof hfib) (rightAB C hcof)
      (ResolutionMixedRawEndpoints.AB_one C hcof hfib)

lemma AC_zero : endpoint C (intervalAC C hcof hfib) 1 = expand C (corner0 C hcof) := by
  apply (NerveProductEndpointTransport.mapTarget_endpoint (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (fromC C) (SSet.stdSimplex.δ (1 : Fin 2)) (postACSystem C hcof hfib) (leftAC C hcof)
      (ResolutionMixedRawEndpoints.AC_zero C hcof hfib)).trans
  exact congrArg (expand C)
    ((left_follow (K C) (F C) (chosen C hcof) (cornerA C) (cornerC C) (cornerD C)
      (edgeAC C) (edgeCD C)).trans
        (congrArg (fun τ => leftAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerD C) τ)
          (edge_commutes C).symm))

lemma AC_one : endpoint C (intervalAC C hcof hfib) 0 = expand C (corner2 C hcof) := by
  apply (NerveProductEndpointTransport.mapTarget_endpoint (parameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (cValues C)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (fromC C) (SSet.stdSimplex.δ (0 : Fin 2)) (postACSystem C hcof hfib) (rightAC C hcof)
      (ResolutionMixedRawEndpoints.AC_one C hcof hfib)).trans
  exact congrArg (expand C)
    (middle_exchange (K C) (F C) (chosen C hcof) (cornerA C) (cornerC C) (cornerD C)
      (edgeAC C) (edgeCD C))

lemma CD_zero : endpoint C (intervalCD C hcof hfib) 1 = expand C (corner2 C hcof) :=
  NerveProductEndpointTransport.restrict_endpoint (parameters C) (cParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (toC C) (SSet.stdSimplex.δ (1 : Fin 2))
    (preCDSystem C hcof hfib) (leftCD C hcof) (ResolutionMixedRawEndpoints.CD_zero C hcof hfib)

lemma CD_one : endpoint C (intervalCD C hcof hfib) 0 = expand C (corner3 C hcof) := by
  apply (NerveProductEndpointTransport.restrict_endpoint (parameters C) (cParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (toC C) (SSet.stdSimplex.δ (0 : Fin 2))
    (preCDSystem C hcof hfib) (rightCD C hcof) (ResolutionMixedRawEndpoints.CD_one C hcof
      hfib)).trans
  exact congrArg (expand C)
    ((right_precede (K C) (F C) (chosen C hcof) (cornerA C) (cornerC C) (cornerD C)
      (edgeAC C) (edgeCD C)).trans
        (congrArg (fun τ => rightAlong (K C) (F C) (chosen C hcof) (cornerA C) (cornerD C) τ)
          (edge_commutes C).symm))

lemma BD_zero : endpoint C (intervalBD C hcof hfib) 1 = expand C (corner1 C hcof) := by
  have hb := NerveProductEndpointTransport.mapTarget_endpoint (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (castFinal C) (SSet.stdSimplex.δ (1 : Fin 2)) (postBDSystem C hcof hfib) (leftBD C hcof)
      (ResolutionMixedRawEndpoints.BD_zero C hcof hfib)
  apply (NerveProductEndpointTransport.restrict_endpoint (parameters C) (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (toB C) (SSet.stdSimplex.δ (1 : Fin 2))
      (castBDSystem C hcof hfib) _ hb).trans
  exact congrArg (fun a => expand C (restrict (parameters C) (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (toB C) a)) (bd_left_finish C hcof) |>.trans
      (congrArg (expand C) (middle_exchange (K C) (F C) (chosen C hcof)
        (cornerA C) (cornerB C) (cornerD C) (edgeAB C) (edgeBD C)).symm)

lemma BD_one : endpoint C (intervalBD C hcof hfib) 0 = expand C (corner3 C hcof) := by
  have hb := NerveProductEndpointTransport.mapTarget_endpoint (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (leftFinalValues C)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (castFinal C) (SSet.stdSimplex.δ (0 : Fin 2)) (postBDSystem C hcof hfib) (rightBD C hcof)
      (ResolutionMixedRawEndpoints.BD_one C hcof hfib)
  apply (NerveProductEndpointTransport.restrict_endpoint (parameters C) (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (toB C) (SSet.stdSimplex.δ (0 : Fin 2))
      (castBDSystem C hcof hfib) _ hb).trans
  exact congrArg (fun a => expand C (restrict (parameters C) (bParameters C)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C)) (toB C) a)) (bd_right_finish C hcof) |>.trans
      (congrArg (expand C) (right_precede (K C) (F C) (chosen C hcof)
        (cornerA C) (cornerB C) (cornerD C) (edgeAB C) (edgeBD C)))

lemma commonA : endpoint C (intervalAB C hcof hfib) 1 = endpoint C (intervalAC C hcof hfib) 1 :=
  (AB_zero C hcof hfib).trans (AC_zero C hcof hfib).symm
lemma commonB : endpoint C (intervalAB C hcof hfib) 0 = endpoint C (intervalBD C hcof hfib) 1 :=
  (AB_one C hcof hfib).trans (BD_zero C hcof hfib).symm
lemma commonC : endpoint C (intervalAC C hcof hfib) 0 = endpoint C (intervalCD C hcof hfib) 1 :=
  (AC_one C hcof hfib).trans (CD_zero C hcof hfib).symm
lemma commonD : endpoint C (intervalBD C hcof hfib) 0 = endpoint C (intervalCD C hcof hfib) 0 :=
  (BD_one C hcof hfib).trans (CD_one C hcof hfib).symm

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility
