module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramFrame

/-!
# 始域 frame の重み付き錐の二変数の関手

概要：BM 命題 4.1・Hovey §5 の始域 frame の錐を元の始域複体に反変にする。
方針：同じ frame 族の Hom と各値の後合成、錐関手を合成する。
規約：既存の constantDiagramSourceHom を各対象で厳密に保持する。
使われ方：両錐比較と元の定値図式からの Hom 比較の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram

open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：始域 frame の錐の二変数の関手（Hovey §5）。
方針：同じ関手的 frame の cosimplicial Hom を重み付き錐へ送る。
規約：元の始域に反変、終域図式に共変。
使われ方：元の始域のすべての射の前合成。 -/
def constantDiagramSourceBifunctor :
    (Complex A)ᵒᵖ ⥤ (K ⥤ (Complex A)) ⥤ SSet.{u} := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact (cosimplicialResolutionFamily (carrierProbeFactorization A)).obj.op ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ Functor.whiskeringRight K (Complex A) SSet.{u} ⋙
      (Functor.whiskeringRight (K ⥤ (Complex A)) (K ⥤ SSet.{u}) SSet.{u}).obj
        (WeightedCones.coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K))

/-- 概要：二変数の関手は既存の始域錐の関手（Hovey §5）。
方針：同じ frame 族での評価を展開する。
規約：既存の同じ単体集合と図式射を保持する。
使われ方：既存の π₀ 比較へ前合成を供給する。 -/
lemma constantDiagramSourceBifunctor_obj (Y : (Complex A)) :
    (constantDiagramSourceBifunctor A K).obj (op Y) = constantDiagramSourceHom A K Y := rfl

/-- 概要：元の始域の射は始域 frame の錐の前合成を与える（Hovey §5）。
方針：同じ二変数の関手を反対射で評価する。
規約：終域図式のすべての射に自然。
使われ方：元の定値図式からの Hom の前合成との比較。 -/
abbrev constantDiagramSourceMap {Y Z : (Complex A)} (f : Y ⟶ Z) :
    constantDiagramSourceHom A K Z ⟶ constantDiagramSourceHom A K Y :=
  (constantDiagramSourceBifunctor A K).map f.op

/-- 概要：始域錐の前合成は同じ frame 射の Hom の錐（Hovey §5）。
方針：後合成関手と錐関手の自然変換を評価する。
規約：frame の射は元の関手的分解の同じ射。
使われ方：混合 Hom の左比較の可換四角形。 -/
lemma constantDiagramSourceMap_app {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    (constantDiagramSourceMap A K f).app F =
      (WeightedCones.coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).map
        (Functor.whiskerLeft F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap
          ((cosimplicialResolutionFamily (carrierProbeFactorization A)).obj.map f))) := rfl

end SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram
