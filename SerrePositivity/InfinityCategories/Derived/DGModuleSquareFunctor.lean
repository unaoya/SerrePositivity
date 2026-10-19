module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleFunctor

/-! # dg 加群四角形の実関手像

概要：dg 関手は四辺・対角・二つの全 Hom end 成分を持つ実四角形を送る。
方針：各三角形で全成分の一致を使い、正方形の二セル表示で貼る。
規約：native nerve の写像では対象宇宙を共通にする。使われ方：cone の実関手像の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D} (s : DGModuleSquareData A D W X Y Z)

/-- 全 Hom end の成分を同時に送った実加群四角形データ。 -/
def map {E : Type w} [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A (RightModule A D) (RightModule A E)) :
    DGModuleSquareData A E (F.onClosed.obj W) (F.onClosed.obj X)
      (F.onClosed.obj Y) (F.onClosed.obj Z) where
  bottom := F.onClosed.map s.bottom
  left := F.onClosed.map s.left
  right := F.onClosed.map s.right
  top := F.onClosed.map s.top
  diagonal := F.onClosed.map s.diagonal
  lowerHomotopy := (F.map (ForgetEnrichment.to (Complex A) W)
    (ForgetEnrichment.to (Complex A) Z)).f (-1) s.lowerHomotopy
  upperHomotopy := (F.map (ForgetEnrichment.to (Complex A) W)
    (ForgetEnrichment.to (Complex A) Z)).f (-1) s.upperHomotopy
  lowerEquation := dgModuleTriangle_map_differential A D E F _ _ _ _ s.lowerEquation
  upperEquation := dgModuleTriangle_map_differential A D E F _ _ _ _ s.upperEquation

/-- 下側の実二単体は同じ関手による像。 -/
lemma map_lowerTriangle {E : Type w} [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A (RightModule A D) (RightModule A E)) :
    s.lowerTriangle.map F = (s.map F).lowerTriangle :=
  dgModuleCompStruct_map A D E F _ _ _ _ s.lowerEquation

/-- 上側の実二単体も同じ関手による像。 -/
lemma map_upperTriangle {E : Type w} [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A (RightModule A D) (RightModule A E)) :
    s.upperTriangle.map F = (s.map F).upperTriangle :=
  dgModuleCompStruct_map A D E F _ _ _ _ s.upperEquation

/-- 全四角形の実写像は dg nerve の native な後合成と一致する。 -/
lemma map_square {E : Type v} [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A (RightModule A D) (RightModule A E)) :
    (s.map F).square = s.square ≫ dgNerve.map F := by
  apply square_isPushout.hom_ext
  · rw [square_upper, ← Category.assoc, square_upper, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (s.map_upperTriangle F).symm
  · rw [square_lower, ← Category.assoc, square_lower, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (s.map_lowerTriangle F).symm

end SerrePositivity.InfinityCategories.DGModuleSquareData
