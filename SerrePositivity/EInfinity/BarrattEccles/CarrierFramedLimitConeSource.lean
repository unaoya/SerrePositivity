module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitProbe
public import SerrePositivity.EInfinity.BarrattEccles.CarrierRightSimplicialCones
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrameSource

/-!
# 右 frame の錐の始域の射と二変数の関手

概要：BM 命題 4.1・Hovey §5 の右 frame の錐を試験始域に反変にする。
方針：同じ試験始域の関手と frame Hom 族の評価を合成する。
規約：固定した始域での関手は既存の carrierFramedLimitConeSpace と同じもの。
使われ方：両錐比較と局所化 Hom 比較の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右 frame の錐の始域反変・終域図式共変の関手（Hovey §5）。
方針：試験始域の置換と同じ frame Hom 族の反転を合成する。
規約：元の全対象と全射を保持する。
使われ方：局所化へ降ろす導来 Hom の二変数の界面。 -/
def carrierFramedLimitConeBifunctor :
    (Complex A)ᵒᵖ ⥤ (K ⥤ (operad A).Algebra) ⥤ SSet.{u} :=
  (carrierFramedLimitProbeFunctor A).op ⋙
    ((carrierRightFrameDiagramFamily A K).rightOp ⋙ FrameWeightRealization.homFamily Kᵒᵖ).flip ⋙
      (Functor.whiskeringRight (K ⥤ (operad A).Algebra) (Kᵒᵖᵒᵖ ⥤ SSet.{u}) SSet.{u}).obj
        (WeightedCones.coneSpace Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K))

/-- 概要：二変数の関手は既存の同じ右錐を回収する（Hovey §5）。
方針：反転した Hom 族の評価を展開する。
規約：同型ではなく関手の厳密な等式。
使われ方：既存の π₀ 比較と始域の射の照合。 -/
lemma carrierFramedLimitConeBifunctor_obj (Y : Complex A) :
    (carrierFramedLimitConeBifunctor A K).obj (op Y) = carrierFramedLimitConeSpace A K Y := rfl

/-- 概要：元の始域の射は右 frame の錐の前合成を与える（Hovey §5）。
方針：同じ二変数の関手を反対射で評価する。
規約：終域図式のすべての射に自然。
使われ方：錐の π₀ の始域写像。 -/
abbrev carrierFramedLimitConeSourceMap {Y Z : Complex A} (f : Y ⟶ Z) :
    carrierFramedLimitConeSpace A K Z ⟶ carrierFramedLimitConeSpace A K Y :=
  (carrierFramedLimitConeBifunctor A K).map f.op

/-- 概要：右錐の始域写像は同じ試験始域の前合成（Hovey §5）。
方針：反対圏での frame Hom の評価の射を展開する。
規約：試験始域の射は具体的な置換関手の同じ射。
使われ方：反対圏の π₀ 比較の自然性への代入。 -/
lemma carrierFramedLimitConeSourceMap_app {Y Z : Complex A} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) :
    (carrierFramedLimitConeSourceMap A K f).app F =
      (WeightedCones.coneSpace Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).map
        ((FrameWeightRealization.hom Kᵒᵖ (carrierRightFrameDiagram A K F)).map
          ((carrierFramedLimitProbeFunctor A).map f).op) := rfl

/-- 概要：元の添字での右 Hom の始域の前合成（Hovey §5）。
方針：同じ試験始域の射を元の右 Hom のすべての値へ前合成する。
規約：反対射表示へ移す前の同じ射。
使われ方：混合 Hom の右図式比較の可換四角形。 -/
abbrev carrierRightSimplicialHomSourceMap {Y Z : Complex A} (f : Y ⟶ Z)
    (F : K ⥤ (operad A).Algebra) :
    carrierRightSimplicialHomDiagram A K Z F ⟶ carrierRightSimplicialHomDiagram A K Y F :=
  Functor.whiskerLeft (F ⋙ carrierRightSimplicialFrameFamily A)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightSourceMap ((carrierFramedLimitProbeFunctor A).map f))

end SerrePositivity.EInfinity.BarrattEccles
