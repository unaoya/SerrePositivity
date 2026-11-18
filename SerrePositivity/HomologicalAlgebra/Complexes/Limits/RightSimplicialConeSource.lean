module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitConeSource

/-!
# 右 frame の錐の添字移送と始域の前合成

概要：Hovey §5.4 の二つの右錐表示の同型は元の始域の射にも自然。
方針：同じ反対射の可換四角形と添字移送関手同型の自然性を合成する。
規約：既存の試験始域と同じ錐の射を使う。
使われ方：両 frame の具体的な錐比較の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右 Hom の二つの表示は始域の前合成に自然（Hovey §5）。
方針：各次元の元の合成を同じ反対射へ写す。
規約：元の図式と右 frame を固定した同じ四角形。
使われ方：錐関手へ移す前の反対射表示の自然性。 -/
lemma rightSimplicialHomDiagramIso_source {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).map (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomSourceMap A K f F) ≫
        (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagramIso A K Y F).hom =
      (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagramIso A K Z F).hom ≫
        (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).map
          ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).map f).op := by
  ext k n h
  rfl

/-- 概要：右錐の添字移送同型は元の始域の射に自然（Hovey §5.4）。
方針：添字移送の逆の自然性と同じ反対射の可換四角形を合成する。
規約：右辺は既存の framedLimitConeSpace の同じ前合成。
使われ方：混合 Hom から具体的な右錐へ始域自然性を移す。 -/
lemma rightSimplicialConeIso_source {Y Z : (Complex A)} (f : Y ⟶ Z)
    (F : K ⥤ (Complex A)) :
    (WeightedCones.coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).map
        (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomSourceMap A K f F) ≫ (_root_.SerrePositivity.ComplexLimits.rightSimplicialConeIso A K Y F).hom =
      (_root_.SerrePositivity.ComplexLimits.rightSimplicialConeIso A K Z F).hom ≫ (_root_.SerrePositivity.ComplexLimits.framedLimitConeSourceMap A K f).app F := by
  let T := WeightedCones.coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
  let D := WeightedCones.coneSpace Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso (opOpEquivalence K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
  let m := _root_.SerrePositivity.ComplexLimits.rightSimplicialHomSourceMap A K f F
  let d := (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).map
    ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).map f).op
  have hn : T.map m ≫ (e.app (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagram A K Y F)).inv =
      (e.app (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagram A K Z F)).inv ≫ D.map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).map m) :=
    e.inv.naturality m
  have hm : D.map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).map m) ≫
        D.map (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagramIso A K Y F).hom =
      D.map (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagramIso A K Z F).hom ≫ D.map d := by
    rw [← D.map_comp, _root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagramIso_source, D.map_comp]
  change T.map m ≫ ((e.app (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagram A K Y F)).inv ≫
      D.map (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagramIso A K Y F).hom) =
    ((e.app (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagram A K Z F)).inv ≫
      D.map (_root_.SerrePositivity.ComplexLimits.rightSimplicialHomDiagramIso A K Z F).hom) ≫ D.map d
  rw [← Category.assoc, hn, Category.assoc, hm, ← Category.assoc]

end SerrePositivity.ComplexLimits
