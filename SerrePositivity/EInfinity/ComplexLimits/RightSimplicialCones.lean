module

public import SerrePositivity.EInfinity.ComplexLimits.RightSimplicialFrames
public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitCones
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameDiagrams
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeReindex

/-!
# 右 frame の錐の元の添字と二重反対圏表示の同型

概要：Hovey §5.4 の実際の右 frame の錐を元の添字上の Hom の錐と同定する。
方針：同じ射の反対化と添字同値による錐関手の自然同型を合成する。
規約：元の試験始域・右 frame・一点重みを保持する。
使われ方：混合 Hom の比較を具体的な framedLimitConeSpace へ代入する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右 frame への Hom を元の図式添字で表示する（Hovey §5）。
方針：単体的右 frame の関手族に同じ試験始域からの Hom を適用する。
規約：元の図式射に自然で、新しい試験始域を選ばない。
使われ方：混合 Hom の右側の具体的な図式。 -/
abbrev rightSimplicialHomDiagram (Y : (Complex A))
    (F : K ⥤ (Complex A)) : K ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram K (framedLimitProbe A Y) (F ⋙ rightSimplicialFrameFamily A)

/-- 概要：右 Hom 図式を元の図式の関手として束ねる（Hovey §5）。
方針：右 frame と同じ始域からの Hom を後合成する。
規約：既存の各値の表示と定義上同じ。
使われ方：錐比較の終域自然性。 -/
abbrev rightSimplicialHomFamily (Y : (Complex A)) :
    (K ⥤ (Complex A)) ⥤ K ⥤ SSet.{u} :=
  (Functor.whiskeringRight K (Complex A) SSet.{u}).obj
    (rightSimplicialFrameFamily A ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomFunctor (framedLimitProbe A Y))

/-- 概要：反対射で表示した右 Hom 図式の関手（Hovey §5）。
方針：既存の右 frame 図式の Hom 族を同じ試験始域で評価する。
規約：framedLimitConeSpace の同じ係数関手。
使われ方：図式の射に自然な二重反対圏表示。 -/
abbrev rightFrameHomDiagramFamily (Y : (Complex A)) :
    (K ⥤ (Complex A)) ⥤ Kᵒᵖᵒᵖ ⥤ SSet.{u} :=
  (rightFrameDiagramFamily A K).rightOp ⋙ FrameWeightRealization.homFamily Kᵒᵖ ⋙
    (CategoryTheory.evaluation (Complex A)ᵒᵖ (Kᵒᵖᵒᵖ ⥤ SSet.{u})).obj
      (op (framedLimitProbe A Y))

/-- 概要：右 Hom 図式の反対射表示との同型（Hovey §5）。
方針：各次元の元の射を反対化する。
規約：すべての添字と単体作用素に自然。
使われ方：二重反対圏表示の同じ錐関手を回収する。 -/
def rightSimplicialHomDiagramIso (Y : (Complex A))
    (F : K ⥤ (Complex A)) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj (rightSimplicialHomDiagram A K Y F) ≅
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj
        (op (framedLimitProbe A Y)) :=
  NatIso.ofComponents (fun k =>
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomIso (framedLimitProbe A Y)
      ((rightSimplicialFrameFamily A).obj (F.obj k.unop.unop))) (by
    intro k l f
    ext n h
    rfl)

/-- 概要：右 Hom の二つの表示は元の図式に自然に同型（Hovey §5）。
方針：各値の同じ反対化同型を束ねる。
規約：元の図式の任意の射を保持する。
使われ方：具体的な錐の同型の自然性。 -/
def rightSimplicialHomComparisonIso (Y : (Complex A)) :
    rightSimplicialHomFamily A K Y ⋙ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K ≅ rightFrameHomDiagramFamily A K Y :=
  NatIso.ofComponents (rightSimplicialHomDiagramIso A K Y) (by
    intro F G f
    ext k n h
    rfl)

/-- 概要：元の添字と反対圏表示の右錐関手は自然に同型（Hovey §5.4）。
方針：添字移送と右 Hom の同じ反対化同型を合成する。
規約：終域図式のすべての射に自然。
使われ方：導来 Hom 比較を終域に自然な同値にする。 -/
def rightSimplicialConeComparisonIso (Y : (Complex A)) :
    rightSimplicialHomFamily A K Y ⋙
        WeightedCones.coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) ≅ framedLimitConeSpace A K Y :=
  Functor.isoWhiskerLeft (rightSimplicialHomFamily A K Y)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexIso (opOpEquivalence K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightSimplicialHomComparisonIso A K Y)
      (WeightedCones.coneSpace Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K))

/-- 概要：元の添字上の右 Hom の錐は実際の右 frame 錐空間（Hovey §5.4）。
方針：自然な錐関手の同型を元の図式で評価する。
規約：構成済みの framedLimitConeSpace の同じ単体集合と比較する。
使われ方：始域 frame との比較を実際の極限の錐へ移す。 -/
def rightSimplicialConeIso (Y : (Complex A)) (F : K ⥤ (Complex A)) :
    (WeightedCones.coneSpace K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)).obj
        (rightSimplicialHomDiagram A K Y F) ≅ (framedLimitConeSpace A K Y).obj F :=
  (rightSimplicialConeComparisonIso A K Y).app F

end SerrePositivity.EInfinity.ComplexLimits
