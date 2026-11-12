module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitSpanBoundaryPath
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointTransportNaturalityComposition

/-!
概要：元の指定境界同型を、左右の境界・付加輸送と native な中央比較の三因子で表示する。
方針：同じ一点図式の結合順序を揃え、元の定義の逆同型を回収する。
規約：指定境界同型を新しい比較で置き換えない。使われ方：共通根辺上の四因子の相殺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C : SSet.{u + 1}} {p : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
local notation "v" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl
local notation "eB" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc i F hi dB j G hj dC
local notation "eC" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc i F hi dB j G hj dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)
local notation "KB" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso i F hi dB eB
local notation "KC" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso j G hj dC eC
local notation "JB" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTransportPointIso c hc i F hi dB
local notation "JC" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTransportPointIso c hc j G hj dC

/-- 左付加輸送を、元の二段階輸送と同じ結合順序で表示する。 -/
def partialColimitSpanLeftAttachmentBoundaryFactor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex i F hi dB) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eB)
      (SSet.yonedaEquiv.symm v ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi dB) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eB)) := by
  simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp JB (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eB)

/-- 右付加輸送も、元の二段階輸送と同じ結合順序で表示する。 -/
def partialColimitSpanRightAttachmentBoundaryFactor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex j G hj dC) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eC)
      (SSet.yonedaEquiv.symm v ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc j G hj dC) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eC)) := by
  simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp JC (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eC)

/-- 左の境界自然性と付加辺輸送の同じ合成。 -/
def partialColimitSpanLeftBoundaryFactor :=
  (KB) ≪≫ partialColimitSpanLeftAttachmentBoundaryFactor c hc i F hi dB j G hj dC

/-- 右の境界自然性と付加辺輸送の同じ合成。 -/
def partialColimitSpanRightBoundaryFactor :=
  (KC) ≪≫ partialColimitSpanRightAttachmentBoundaryFactor c hc i F hi dB j G hj dC

/-- 元の native な二単体の合成比較を、元の始点の一点で制限する。 -/
def partialColimitSpanMiddleBoundaryFactor :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportIso c hc i F hi dB j G hj dC q)
    (SSet.yonedaEquiv.symm v)

/-- 元の境界同型は、同じ左右・中央の三因子の積の逆そのもの。 -/
lemma partialColimitSpanBoundaryIso_factors :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanBoundaryIso c hc i F hi dB j G hj dC =
      (partialColimitSpanLeftBoundaryFactor c hc i F hi dB j G hj dC ≪≫
        partialColimitSpanMiddleBoundaryFactor c hc i F hi dB j G hj dC ≪≫
        (partialColimitSpanRightBoundaryFactor c hc i F hi dB j G hj dC).symm).symm := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanBoundaryIso, partialColimitSpanLeftBoundaryFactor,
    partialColimitSpanMiddleBoundaryFactor, partialColimitSpanRightBoundaryFactor,
    partialColimitSpanLeftAttachmentBoundaryFactor, partialColimitSpanRightAttachmentBoundaryFactor]
  simp only [Iso.trans_symm, Iso.trans_assoc]

/-- 左因子の射は、既存の結合表示の同じ射である。 -/
lemma partialColimitSpanLeftBoundaryFactor_hom_arrow :
    Arrow.mk (partialColimitSpanLeftBoundaryFactor c hc i F hi dB j G hj dC).hom =
      Arrow.mk ((KB) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp JB (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eB)).hom := by
  dsimp only [partialColimitSpanLeftBoundaryFactor, partialColimitSpanLeftAttachmentBoundaryFactor]
  rfl

/-- 右因子の射も、既存の結合表示の同じ射である。 -/
lemma partialColimitSpanRightBoundaryFactor_hom_arrow :
    Arrow.mk (partialColimitSpanRightBoundaryFactor c hc i F hi dB j G hj dC).hom =
      Arrow.mk ((KC) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp JC (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eC)).hom := by
  dsimp only [partialColimitSpanRightBoundaryFactor,
    partialColimitSpanRightAttachmentBoundaryFactor]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
