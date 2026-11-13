module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentConstantCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalMapCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentTransformationTotalMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentTransformationUnitTriangle
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.ConstantCoconeHomotopyComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTransformationUnitCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductNativeLegs
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.FiniteCoherentProjection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.TotalKanMapCocone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.TotalKanNativeCoconeComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.TotalKanNativeHomAction

/-!
概要：元の有限 native 積の各脚の全余錐作用を、元の反復射影変換と単位へ比較する。
方針：同じ脚の Kan ホモトピー・相対合成比較・元の単位表現を続ける。
規約：元の脚の全一単体・全余錐・指定三角形を保持する。
使われ方：P_Σ の sifted 余極限閉性へ有限 coherent 積比較を適用する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (n : ℕ) {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (i : Discrete (ULift.{u} (Fin (n + 1))))

/-- 元の全空間射影の余錐は、反復 coherent 射影と元の単位の同じ合成余錐と同型。 -/
def finiteCoherentProjectionCoconeIso
    (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.as.down)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i.as.down)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)
        (F i.as.down) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n F i.as.down))
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i.as.down)) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone_vertex _ _ _))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.as.down) T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i.as.down))
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantCoconeHomotopyIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i.as.down))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionUnitIso n F i.as.down).simplicialHomotopy).symm ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCoconeIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.as.down) T).symm

/-- 余錐作用で使う辺は、元の native 有限積錐の同じ脚の全一単体。 -/
lemma finiteSiftedCoherentProductNativeEdge :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeKanLeg n F i)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone n F)
          (ULift.up (ComposableArrows.mk₀ i))).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg_edge _ _ _ _

/-- 元の native 脚の全余錐作用は、反復射影と指定単位の同じ三角形の余錐に同型。 -/
def finiteSiftedCoherentProductNativeCoconeIso
    (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.as.down)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i.as.down)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F))
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i.as.down))).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeKanLeg n F i)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex n F i.as.down) T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i.as.down))
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitCocone_vertex _ _ _ T)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeCoconeIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeKanLeg n F i) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) (F i.as.down)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n F i.as.down)
        (Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeKanLeg_projection n F i)) ≪≫
          finiteCoherentProjectionCoconeIso n F i T

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
