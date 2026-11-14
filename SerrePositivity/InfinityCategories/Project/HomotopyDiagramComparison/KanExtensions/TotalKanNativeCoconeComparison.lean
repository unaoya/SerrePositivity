module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.TotalKanNativeHomAction

/-!
概要：元の Kan 射の coherent 辺による native 余錐作用は、元の単位表現の余錐と同型。
方針：同じ左 Hom の点で全輸送比較を評価し、元の標準余錐比較の充満忠実性で反映する。
規約：元の余極限余錐・辺・単位を保持。使われ方：sifted 積の脚の全余錐の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (a : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G)

/-- 同じ元の coherent 辺の native な余錐作用と、同じ Kan 射の単位表現の全余錐は同型。 -/
def totalKanNativeCoconeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone F G a) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone_vertex F G a)) := by
  let c := _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F
  let z := _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone F G a) z (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone_vertex F G a)
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentCoconeTotalComparison F z ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallUnstraighteningHomIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj).inv
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence D :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentCoconeTotalComparison_isQCatEquivalence F z).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallUnstraighteningHomIso F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj).symm).isQCatEquivalence)
  apply hd.isFullyFaithful.preimageVertexIso
  have h := ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentCoconeTransportActionIso F c z).app (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G a)) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomActionIso F G a
  have hq : D.app (Opposite.op ⦋0⦌) q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone F G a) z
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone_vertex F G a)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt_smallComparison F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone F G a) z
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCocone_vertex F G a)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (D.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily c z).app _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint F G a)))
    (D.app _ q)
  rw [hq]
  exact h ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCoconeFiberIso F z (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeInput F G a)).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
