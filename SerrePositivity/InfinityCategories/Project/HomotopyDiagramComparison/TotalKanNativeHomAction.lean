module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedValueTransportNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LeftHomEdgeTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TotalKanMapCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentCoconeTransportAction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCoconeValuePre

/-!
概要：元の余極限 Kan 射の coherent 辺を、元の余錐の左 Hom の指定点として追跡する。
方針：値比較の輸送自然性と、元の全空間余錐の単位比較を同じ辺で合成する。
規約：元の余錐と辺を保持。使われ方：native 余錐輸送と Kan 射の単位表現の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (a : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G)

/-- 元の Kan 射の coherent 辺を、元の余極限余錐の頂点を始点として表示する。 -/
def totalKanNativeEdge :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F).vertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex G) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedRightMorphismEdge (K := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
    (L := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G) a).ofEq
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone_vertex F).symm rfl

/-- 同じ元の coherent 辺を、元の余錐の左 Hom の点として表示する。 -/
def totalKanNativeHomPoint :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F).vertex
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex G)) _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint (totalKanNativeEdge F G a)

/-- 元の辺の fiber 輸送は、元の余錐の頂点の値比較を介して同じ Kan 射に整合する。 -/
def totalKanNativeEdge_valueIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalSourceValueMap F ≫ (SSet.uliftFunctor.{u + 1, u}).map a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (totalKanNativeEdge F G a) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex G)).hom) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedValue_transportIso (K := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject F)
    (L := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject G) a).precomp
      (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone_vertex F)))
  rw [totalKanNativeEdge, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeTransport_changeSource]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalSourceValueMap, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan, Category.assoc] using e

/-- 元の左 Hom の指定点での全余錐作用は、同じ Kan 射の元の単位表現と同型。 -/
def totalKanNativeHomActionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentCoconeTransportAction F (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint F G a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeInput F G a))) := by
  let c := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F
  let z := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalVertex G
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberMap c
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (totalKanNativeEdge F G a)
  let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence z).hom
  let k := (pre f).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection z) ≫
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F)).map v
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedLeftHomEdgeTransportIso (totalKanNativeEdge F G a)).map k
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentCoconeTransportAction F c z).app _ (totalKanNativeHomPoint F G a))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ t ≫ v)) at h
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (totalKanNativeEdge_valueIso F G a).symm f
  have d := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentLargeTotalCoconeUnitIso F).postcomp
    ((SSet.uliftFunctor.{u + 1, u}).map a)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ t ≫ v)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeInput F G a)) := by
    simpa only [c, f, t, v, z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalSourceValueMap,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentLargeTotalUnit, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeInput,
      Functor.map_comp, Category.assoc, eqToHom_refl, Category.comp_id] using e ≪≫ d
  exact h ≪≫ he

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
