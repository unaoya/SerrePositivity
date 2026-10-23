module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedValueTransportNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftHomEdgeTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanMapCocone
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCoconeTransportAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalCoconeValuePre

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (a : F2.coherentDiagramTotalKan F ⟶ F2.coherentDiagramTotalKan G)

/-- 元の Kan 射の coherent 辺を、元の余極限余錐の頂点を始点として表示する。 -/
def totalKanNativeEdge :
    SSet.Edge (F2.coherentDiagramTotalCocone F).vertex (F2.coherentDiagramTotalVertex G) :=
  (pointedRightMorphismEdge (K := F2.coherentDiagramTotalKanObject F)
    (L := F2.coherentDiagramTotalKanObject G) a).ofEq
      (F2.coherentDiagramTotalCocone_vertex F).symm rfl

/-- 同じ元の coherent 辺を、元の余錐の左 Hom の点として表示する。 -/
def totalKanNativeHomPoint :
    (pinchedHomLeft (F2.coherentDiagramTotalCocone F).vertex
      (F2.coherentDiagramTotalVertex G)) _⦋0⦌ := leftHomEdgePoint (totalKanNativeEdge F G a)

/-- 元の辺の fiber 輸送は、元の余錐の頂点の値比較を介して同じ Kan 射に整合する。 -/
def totalKanNativeEdge_valueIso :
    FunctorIso
      (F2.coherentTotalSourceValueMap F ≫ (SSet.uliftFunctor.{u + 1, u}).map a)
      (edgeTransport pointedSpaceProjection (totalKanNativeEdge F G a) ≫
        (pointedSpaceFiberValueEquivalence (F2.coherentDiagramTotalVertex G)).hom) := by
  have e := (pointedValue_transportIso (K := F2.coherentDiagramTotalKanObject F)
    (L := F2.coherentDiagramTotalKanObject G) a).precomp
      (eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (F2.coherentDiagramTotalCocone_vertex F)))
  rw [totalKanNativeEdge, edgeTransport_changeSource]
  simpa only [F2.coherentTotalSourceValueMap, F2.coherentDiagramTotalVertex,
    F2.coherentDiagramTotalKanObject, F2.coherentDiagramTotalKan, Category.assoc] using e

/-- 元の左 Hom の指定点での全余錐作用は、同じ Kan 射の元の単位表現と同型。 -/
def totalKanNativeHomActionIso :
    VertexIso
      ((F2.coherentCoconeTransportAction F (F2.coherentDiagramTotalCocone F)
        (F2.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint F G a))
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (totalKanMapCoconeInput F G a))) := by
  let c := F2.coherentDiagramTotalCocone F
  let z := F2.coherentDiagramTotalVertex G
  let f := F2.coconeFiberMap c
  let t := edgeTransport pointedSpaceProjection (totalKanNativeEdge F G a)
  let v := (pointedSpaceFiberValueEquivalence z).hom
  let k := (pre f).app (vertexFiber pointedSpaceProjection z) ≫
    (ihom (leftUnstraightening F)).map v
  have h := (pointedLeftHomEdgeTransportIso (totalKanNativeEdge F G a)).map k
  change VertexIso
    ((F2.coherentCoconeTransportAction F c z).app _ (totalKanNativeHomPoint F G a))
    (functorVertex (f ≫ t ≫ v)) at h
  have e := FunctorIso.precomp (totalKanNativeEdge_valueIso F G a).symm f
  have d := (F2.coherentLargeTotalCoconeUnitIso F).postcomp
    ((SSet.uliftFunctor.{u + 1, u}).map a)
  have he : FunctorIso (f ≫ t ≫ v)
      ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (totalKanMapCoconeInput F G a)) := by
    simpa only [c, f, t, v, z, F2.coconeFiberValueMapAt, F2.coherentTotalSourceValueMap,
      F2.coherentLargeTotalUnit, F2.coherentDiagramTotalUnit, totalKanMapCoconeInput,
      Functor.map_comp, Category.assoc, eqToHom_refl, Category.comp_id] using e ≪≫ d
  exact h ≪≫ he

end SerrePositivity.InfinityCategories.HomotopyLimits
