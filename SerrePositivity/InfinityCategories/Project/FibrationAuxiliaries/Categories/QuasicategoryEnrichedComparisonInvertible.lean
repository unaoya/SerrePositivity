module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparisonArrowValue
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramArrowFamilyEdge
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom

/-!
概要：成分が同値な全局所 Hom の豊穣比較を、同じ区間族の可逆辺として実現する。
方針：底全体の頂点公式を使い、元の自然変換の可逆性を点ごとに判定する。
規約：全高次の同じ区間族を保持する。
使われ方：全局所比較の可逆 path への持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ一単体の端点表示の変更は可逆性を保つ。 -/
lemma isInvertibleEdge_ofEq {Y : SSet.{u}} {x y x' y' : Y _⦋0⦌}
    (e : Edge x y) (hx : x = x') (hy : y = y')
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.ofEq hx hy).toTruncated :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (e.ofEq hx hy).toTruncated)
    (f := e.toTruncated) rfl).mpr he

local instance quasicategoryComparisonInvertible_sourceCore_simplicialCategory
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 成分が同値な元の比較の、同じ全局所 Hom にわたる区間族の辺は可逆。 -/
lemma QuasicategoryEnrichedDiagramComparison.interval_isInvertible
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagramComparison D E)
    (hη : ∀ j X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((η.app j).val X)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily
        (η.arrowDiagram.realization ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry J))).toTruncated) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_evaluateFunctorAt_any
    (K := SimplicialNerve (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C))
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
    (((SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily
        (η.arrowDiagram.realization ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowCurry J))).toTruncated)).mpr
  intro s
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object s]
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject s
  let θ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramQCatTransformation
    (F := D.toCoreEnrichedFunctor.obj X) (G := E.toCoreEnrichedFunctor.obj X)
    (Functor.whiskerRight (η.evaluate X) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)
  have h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrowFamily_edgeAt η.arrowDiagram.realization
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) θ (η.realization_vertex X)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr h).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramNaturalTransformationEdge_isInvertible θ (fun j ↦ hη j X)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
