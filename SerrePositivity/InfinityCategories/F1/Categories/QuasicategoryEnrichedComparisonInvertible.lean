module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedComparisonArrowValue
public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramArrowFamilyEdge
public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Core.EquivalencePathInternalHom

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
namespace SerrePositivity.InfinityCategories

/-- 同じ一単体の端点表示の変更は可逆性を保つ。 -/
lemma isInvertibleEdge_ofEq {Y : SSet.{u}} {x y x' y' : Y _⦋0⦌}
    (e : Edge x y) (hx : x = x') (hy : y = y')
    (he : IsInvertibleEdge e.toTruncated) :
    IsInvertibleEdge (e.ofEq hx hy).toTruncated :=
  (isInvertibleEdge_congr (e := (e.ofEq hx hy).toTruncated)
    (f := e.toTruncated) rfl).mpr he

local instance quasicategoryComparisonInvertible_sourceCore_simplicialCategory
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

/-- 成分が同値な元の比較の、同じ全局所 Hom にわたる区間族の辺は可逆。 -/
lemma QuasicategoryEnrichedDiagramComparison.interval_isInvertible
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : QuasicategoryEnrichedDiagram C J}
    (η : QuasicategoryEnrichedDiagramComparison D E)
    (hη : ∀ j X, IsQCatEquivalence ((η.app j).val X)) :
    IsInvertibleEdge (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
      (transposeFunctorFamily
        (η.arrowDiagram.realization ≫ qCatDiagramArrowCurry J))).toTruncated) := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt_any
    (K := SimplicialNerve (TransportEnrichment quasicategoryCoreFunctor.{u} C))
    (X := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
    (((SSet.Edge.ofTruncated homotopyIntervalEdge).map
      (transposeFunctorFamily
        (η.arrowDiagram.realization ≫ qCatDiagramArrowCurry J))).toTruncated)).mpr
  intro s
  rw [← coherentNerveVertex_object s]
  let X := coherentNerveObject s
  let θ := quasicategoryDiagramQCatTransformation
    (F := D.toCoreEnrichedFunctor.obj X) (G := E.toCoreEnrichedFunctor.obj X)
    (Functor.whiskerRight (η.evaluate X) quasicategoryObjectForget)
  have h := qCatDiagramArrowFamily_edgeAt η.arrowDiagram.realization
    (coherentNerveVertex X) θ (η.realization_vertex X)
  apply (isInvertibleEdge_congr h).mpr
  exact qCatDiagramNaturalTransformationEdge_isInvertible θ (fun j ↦ hη j X)

end SerrePositivity.InfinityCategories
