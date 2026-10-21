module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramTriangleLaterFaces
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramReindexRealization

/-!
概要：元の豊穣比較三角形を関手空間内へ curry し、同じ全ての比較辺を回収する。
方針：同じ三点図式の共同実現と、面に厳密に自然な単体 curry を合成する。
規約：元の全 fibration と全高次 Hom を同じ族として保持する。
使われ方：元の Hom 比較 span の合成を同じ三角形で比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] {D E F : QuasicategoryEnrichedDiagram C J}
  (η : QuasicategoryEnrichedDiagramComparison D E) (θ : QuasicategoryEnrichedDiagramComparison E F)

/-- 同じ元の豊穣三角形を、関手空間内の二単体の全対象・全高次の族にする。 -/
def quasicategoryEnrichedDiagramTriangleCurry :
    SimplicialNerve (TransportEnrichment quasicategoryCoreFunctor.{u} C) ⟶
      (ihom (Δ[2] : SSet.{u + 1})).obj
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J))) :=
  (quasicategoryEnrichedDiagramTriangle η θ).realization ≫ qCatDiagramSimplexCurry 2 J

/-- 同じ二単体族の最初の面は、元の最初の比較の同じ区間族。 -/
lemma quasicategoryEnrichedDiagramTriangleCurry_first :
    quasicategoryEnrichedDiagramTriangleCurry η θ ≫
      (pre (stdSimplex.δ (2 : Fin 3))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J))) =
      η.arrowDiagram.realization ≫ qCatDiagramArrowCurry J := by
  rw [quasicategoryEnrichedDiagramTriangleCurry, Category.assoc,
    qCatDiagramSimplexCurry_face 1 J (2 : Fin 3), ← Category.assoc,
    QuasicategoryEnrichedDiagram.realization_reindex,
    quasicategoryEnrichedDiagramTriangle_face_first, qCatDiagramSimplexCurry_one]

/-- 同じ二単体族の次の面は、元の次の比較の同じ区間族。 -/
lemma quasicategoryEnrichedDiagramTriangleCurry_second :
    quasicategoryEnrichedDiagramTriangleCurry η θ ≫
      (pre (stdSimplex.δ (0 : Fin 3))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J))) =
      θ.arrowDiagram.realization ≫ qCatDiagramArrowCurry J := by
  rw [quasicategoryEnrichedDiagramTriangleCurry, Category.assoc,
    qCatDiagramSimplexCurry_face 1 J (0 : Fin 3), ← Category.assoc,
    QuasicategoryEnrichedDiagram.realization_reindex,
    quasicategoryEnrichedDiagramTriangle_face_second, qCatDiagramSimplexCurry_one]

/-- 同じ二単体族の長辺の面は、元の合成比較の同じ区間族。 -/
lemma quasicategoryEnrichedDiagramTriangleCurry_long :
    quasicategoryEnrichedDiagramTriangleCurry η θ ≫
      (pre (stdSimplex.δ (1 : Fin 3))).app
        (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J))) =
      (η.trans θ).arrowDiagram.realization ≫ qCatDiagramArrowCurry J := by
  rw [quasicategoryEnrichedDiagramTriangleCurry, Category.assoc,
    qCatDiagramSimplexCurry_face 1 J (1 : Fin 3), ← Category.assoc,
    QuasicategoryEnrichedDiagram.realization_reindex,
    quasicategoryEnrichedDiagramTriangle_face_long, qCatDiagramSimplexCurry_one]

end SerrePositivity.InfinityCategories
