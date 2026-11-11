module
public import SerrePositivity.KST.SConstruction.StableBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.StableMultiRealizationHomotopy
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 完全関手同型と元の境界商の基点固定成分
概要：完全関手の関手同型から、同じ境界商射の点つき成分等号を得る。
方針：完全関手 core の実際の辺を、全零境界を保つ豊穣作用で写す。
規約：基点を忘れたホモトピーで代用しない。使われ方：実 Perf 評価の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 全 Hom 作用の通常射の頂点は、元の同じ境界商射の点つき頂点。 -/
lemma stableBoundaryPointedEnrichedFunctor_vertex (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    ((stableBoundaryPointedEnrichedFunctor r).map C D).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' C D F) =
      PointedMapping.familyVertex
        (boundaryReducedRealizationMap r (stableExactInputMap F)) := by
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌) PUnit.unit)
    (stableBoundaryPointedEnrichedFunctor_hom r F)
  exact h.trans (PointedMapping.familyVertex_eq_pointedHomVertex _).symm

/-- 同じ完全関手の関手同型は、元の境界商の基点固定成分の等号を与える。 -/
lemma stableBoundaryReducedMap_component_of_functorIso (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    PointedMapping.componentOf (boundaryReducedRealizationMap r (stableExactInputMap F)) =
      PointedMapping.componentOf
        (boundaryReducedRealizationMap r (stableExactInputMap G)) := by
  let a := Classical.choice (nonempty_stableExactFunctorIsoEdge e)
  let b := a.map ((stableBoundaryPointedEnrichedFunctor r).map C D)
  have b' : SSet.Edge
      (PointedMapping.familyVertex
        (boundaryReducedRealizationMap r (stableExactInputMap F)))
      (PointedMapping.familyVertex
        (boundaryReducedRealizationMap r (stableExactInputMap G))) := {
    edge := b.edge
    src_eq := b.src_eq.trans (stableBoundaryPointedEnrichedFunctor_vertex r F)
    tgt_eq := b.tgt_eq.trans (stableBoundaryPointedEnrichedFunctor_vertex r G) }
  exact SSet.π₀.sound b'

end SerrePositivity.KST.SConstruction
