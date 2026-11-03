module

public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetDiagramPresentation
public import SerrePositivity.InfinityCategories.F2.Ind.FunctorFilteredColimitDetection
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex

/-!
概要：元の全図式の単一 filtered 表示は、形状同型に沿って移送できる。
方針：C 全族と同じ全余錐を前合成し、元の頂点の厳密な表示を回収する。
規約：表示添字・正則 κ・元の図式を保持する。
使われ方：有限半順序表示を標準 span/cospan の元の図式へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 単一 filtered 表示は、任意の小さい形状同型の前合成で保たれる。 -/
lemma HasSingleFilteredDiagramPresentation.precomp_iso (κ : Cardinal.{u})
    {K L C : SSet.{u}} [Quasicategory C] (e : K ≅ L)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ IndInfinity κ C)
    (hD : HasSingleFilteredDiagramPresentation κ D) :
    HasSingleFilteredDiagramPresentation κ ((SSet.uliftFunctor.map e.hom) ≫ D) := by
  obtain ⟨I, hI, hfiltered, a, c, hcv, hc⟩ := hD
  letI := hI
  letI := hfiltered
  let f := (SSet.uliftFunctor.{u + 1, u}).map e.hom
  let a' := a ≫ (pre e.hom).app C
  let d := reindexFunctorCocone c f
  have hp : IsPointwiseColimitCone d :=
    (indFunctor_isPointwiseColimit_of_isColimit κ c hc).reindex f
  have he : (SSet.uliftFunctor.{u + 1, u}).map a' ≫ diagramYoneda κ K C =
      ((SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ L C) ≫
        (pre f).app (IndInfinity κ C) := by
    rw [show a' = a ≫ (pre e.hom).app C from rfl, Functor.map_comp,
      Category.assoc, diagramYoneda_restrict, ← Category.assoc]
  let d' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a' ≫ diagramYoneda κ K C) :=
    ⟨d.val, d.property.trans he.symm⟩
  refine ⟨I, hI, hfiltered, a', d', ?_, ?_⟩
  · change ((pre f).app (IndInfinity κ C)).app (Opposite.op ⦋0⦌) c.vertex = _
    rw [hcv]
    rfl
  · exact (isColimitCone_iff_of_coconeMap_eq d' d rfl).mpr
      (isColimitCone_functor_of_pointwise d hp)

end SerrePositivity.InfinityCategories.F2.Ind
