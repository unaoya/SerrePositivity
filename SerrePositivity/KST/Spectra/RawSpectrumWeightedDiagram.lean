module

public import SerrePositivity.KST.Spectra.RawSpectrumCotensorNaturality
public import SerrePositivity.KST.Spectra.KanSequenceWeightedDiagram
public import SerrePositivity.KST.Spectra.EndRightAdjoint

/-!
概要：一般の Kan 列の重み付き Hom 図式へ、整合写像空間を施した二変数図式の同型。
方針：各成分の cotensor 交換を、源制限・標的後合成の厳密な自然性で束ねる。
規約：全単体パラメータを保持する。使われ方：homotopy end と写像空間の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed Opposite
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance rawWeightedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

/-- 整合写像と重み付き内部 Hom の交換は、end を定める二変数図式全体の同型。 -/
def weightedDiagramIso {I : Type u} [SmallCategory I] (X : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) :
    EndRightAdjoint.postDiagram (pointedFunctor X) (KanSequence.weightedDiagram W D) ≅
      PointedWeightedEnd.diagram W (D ⋙ pointedFunctor X) :=
  NatIso.ofComponents
    (fun i ↦ NatIso.ofComponents
      (fun j ↦ cotensorIso X (D.obj j) (PointedObject.adjoin (W.obj i.unop)))
      (fun f ↦ by
        dsimp only [EndRightAdjoint.postDiagram, KanSequence.weightedDiagram,
          KanSequence.mappingBifunctor, PointedWeightedEnd.diagram,
          Enriched.FunctorCategory.diagram, eHomFunctor, Functor.comp, Functor.op,
          Functor.whiskeringLeft, Functor.whiskeringRight]
        simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        exact cotensorComparison_natural X _ (D.map f)))
    (fun f ↦ by
      apply NatTrans.ext
      funext j
      dsimp only [EndRightAdjoint.postDiagram, KanSequence.weightedDiagram,
        KanSequence.mappingBifunctor, PointedWeightedEnd.diagram,
        Enriched.FunctorCategory.diagram, eHomFunctor, Functor.comp, Functor.op,
        Functor.whiskeringLeft, Functor.whiskeringRight, NatTrans.comp_app,
        NatIso.ofComponents_hom_app]
      simp only [enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      have h := cotensorComparison_pre X (D.obj j)
        (PointedObject.adjoinFunctor.map (W.map f.unop))
      rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
      exact h)

/-- 整合写像を施した二変数図式の end と、整合写像を係数とする重み付き end の同型。 -/
def weightedDiagramEndIso {I : Type u} [SmallCategory I] (X : OmegaSpectrum.{u})
    (W : I ⥤ SSet.{u}) (D : I ⥤ KanSequence.{u}) :
    end_ (EndRightAdjoint.postDiagram (pointedFunctor X) (KanSequence.weightedDiagram W D)) ≅
      PointedWeightedEnd.obj W (D ⋙ pointedFunctor X) :=
  (endFunctor I PointedSimplicialSet.{u}).mapIso (weightedDiagramIso X W D)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
