module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFunctoriality
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonCanonical
public import SerrePositivity.DifferentialGraded.Verdier.DerivedGraphComposition

/-! # graph 作用と、元の tria から誘導した Verdier 関手の比較正方形 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance graphSquareExtensionCommShift : (dgDerivedExtension A D E F).CommShift ℤ :=
  dgDerivedExtensionCommShift A D E F
local instance graphSquareExtensionIsTriangulated : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

lemma graphTriaFunctor_mem (X : TriaCategory A D) :
    derivedFiniteCellOver A E Set.univ
      ((dgDerivedExtension A D E F).obj X.obj) :=
  graphDerivedExtension_derivedFiniteCell_mem A D E F (derivedFiniteCellOver A E Set.univ)
    Set.univ (fun x _ => (triaRepresentable A E (F.obj x)).property) X.property

/-- 任意 dg 関手の実際の導来延長を tria に制限する。 -/
def graphTriaFunctor : TriaCategory A D ⥤ TriaCategory A E :=
  (derivedFiniteCellOver A E Set.univ).lift (triaInclusion A D ⋙ dgDerivedExtension A D E F)
    (graphTriaFunctor_mem A D E F)

instance graphTriaFunctorCommShift : (graphTriaFunctor A D E F).CommShift ℤ := by
  dsimp [graphTriaFunctor]
  infer_instance
instance graphTriaFunctorIsTriangulated : (graphTriaFunctor A D E F).IsTriangulated := by
  dsimp [graphTriaFunctor]
  infer_instance

variable (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)
include hF

lemma graphTriaFunctor_image {X : TriaCategory A D} (hX : triaImage A D S X) :
    triaImage A E T ((graphTriaFunctor A D E F).obj X) :=
  graphDerivedExtension_derivedFiniteCell_mem A D E F (derivedFiniteCellOver A E T) S
    (fun x hx => (moduleFiniteCellOver A E T).prop_map_obj (moduleToDerived A E)
      (moduleFiniteCellOver_representable A E (F.obj x) (hF x hx))) hX

lemma graphTriaFunctor_verdier_inverts :
    (triaImage A D S).trW.IsInvertedBy (graphTriaFunctor A D E F ⋙ triaQuotient A E T) := by
  intro X Y f hf
  exact (triangulatedKernel_trW_iff _ f).1
    ((triaImage A D S).trW_monotone (fun X hX =>
      verdierQuotient_isZero (triaImage A E T) _ (graphTriaFunctor_image A D E F S T hF hX))
      _ hf)

/-- 元の D→E の tria 関手を先に Verdier 局所化した、指定商間の関手。 -/
def graphVerdierFunctor : TriaQuotient A D S ⥤ TriaQuotient A E T :=
  Localization.lift (graphTriaFunctor A D E F ⋙ triaQuotient A E T)
    (graphTriaFunctor_verdier_inverts A D E F S T hF) (triaQuotient A D S)

def graphVerdierFunctorFactors :
    triaQuotient A D S ⋙ graphVerdierFunctor A D E F S T hF ≅
      graphTriaFunctor A D E F ⋙ triaQuotient A E T :=
  Localization.fac _ (graphTriaFunctor_verdier_inverts A D E F S T hF) _

instance graphVerdierFunctorLifting :
    Localization.Lifting (triaQuotient A D S) (triaImage A D S).trW
      (graphTriaFunctor A D E F ⋙ triaQuotient A E T)
      (graphVerdierFunctor A D E F S T hF) :=
  Localization.liftingLift _ (graphTriaFunctor_verdier_inverts A D E F S T hF) _

instance graphVerdierFunctorCommShift : (graphVerdierFunctor A D E F S T hF).CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (graphTriaFunctor A D E F ⋙ triaQuotient A E T) (graphVerdierFunctor A D E F S T hF)

instance graphVerdierFunctorFactorsCommShift :
    NatTrans.CommShift (graphVerdierFunctorFactors A D E F S T hF).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (graphTriaFunctor A D E F ⋙ triaQuotient A E T) (graphVerdierFunctor A D E F S T hF)

instance graphVerdierFunctorIsTriangulated :
    (graphVerdierFunctor A D E F S T hF).IsTriangulated := by
  have : (triaQuotient A D S).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (triaQuotient A D S) (triaImage A D S).trW
  exact Functor.isTriangulated_of_precomp_iso (graphVerdierFunctorFactors A D E F S T hF)

/-- dg 包含正方形は、実際の導来 graph 作用の正方形を与える。 -/
def graphDerivedQuotientSquare :
    dgDerivedExtension A D (QuotientObject D S) (inclusion A D S) ⋙
        dgDerivedExtension A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) ≅
      dgDerivedExtension A D E F ⋙
        dgDerivedExtension A E (QuotientObject E T) (inclusion A E T) :=
  derivedGraphExtensionCompositionIso A D (QuotientObject D S) (QuotientObject E T)
      (inclusion A D S) (quotientDGFunctor A D E F S T hF) ≪≫
    eqToIso (congrArg (dgDerivedExtension A D (QuotientObject E T))
      (quotientDGFunctor_inclusion A D E F S T hF)) ≪≫
    (derivedGraphExtensionCompositionIso A D E (QuotientObject E T) F (inclusion A E T)).symm

def graphTriaQuotientSquare :
    graphTriaFunctor A D E F ⋙ derivedComparisonTria A E T ≅
      derivedComparisonTria A D S ⋙
        graphTriaFunctor A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) :=
  ((whiskeringRight _ _ _).obj (triaInclusion A (QuotientObject E T))).preimageIso
    (X := graphTriaFunctor A D E F ⋙ derivedComparisonTria A E T)
    (Y := derivedComparisonTria A D S ⋙
      graphTriaFunctor A (QuotientObject D S) (QuotientObject E T)
        (quotientDGFunctor A D E F S T hF))
    (isoWhiskerLeft (triaInclusion A D) (graphDerivedQuotientSquare A D E F S T hF).symm)

/-- 実際に局所化した関手と局所 dg 商比較の正方形。K-flat 性はこの同型に不要。 -/
def graphLocalVerdierSquare :
    graphVerdierFunctor A D E F S T hF ⋙ localQuotientTriaFunctor A E T ≅
      localQuotientTriaFunctor A D S ⋙
        graphTriaFunctor A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) :=
  (Localization.fullyFaithfulWhiskeringLeft
    (triaQuotient A D S) (triaImage A D S).trW _).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (graphVerdierFunctorFactors A D E F S T hF) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (localQuotientTriaFactors A E T) ≪≫
      graphTriaQuotientSquare A D E F S T hF ≪≫
      isoWhiskerRight (localQuotientTriaFactors A D S).symm _ ≪≫
      Functor.associator _ _ _)

def graphCanonicalVerdierSquare :
    graphVerdierFunctor A D E F S T hF ⋙ quotientVerdierComparison A E T ≅
      quotientVerdierComparison A D S ⋙
        graphTriaFunctor A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) :=
  isoWhiskerLeft _ (quotientComparisonModelsIso A E T).symm ≪≫
    graphLocalVerdierSquare A D E F S T hF ≪≫
      isoWhiskerRight (quotientComparisonModelsIso A D S) _
end SerrePositivity.DifferentialGraded.DGQuotient
