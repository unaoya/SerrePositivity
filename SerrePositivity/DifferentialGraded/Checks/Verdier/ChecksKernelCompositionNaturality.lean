module
public import SerrePositivity.DifferentialGraded.Verdier.Kernel

/-! # 全 kernel 射に自然な降下合成比較の公理監査 -/
@[expose] public section
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms horizontalComparison
#print axioms horizontalComparison_naturality
#print axioms transportedComparison_naturality
#print axioms supportedKernelCompositionMap
#print axioms supportedKernelVerdierCompositeFactors_naturality
#print axioms supportedKernelVerdierCompositionIso_naturality
#print axioms karoubiFunctorCompositionIso_naturality
#print axioms supportedKernelCompletedCompositionIso_naturality
#print axioms conjugatedKernelCompositionIso_naturality
#print axioms supportedKernelCompletedTriaCompositionIso_naturality
#print axioms supportedKernelLocalPerfectCompositionIso_naturality

/-- 両 kernel をそれぞれ同型な対象へ換える場合にも、同じ完備合成比較が可換する。 -/
example (A : Type) [CommRing A] (D E B : Type)
    [DGCategory A D] [DGCategory A E] [DGCategory A B]
    [Small.{0} D] [Small.{0} E] [Small.{0} B]
    (S : Set D) (T : Set E) (U : Set B) (hD : localHomKFlat A D)
    (P P' : SupportedPerfectKernelCategory A D E S T)
    (Q Q' : SupportedPerfectKernelCategory A E B T U) (α : P ≅ P') (β : Q ≅ Q') :
    NatTrans.hcomp ((supportedKernelCompletedFunctor A D E S T).map α.hom)
        ((supportedKernelCompletedFunctor A E B T U).map β.hom) ≫
        (supportedKernelCompletedCompositionIso A D E B S T U hD P' Q').hom =
      (supportedKernelCompletedCompositionIso A D E B S T U hD P Q).hom ≫
        (supportedKernelCompletedFunctor A D B S U).map
          (supportedKernelCompositionMap A D E B S T U hD P P' Q Q' α.hom β.hom) :=
  supportedKernelCompletedCompositionIso_naturality A D E B S T U hD P P' Q Q' α.hom β.hom
