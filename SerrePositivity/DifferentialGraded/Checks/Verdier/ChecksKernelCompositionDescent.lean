module
public import SerrePositivity.DifferentialGraded.Verdier.Kernel


/-! # 実際の kernel 合成比較の指定商への降下の公理監査 -/
@[expose] public section
noncomputable section
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms supportedKernelComposite_columns
#print axioms supportedKernelComposite
#print axioms supportedKernelComposeFunctor
#print axioms supportedKernelComposeFunctor_map
#print axioms supportedKernelPerfectCompositionIso
#print axioms supportedKernelPerfectCompositionIso_naturality
#print axioms supportedKernelVerdierCompositeFactors
#print axioms supportedKernelVerdierCompositionIso
#print axioms supportedKernelVerdierCompositionIso_app
#print axioms supportedKernelCompletedCompositionIso
#print axioms conjugatedKernelCompositionIso
#print axioms supportedKernelCompletedTriaCompositionIso
#print axioms supportedKernelLocalPerfectCompositionIso

/-- 二つの dg 関手の graph kernel の合成でも、指定商の実際の完備作用は合成と比較できる。 -/
example (A : Type) [CommRing A] (D E B : Type)
    [DGCategory A D] [DGCategory A E] [DGCategory A B]
    [Small.{0} D] [Small.{0} E] [Small.{0} B] (hD : localHomKFlat A D)
    (F : DGFunctor A D E) (G : DGFunctor A E B) :
    let hP := graphPairKernelColumnsPerfect A D E F
    let hQ := graphPairKernelColumnsPerfect A E B G
    let P : SupportedPerfectKernelCategory A D E Set.univ Set.univ :=
      ⟨Morita.kernelGraph A D E F, hP, fun d _ => hP d⟩
    let Q : SupportedPerfectKernelCategory A E B Set.univ Set.univ :=
      ⟨Morita.kernelGraph A E B G, hQ, fun e _ => hQ e⟩
    (supportedKernelCompletedFunctor A D E Set.univ Set.univ).obj P ⋙
        (supportedKernelCompletedFunctor A E B Set.univ Set.univ).obj Q ≅
      (supportedKernelCompletedFunctor A D B Set.univ Set.univ).obj
        (supportedKernelComposite A D E B Set.univ Set.univ Set.univ hD P Q) := by
  dsimp only
  exact supportedKernelCompletedCompositionIso _ _ _ _ _ _ _ _ _ _
