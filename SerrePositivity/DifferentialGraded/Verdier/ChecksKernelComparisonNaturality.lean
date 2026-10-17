module
public import SerrePositivity.DifferentialGraded.Verdier.KernelComparisonNaturality
public import SerrePositivity.DifferentialGraded.Verdier.GraphPairMorita

/-! # kernel 射に自然な指定商・完備化・perfect 比較の公理監査 -/
@[expose] public section
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms supportedKernelPerfectFunctor
#print axioms supportedKernelVerdierMap_app
#print axioms supportedKernelVerdierFunctor
#print axioms supportedKernelVerdierMap_id
#print axioms supportedKernelVerdierMap_comp
#print axioms supportedKernelVerdierFactors
#print axioms supportedKernelCompletedFunctor
#print axioms supportedKernelCompletedTriaFunctor
#print axioms supportedKernelLocalPerfectFunctor
#print axioms supportedKernelLocalPerfectSquare
#print axioms supportedKernelLocalPerfectSquare_app
#print axioms supportedKernelLocalPerfectSquare_naturality

/-- 任意の dg 関手の graph kernel を入れた場合にも、誘導商作用は恒等射を保つ。 -/
example (A : Type) [CommRing A] (D E : Type) [DGCategory A D] [DGCategory A E]
    [Small.{0} D] [Small.{0} E] (F : DGFunctor A D E) :
    let hK := graphPairKernelColumnsPerfect A D E F
    let K : SupportedPerfectKernelCategory A D E Set.univ Set.univ :=
      ⟨Morita.kernelGraph A D E F, hK, fun d _ => hK d⟩
    supportedKernelVerdierMap A D E Set.univ Set.univ (𝟙 K) =
      𝟙 (supportedKernelVerdierValue A D E Set.univ Set.univ K) := by
  dsimp only
  exact supportedKernelVerdierMap_id _ _ _ _ _ _
