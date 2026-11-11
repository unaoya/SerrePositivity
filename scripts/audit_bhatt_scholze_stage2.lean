import SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDP
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBaseChange
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBasis
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPFactorial
import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction
import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeMaps
import SerrePositivity.BhattScholze.Prismatic.AffinePolynomial
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDelta
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaBounds
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaFlat
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaResidue
import SerrePositivity.BhattScholze.Prismatic.Envelope
import SerrePositivity.BhattScholze.Prismatic.PrismOver
import SerrePositivity.BhattScholze.Prismatic.VariableEnvelope
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedCoefficient
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge
import SerrePositivity.CommutativeAlgebra.DeRham.Graded
import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion
import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
import SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinCochains
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy
import SerrePositivity.HomologicalAlgebra.Cosimplicial.PrincipalShortExact
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import SerrePositivity.HomologicalAlgebra.Cosimplicial.ShortExact
import SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
import SerrePositivity.BhattScholze.Perfectoidization.Derived.FiniteEtalePerfectoid
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCardinality
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite
import SerrePositivity.BhattScholze.Prismatic.PolynomialFrobeniusCech
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity
import SerrePositivity.HomologicalAlgebra.Cech.Basic
import SerrePositivity.HomologicalAlgebra.Cech.BaseChange
import SerrePositivity.HomologicalAlgebra.Cech.Split
import SerrePositivity.HomologicalAlgebra.Cech.Filtered
import SerrePositivity.HomologicalAlgebra.Cech.Diagonal
import SerrePositivity.HomologicalAlgebra.Cech.Double
import SerrePositivity.HomologicalAlgebra.Cech.Composition
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Basic
import SerrePositivity.CommutativeAlgebra.Ultraproduct.Localization
import SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Colimit
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Endpoint
import SerrePositivity.CommutativeAlgebra.ValuationInterval.FinitePresentation
import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechMilnor
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechOverlap
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechUltraproduct
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcIntervalOverlap
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorDetection
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorTensor
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectCech
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationProduct
import SerrePositivity.BhattScholze.Delta.Division.BaseChange
import SerrePositivity.BhattScholze.Prismatic.CrystallineAffineDivision
import SerrePositivity.BhattScholze.Prismatic.CrystallineAffineEnvelope
import SerrePositivity.BhattScholze.Prismatic.CrystallineBase
import SerrePositivity.BhattScholze.Prismatic.CrystallineBridge
import SerrePositivity.BhattScholze.Prismatic.CrystallineBridgeCoordinates
import SerrePositivity.BhattScholze.Prismatic.CrystallineBridgePushout
import SerrePositivity.BhattScholze.Prismatic.CrystallineCechResidue
import SerrePositivity.BhattScholze.Prismatic.CrystallineCechSource
import SerrePositivity.BhattScholze.Prismatic.CrystallineCompletedFreeDelta
import SerrePositivity.BhattScholze.Prismatic.CrystallineCompletedPushout
import SerrePositivity.BhattScholze.Prismatic.CrystallineCoordinates
import SerrePositivity.BhattScholze.Prismatic.CrystallineDivisionCompletion
import SerrePositivity.BhattScholze.Prismatic.CrystallineDivisionEnvelope
import SerrePositivity.BhattScholze.Prismatic.CrystallineExtraContraction
import SerrePositivity.BhattScholze.Prismatic.CrystallineExtraModel
import SerrePositivity.BhattScholze.Prismatic.CrystallineExtraPolynomial
import SerrePositivity.BhattScholze.Prismatic.CrystallineFreeDivision
import SerrePositivity.BhattScholze.Prismatic.CrystallinePDInclusion
import SerrePositivity.BhattScholze.Prismatic.CrystallinePDIntegral
import SerrePositivity.BhattScholze.Prismatic.CrystallinePDModel
import SerrePositivity.BhattScholze.Prismatic.CrystallinePDRawComparison
import SerrePositivity.BhattScholze.Prismatic.CrystallinePDTensorPresentation
import SerrePositivity.BhattScholze.Prismatic.CrystallinePrincipalResidue
import SerrePositivity.BhattScholze.Prismatic.CrystallineRawCoordinates
import SerrePositivity.BhattScholze.Prismatic.CrystallineRawPDFactor
import SerrePositivity.BhattScholze.Prismatic.CrystallineRawPDSplit
import SerrePositivity.BhattScholze.Prismatic.CrystallineReductionPushout
import SerrePositivity.BhattScholze.Prismatic.CrystallineTensorRegularity
import SerrePositivity.BhattScholze.Prismatic.FrobeniusCechComparison
import SerrePositivity.BhattScholze.Prismatic.HodgeTateAffineModel
import SerrePositivity.BhattScholze.Prismatic.PDCompletedCech
import SerrePositivity.BhattScholze.Prismatic.PDPolynomialCech
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import SerrePositivity.BhattScholze.Almost.CompletedModuleTensor
import SerrePositivity.BhattScholze.Almost.AlmostTensor
import SerrePositivity.BhattScholze.Almost.AlmostTensorForward
import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
import SerrePositivity.BhattScholze.Almost.AlmostGenerators
import SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison
import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralApproximation
import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureApproximation
import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureCompletion
import SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectoidFilteredColimit
import SerrePositivity.EInfinity.Interface.Core
import SerrePositivity.EInfinity.Interface.StrictInputs
import SerrePositivity.EInfinity.Interface.Theory
import SerrePositivity.EInfinity.BarrattEccles.Theory
import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPDerivation
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPIntegral
import SerrePositivity.BhattScholze.Prismatic.BocksteinCupSquare
import SerrePositivity.BhattScholze.Prismatic.CartierCompletedForms
import SerrePositivity.BhattScholze.Prismatic.CrystallineBockstein
import SerrePositivity.BhattScholze.Prismatic.CrystallineChain
import SerrePositivity.BhattScholze.Prismatic.CrystallineChainProduct
import SerrePositivity.BhattScholze.Prismatic.CrystallineCoordinateReduction
import SerrePositivity.BhattScholze.Prismatic.CrystallineGeneratorBridge
import SerrePositivity.BhattScholze.Prismatic.CrystallineGeneratorClasses
import SerrePositivity.BhattScholze.Prismatic.CrystallineTotalCoordinate
import SerrePositivity.BhattScholze.Prismatic.CrystallineTotalRegular
import SerrePositivity.BhattScholze.Prismatic.FinitePolynomialCartier
import SerrePositivity.BhattScholze.Prismatic.HodgeTateAffineForms
import SerrePositivity.BhattScholze.Prismatic.HodgeTateBocksteinSquare
import SerrePositivity.BhattScholze.Prismatic.HodgeTateCartierAssembly
import SerrePositivity.BhattScholze.Prismatic.HodgeTateCompletedMap
import SerrePositivity.BhattScholze.Prismatic.HodgeTateGradedDGAlgebra
import SerrePositivity.BhattScholze.Prismatic.HodgeTateModule
import SerrePositivity.BhattScholze.Prismatic.HodgeTateModuleComplete
import SerrePositivity.BhattScholze.Prismatic.HodgeTateOneDerivative
import SerrePositivity.BhattScholze.Prismatic.HodgeTateOneGenerators
import SerrePositivity.BhattScholze.Prismatic.HodgeTateOneSquare
import SerrePositivity.BhattScholze.Prismatic.HodgeTateZero
import SerrePositivity.BhattScholze.Prismatic.HodgeTateZeroLeibniz
import SerrePositivity.BhattScholze.Prismatic.PDColumnContraction
import SerrePositivity.BhattScholze.Prismatic.PDColumnCoordinateEvaluation
import SerrePositivity.BhattScholze.Prismatic.PDCompletedDerivation
import SerrePositivity.BhattScholze.Prismatic.PDCoordinateForms
import SerrePositivity.BhattScholze.Prismatic.PDCrystallineReduction
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamAxisProduct
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamBicomplex
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamBigradedLeibniz
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamCech
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamCoefficients
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamCohomology
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamCohomologyProduct
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamCollapse
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumn
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnComparison
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnPoincare
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnZero
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnZeroProduct
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamComparisonClass
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamProjectionProduct
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamRow
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamRowComparison
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamRowZeroProduct
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamTotalCoefficients
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamTotalLeibniz
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamTotalProduct
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamWedge
import SerrePositivity.BhattScholze.Prismatic.PDModelReduction
import SerrePositivity.BhattScholze.Prismatic.PDRawCoefficients
import SerrePositivity.BhattScholze.Prismatic.PDRawDeRhamColumn
import SerrePositivity.BhattScholze.Prismatic.PDRawDifferential
import SerrePositivity.BhattScholze.Prismatic.PDRawFrobeniusCoordinate
import SerrePositivity.BhattScholze.Prismatic.PDRawPartialCoefficients
import SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateBasis
import SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateHomotopy
import SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateIntegral
import SerrePositivity.CommutativeAlgebra.DeRham.CartierFinite
import SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteGenerators
import SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteProduct
import SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteRepresentative
import SerrePositivity.CommutativeAlgebra.DeRham.CartierOneVariable
import SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
import SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
import SerrePositivity.CommutativeAlgebra.DeRham.CohomologyWedge
import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoefficientMap
import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorContraction
import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoordinateProjection
import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction
import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCoordinatePower
import SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso
import SerrePositivity.HomologicalAlgebra.BicomplexComponents
import SerrePositivity.HomologicalAlgebra.BicomplexProductLeibniz
import SerrePositivity.HomologicalAlgebra.BicomplexProjection
import SerrePositivity.HomologicalAlgebra.BicomplexRowQuasiIso
import SerrePositivity.HomologicalAlgebra.CochainProduct
import SerrePositivity.HomologicalAlgebra.CochainProductClass
import SerrePositivity.HomologicalAlgebra.CochainProductNaturality
import SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyCupGradedRing
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
import SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleCochainCup
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalFlat
import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPModPBlocks
import SerrePositivity.BhattScholze.Delta.DividedPower.FrobeniusDivisionPD
import SerrePositivity.BhattScholze.Delta.DividedPower.FrobeniusDivisionRegularSequence
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePD
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDFactorial
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDKoszul
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDPrimeRegular
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDTor
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDUniversalTor
import SerrePositivity.BhattScholze.Delta.DividedPower.TruncatedPolynomialBasis
import SerrePositivity.CommutativeAlgebra.KoszulRegular.Powers
import SerrePositivity.CommutativeAlgebra.KoszulRegular.PrincipalReduction
import SerrePositivity.EInfinity.ComplexLimits.StrictHomology
import SerrePositivity.EInfinity.SimplicialLocalization.SourceHom
import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestriction
import SerrePositivity.EInfinity.BarrattEccles.Theory.Conservative
import SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteInitial
import SerrePositivity.BhattScholze.Delta.Distinguished.Universal
import SerrePositivity.BhattScholze.Delta.Division.FrobeniusPushout
import SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented
import SerrePositivity.BhattScholze.Prism.Basic.UniversalOrientedFrobenius
import SerrePositivity.BhattScholze.Prismatic.RelativeCompleteRegularity
import SerrePositivity.CommutativeAlgebra.CompletelyFlat.LocalizedTor
import SerrePositivity.BhattScholze.Prismatic.BigCechAffineEnvelope
import SerrePositivity.BhattScholze.Prismatic.BigCechAlexander
import SerrePositivity.BhattScholze.Prismatic.BigCechCompletionLift
import SerrePositivity.BhattScholze.Prismatic.BigCechFrameComparison
import SerrePositivity.BhattScholze.Prismatic.BigCechFrameLift
import SerrePositivity.BhattScholze.Prismatic.BigCechFrameResidue
import SerrePositivity.BhattScholze.Prismatic.BigCechFrameRetraction
import SerrePositivity.BhattScholze.Prismatic.BigPDModel
import SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelope
import SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion
import SerrePositivity.BhattScholze.Prismatic.PDCechFrameHomotopy
import SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import SerrePositivity.BhattScholze.Prismatic.PDCechNerveNaturality
import SerrePositivity.BhattScholze.Prismatic.PDCompletedColumnContraction
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedColumnZero
import SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedProjection
import SerrePositivity.BhattScholze.Prismatic.PDFrobeniusLift
import SerrePositivity.BhattScholze.Prismatic.PDFromGenerators
import SerrePositivity.BhattScholze.Prismatic.PDModelBaseChange
import SerrePositivity.BhattScholze.Prismatic.PDPolynomialFunctor
import SerrePositivity.BhattScholze.Prismatic.PDPolynomialGraph
import SerrePositivity.BhattScholze.Prismatic.PDPolynomialSplitEnvelope
import SerrePositivity.BhattScholze.Prismatic.PDRawBaseChangeLinear
import SerrePositivity.BhattScholze.Prismatic.PDRawCoefficientPD
import SerrePositivity.BhattScholze.Prismatic.PDRelativeFree
import SerrePositivity.BhattScholze.Prismatic.PDSmallModelComparison
import SerrePositivity.BhattScholze.Prismatic.PDSmallRawEnvelope
import SerrePositivity.BhattScholze.Prismatic.PolynomialCategory
import SerrePositivity.BhattScholze.Prismatic.PolynomialCompletionFunctor
import SerrePositivity.BhattScholze.Prismatic.PolynomialCompletionResidue
import SerrePositivity.BhattScholze.Prismatic.RelativePDEnvelope
import SerrePositivity.BhattScholze.Prismatic.UniversalWittComparison
import SerrePositivity.BhattScholze.Prismatic.WittAdicCompleteness
import SerrePositivity.BhattScholze.Prismatic.WittBigBridge
import SerrePositivity.BhattScholze.Prismatic.WittBigCrystalline
import SerrePositivity.BhattScholze.Prismatic.WittCrystallinePrism
import SerrePositivity.BhattScholze.Prismatic.WittPDBase
import SerrePositivity.BhattScholze.Prismatic.WittPDEnvelopeCrystalline
import SerrePositivity.BhattScholze.Prismatic.WittPDPrismMaps
import SerrePositivity.BhattScholze.Prismatic.WittSmallFrame
import SerrePositivity.BhattScholze.Prismatic.WittToSmall
import SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame
import SerrePositivity.BhattScholze.Delta.Basic.Tensor
import SerrePositivity.BhattScholze.Prism.Bounded.CompleteCochainPurity
import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatCochain
import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatDiscrete
import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCardinal
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorFlatness
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorH0
import SerrePositivity.BhattScholze.Prism.Bounded.CompletelyFlatPrism
import SerrePositivity.BhattScholze.Prism.Bounded.CompletionFiniteResidue
import SerrePositivity.BhattScholze.Prismatic.FiniteCechDescent
import SerrePositivity.BhattScholze.Prismatic.FlatCechComparison
import SerrePositivity.BhattScholze.Prismatic.FlatCechConerve
import SerrePositivity.BhattScholze.Prismatic.FlatCechDescent
import SerrePositivity.BhattScholze.Prismatic.FlatCechLimit
import SerrePositivity.BhattScholze.Prismatic.FlatCechSheaf
import SerrePositivity.BhattScholze.Prismatic.FlatCover
import SerrePositivity.BhattScholze.Prismatic.FlatCoverPushout
import SerrePositivity.BhattScholze.Prismatic.FlatPushoutResidue
import SerrePositivity.BhattScholze.Prismatic.FlatSiteResidue
import SerrePositivity.BhattScholze.Prismatic.FlatSiteSheaf
import SerrePositivity.BhattScholze.Prismatic.FlatTopologyPushout
import SerrePositivity.BhattScholze.Prismatic.VariableEnvelopeBaseChange
import SerrePositivity.CategoryTheory.FiniteWidePushout
import SerrePositivity.CategoryTheory.FiniteWidePushoutMap
import SerrePositivity.CommutativeAlgebra.Adic.CompatibleResidues
import SerrePositivity.CommutativeAlgebra.Adic.ModuleCompleteSup
import SerrePositivity.CommutativeAlgebra.CompletelyFlat.FiniteIdealReduction
import SerrePositivity.HomologicalAlgebra.Cech.InverseTower
import SerrePositivity.BhattScholze.Semiperfectoid.DiscreteDelta
import SerrePositivity.BhattScholze.Semiperfectoid.DiscretePrism
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelope
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeCoefficient
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeCompletedResidue
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeConormal
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeDiscrete
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeExistence
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeInitial
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeInvertP
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeInvertPGenerators
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeKoszul
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopePresentation
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeReduction
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeRegular
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeResidue
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeTensorSwap
import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeVariables
import SerrePositivity.BhattScholze.Semiperfectoid.PrismRetract
import SerrePositivity.BhattScholze.Semiperfectoid.RawVariableEnvelope
import SerrePositivity.CategoryTheory.InitialOfRetraction
import SerrePositivity.CommutativeAlgebra.Adic.RingRetract
import SerrePositivity.CommutativeAlgebra.Koszul.Generators
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionEquivalence
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RegularQuotientH0
import SerrePositivity.HomologicalAlgebra.DerivedScalarExtensionComposition
import SerrePositivity.HomologicalAlgebra.KoszulRegularBaseChange
import SerrePositivity.HomologicalAlgebra.RegularRelationCompletedBaseChange
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDReduction
import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDTruncatedFlat
import SerrePositivity.BhattScholze.Prism.Basic.Construction61Frobenius
import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCover
import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverCochainTor
import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverCompleteTor
import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverFactorization
import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverPairTor
import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverReduction
import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverRegularity
import SerrePositivity.BhattScholze.Prismatic.Construction61Detection
import SerrePositivity.BhattScholze.Prismatic.Construction61Reflection
import SerrePositivity.CommutativeAlgebra.Adic.RegularLift
import SerrePositivity.CommutativeAlgebra.Frobenius.PrincipalQuotientFlat
import SerrePositivity.CommutativeAlgebra.Koszul.UnboundedTensor
import SerrePositivity.HomologicalAlgebra.CochainCompleteDetection
import SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude
import SerrePositivity.HomologicalAlgebra.CochainFlatDetection
import SerrePositivity.HomologicalAlgebra.CompleteBaseChangeConservative
import SerrePositivity.HomologicalAlgebra.CompleteCochainCone
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairRestriction
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedCoordinate
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedCoordinateResidue
import SerrePositivity.HomologicalAlgebra.KoszulTorBound
import SerrePositivity.HomologicalAlgebra.RegularQuotientUnboundedModel
import SerrePositivity.HomologicalAlgebra.ScalarConeQuotientModel
import SerrePositivity.HomologicalAlgebra.SemifreeBaseChangeModel
import SerrePositivity.HomologicalAlgebra.TorPostFlatComposition
import SerrePositivity.HomologicalAlgebra.TwoCoordinateCompleteTor
import SerrePositivity.HomologicalAlgebra.UnboundedSemifreeModel
import Lean.Util.CollectAxioms

/-!
概要：段階 II で BS の drafts から本体へ移したモジュールを公理監査する。
方針：下の一覧のモジュールで定義された宣言（生成宣言を含む）について、公理の依存を再帰的に調べる。
規約：標準三公理 propext・Classical.choice・Quot.sound だけを許す。新しいモジュールを取り込むたびに、import と一覧の両方に足す。
使われ方：調整役が取り込みのたびに `lake env lean` で実行する（import するモジュールを先に `lake build`）。
-/

open Lean in
run_cmd do
  let mods : Array Name := #[
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDReduction,
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDTruncatedFlat,
    `SerrePositivity.BhattScholze.Prism.Basic.Construction61Frobenius,
    `SerrePositivity.BhattScholze.Prism.Basic.CrystallineCover,
    `SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverCochainTor,
    `SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverCompleteTor,
    `SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverFactorization,
    `SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverPairTor,
    `SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverReduction,
    `SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverRegularity,
    `SerrePositivity.BhattScholze.Prismatic.Construction61Detection,
    `SerrePositivity.BhattScholze.Prismatic.Construction61Reflection,
    `SerrePositivity.CommutativeAlgebra.Adic.RegularLift,
    `SerrePositivity.CommutativeAlgebra.Frobenius.PrincipalQuotientFlat,
    `SerrePositivity.CommutativeAlgebra.Koszul.UnboundedTensor,
    `SerrePositivity.HomologicalAlgebra.CochainCompleteDetection,
    `SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude,
    `SerrePositivity.HomologicalAlgebra.CochainFlatDetection,
    `SerrePositivity.HomologicalAlgebra.CompleteBaseChangeConservative,
    `SerrePositivity.HomologicalAlgebra.CompleteCochainCone,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairRestriction,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedCoordinate,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedCoordinateResidue,
    `SerrePositivity.HomologicalAlgebra.KoszulTorBound,
    `SerrePositivity.HomologicalAlgebra.RegularQuotientUnboundedModel,
    `SerrePositivity.HomologicalAlgebra.ScalarConeQuotientModel,
    `SerrePositivity.HomologicalAlgebra.SemifreeBaseChangeModel,
    `SerrePositivity.HomologicalAlgebra.TorPostFlatComposition,
    `SerrePositivity.HomologicalAlgebra.TwoCoordinateCompleteTor,
    `SerrePositivity.HomologicalAlgebra.UnboundedSemifreeModel,
    `SerrePositivity.BhattScholze.Semiperfectoid.DiscreteDelta,
    `SerrePositivity.BhattScholze.Semiperfectoid.DiscretePrism,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelope,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeCoefficient,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeCompletedResidue,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeConormal,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeDiscrete,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeExistence,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeInitial,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeInvertP,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeInvertPGenerators,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeKoszul,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopePresentation,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeReduction,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeRegular,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeResidue,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeTensorSwap,
    `SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeVariables,
    `SerrePositivity.BhattScholze.Semiperfectoid.PrismRetract,
    `SerrePositivity.BhattScholze.Semiperfectoid.RawVariableEnvelope,
    `SerrePositivity.CategoryTheory.InitialOfRetraction,
    `SerrePositivity.CommutativeAlgebra.Adic.RingRetract,
    `SerrePositivity.CommutativeAlgebra.Koszul.Generators,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionEquivalence,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.RegularQuotientH0,
    `SerrePositivity.HomologicalAlgebra.DerivedScalarExtensionComposition,
    `SerrePositivity.HomologicalAlgebra.KoszulRegularBaseChange,
    `SerrePositivity.HomologicalAlgebra.RegularRelationCompletedBaseChange,
    `SerrePositivity.BhattScholze.Delta.Basic.Tensor,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompleteCochainPurity,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatCochain,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatDiscrete,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCardinal,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorFlatness,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorH0,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompletelyFlatPrism,
    `SerrePositivity.BhattScholze.Prism.Bounded.CompletionFiniteResidue,
    `SerrePositivity.BhattScholze.Prismatic.FiniteCechDescent,
    `SerrePositivity.BhattScholze.Prismatic.FlatCechComparison,
    `SerrePositivity.BhattScholze.Prismatic.FlatCechConerve,
    `SerrePositivity.BhattScholze.Prismatic.FlatCechDescent,
    `SerrePositivity.BhattScholze.Prismatic.FlatCechLimit,
    `SerrePositivity.BhattScholze.Prismatic.FlatCechSheaf,
    `SerrePositivity.BhattScholze.Prismatic.FlatCover,
    `SerrePositivity.BhattScholze.Prismatic.FlatCoverPushout,
    `SerrePositivity.BhattScholze.Prismatic.FlatPushoutResidue,
    `SerrePositivity.BhattScholze.Prismatic.FlatSiteResidue,
    `SerrePositivity.BhattScholze.Prismatic.FlatSiteSheaf,
    `SerrePositivity.BhattScholze.Prismatic.FlatTopologyPushout,
    `SerrePositivity.BhattScholze.Prismatic.VariableEnvelopeBaseChange,
    `SerrePositivity.CategoryTheory.FiniteWidePushout,
    `SerrePositivity.CategoryTheory.FiniteWidePushoutMap,
    `SerrePositivity.CommutativeAlgebra.Adic.CompatibleResidues,
    `SerrePositivity.CommutativeAlgebra.Adic.ModuleCompleteSup,
    `SerrePositivity.CommutativeAlgebra.CompletelyFlat.FiniteIdealReduction,
    `SerrePositivity.HomologicalAlgebra.Cech.InverseTower,
    `SerrePositivity.BhattScholze.Prismatic.BigCechAffineEnvelope,
    `SerrePositivity.BhattScholze.Prismatic.BigCechAlexander,
    `SerrePositivity.BhattScholze.Prismatic.BigCechCompletionLift,
    `SerrePositivity.BhattScholze.Prismatic.BigCechFrameComparison,
    `SerrePositivity.BhattScholze.Prismatic.BigCechFrameLift,
    `SerrePositivity.BhattScholze.Prismatic.BigCechFrameResidue,
    `SerrePositivity.BhattScholze.Prismatic.BigCechFrameRetraction,
    `SerrePositivity.BhattScholze.Prismatic.BigPDModel,
    `SerrePositivity.BhattScholze.Prismatic.CompletedPDEnvelope,
    `SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion,
    `SerrePositivity.BhattScholze.Prismatic.PDCechFrameHomotopy,
    `SerrePositivity.BhattScholze.Prismatic.PDCechNerve,
    `SerrePositivity.BhattScholze.Prismatic.PDCechNerveNaturality,
    `SerrePositivity.BhattScholze.Prismatic.PDCompletedColumnContraction,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedColumnZero,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCompletedProjection,
    `SerrePositivity.BhattScholze.Prismatic.PDFrobeniusLift,
    `SerrePositivity.BhattScholze.Prismatic.PDFromGenerators,
    `SerrePositivity.BhattScholze.Prismatic.PDModelBaseChange,
    `SerrePositivity.BhattScholze.Prismatic.PDPolynomialFunctor,
    `SerrePositivity.BhattScholze.Prismatic.PDPolynomialGraph,
    `SerrePositivity.BhattScholze.Prismatic.PDPolynomialSplitEnvelope,
    `SerrePositivity.BhattScholze.Prismatic.PDRawBaseChangeLinear,
    `SerrePositivity.BhattScholze.Prismatic.PDRawCoefficientPD,
    `SerrePositivity.BhattScholze.Prismatic.PDRelativeFree,
    `SerrePositivity.BhattScholze.Prismatic.PDSmallModelComparison,
    `SerrePositivity.BhattScholze.Prismatic.PDSmallRawEnvelope,
    `SerrePositivity.BhattScholze.Prismatic.PolynomialCategory,
    `SerrePositivity.BhattScholze.Prismatic.PolynomialCompletionFunctor,
    `SerrePositivity.BhattScholze.Prismatic.PolynomialCompletionResidue,
    `SerrePositivity.BhattScholze.Prismatic.RelativePDEnvelope,
    `SerrePositivity.BhattScholze.Prismatic.UniversalWittComparison,
    `SerrePositivity.BhattScholze.Prismatic.WittAdicCompleteness,
    `SerrePositivity.BhattScholze.Prismatic.WittBigBridge,
    `SerrePositivity.BhattScholze.Prismatic.WittBigCrystalline,
    `SerrePositivity.BhattScholze.Prismatic.WittCrystallinePrism,
    `SerrePositivity.BhattScholze.Prismatic.WittPDBase,
    `SerrePositivity.BhattScholze.Prismatic.WittPDEnvelopeCrystalline,
    `SerrePositivity.BhattScholze.Prismatic.WittPDPrismMaps,
    `SerrePositivity.BhattScholze.Prismatic.WittSmallFrame,
    `SerrePositivity.BhattScholze.Prismatic.WittToSmall,
    `SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame,
    `SerrePositivity.BhattScholze.Delta.Distinguished.Universal,
    `SerrePositivity.BhattScholze.Delta.Division.FrobeniusPushout,
    `SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented,
    `SerrePositivity.BhattScholze.Prism.Basic.UniversalOrientedFrobenius,
    `SerrePositivity.BhattScholze.Prismatic.RelativeCompleteRegularity,
    `SerrePositivity.CommutativeAlgebra.CompletelyFlat.LocalizedTor,
    `SerrePositivity.EInfinity.ComplexLimits.StrictHomology,
    `SerrePositivity.EInfinity.SimplicialLocalization.SourceHom,
    `SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestriction,
    `SerrePositivity.EInfinity.BarrattEccles.Theory.Conservative,
    `SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteInitial,
    `SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalFlat,
    `SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPModPBlocks,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FrobeniusDivisionPD,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FrobeniusDivisionRegularSequence,
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePD,
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDFactorial,
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDKoszul,
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDPrimeRegular,
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDTor,
    `SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDUniversalTor,
    `SerrePositivity.BhattScholze.Delta.DividedPower.TruncatedPolynomialBasis,
    `SerrePositivity.CommutativeAlgebra.KoszulRegular.Powers,
    `SerrePositivity.CommutativeAlgebra.KoszulRegular.PrincipalReduction,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPDerivation,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPIntegral,
    `SerrePositivity.BhattScholze.Prismatic.BocksteinCupSquare,
    `SerrePositivity.BhattScholze.Prismatic.CartierCompletedForms,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineBockstein,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineChain,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineChainProduct,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineCoordinateReduction,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineGeneratorBridge,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineGeneratorClasses,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineTotalCoordinate,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineTotalRegular,
    `SerrePositivity.BhattScholze.Prismatic.FinitePolynomialCartier,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateAffineForms,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateBocksteinSquare,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateCartierAssembly,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateCompletedMap,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateGradedDGAlgebra,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateModule,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateModuleComplete,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateOneDerivative,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateOneGenerators,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateOneSquare,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateZero,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateZeroLeibniz,
    `SerrePositivity.BhattScholze.Prismatic.PDColumnContraction,
    `SerrePositivity.BhattScholze.Prismatic.PDColumnCoordinateEvaluation,
    `SerrePositivity.BhattScholze.Prismatic.PDCompletedDerivation,
    `SerrePositivity.BhattScholze.Prismatic.PDCoordinateForms,
    `SerrePositivity.BhattScholze.Prismatic.PDCrystallineReduction,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamAxisProduct,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamBicomplex,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamBigradedLeibniz,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCech,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCoefficients,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCohomology,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCohomologyProduct,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamCollapse,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumn,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnComparison,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnPoincare,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnZero,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamColumnZeroProduct,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamComparisonClass,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamProjectionProduct,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamRow,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamRowComparison,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamRowZeroProduct,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamTotalCoefficients,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamTotalLeibniz,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamTotalProduct,
    `SerrePositivity.BhattScholze.Prismatic.PDDeRhamWedge,
    `SerrePositivity.BhattScholze.Prismatic.PDModelReduction,
    `SerrePositivity.BhattScholze.Prismatic.PDRawCoefficients,
    `SerrePositivity.BhattScholze.Prismatic.PDRawDeRhamColumn,
    `SerrePositivity.BhattScholze.Prismatic.PDRawDifferential,
    `SerrePositivity.BhattScholze.Prismatic.PDRawFrobeniusCoordinate,
    `SerrePositivity.BhattScholze.Prismatic.PDRawPartialCoefficients,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateBasis,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateHomotopy,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateIntegral,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierFinite,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteGenerators,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteProduct,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierFiniteRepresentative,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierOneVariable,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives,
    `SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight,
    `SerrePositivity.CommutativeAlgebra.DeRham.CohomologyWedge,
    `SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoefficientMap,
    `SerrePositivity.CommutativeAlgebra.DeRham.ExteriorContraction,
    `SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoordinateProjection,
    `SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction,
    `SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCoordinatePower,
    `SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso,
    `SerrePositivity.HomologicalAlgebra.BicomplexComponents,
    `SerrePositivity.HomologicalAlgebra.BicomplexProductLeibniz,
    `SerrePositivity.HomologicalAlgebra.BicomplexProjection,
    `SerrePositivity.HomologicalAlgebra.BicomplexRowQuasiIso,
    `SerrePositivity.HomologicalAlgebra.CochainProduct,
    `SerrePositivity.HomologicalAlgebra.CochainProductClass,
    `SerrePositivity.HomologicalAlgebra.CochainProductNaturality,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.AWBilinear,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyCupGradedRing,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleCochainCup,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap,
    `SerrePositivity.EInfinity.Interface.Core,
    `SerrePositivity.EInfinity.Interface.StrictInputs,
    `SerrePositivity.EInfinity.Interface.Theory,
    `SerrePositivity.EInfinity.BarrattEccles.Theory,
    `SerrePositivity.EInfinity.Perfectoidization.TheoryInterface,
    `SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralApproximation,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureApproximation,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureCompletion,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectoidFilteredColimit,
    `SerrePositivity.BhattScholze.Almost.CompletedModuleTensor,
    `SerrePositivity.BhattScholze.Almost.AlmostTensor,
    `SerrePositivity.BhattScholze.Almost.AlmostTensorForward,
    `SerrePositivity.BhattScholze.Almost.AlmostConnectivity,
    `SerrePositivity.BhattScholze.Almost.AlmostGenerators,
    `SerrePositivity.BhattScholze.Delta.Division.BaseChange,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineAffineDivision,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineAffineEnvelope,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineBase,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineBridge,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineBridgeCoordinates,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineBridgePushout,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineCechResidue,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineCechSource,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineCompletedFreeDelta,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineCompletedPushout,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineCoordinates,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineDivisionCompletion,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineDivisionEnvelope,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineExtraContraction,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineExtraModel,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineExtraPolynomial,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineFreeDivision,
    `SerrePositivity.BhattScholze.Prismatic.CrystallinePDInclusion,
    `SerrePositivity.BhattScholze.Prismatic.CrystallinePDIntegral,
    `SerrePositivity.BhattScholze.Prismatic.CrystallinePDModel,
    `SerrePositivity.BhattScholze.Prismatic.CrystallinePDRawComparison,
    `SerrePositivity.BhattScholze.Prismatic.CrystallinePDTensorPresentation,
    `SerrePositivity.BhattScholze.Prismatic.CrystallinePrincipalResidue,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineRawCoordinates,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineRawPDFactor,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineRawPDSplit,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineReductionPushout,
    `SerrePositivity.BhattScholze.Prismatic.CrystallineTensorRegularity,
    `SerrePositivity.BhattScholze.Prismatic.FrobeniusCechComparison,
    `SerrePositivity.BhattScholze.Prismatic.HodgeTateAffineModel,
    `SerrePositivity.BhattScholze.Prismatic.PDCompletedCech,
    `SerrePositivity.BhattScholze.Prismatic.PDPolynomialCech,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor,
    `SerrePositivity.CommutativeAlgebra.Ultraproduct.Basic,
    `SerrePositivity.CommutativeAlgebra.Ultraproduct.Localization,
    `SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic,
    `SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic,
    `SerrePositivity.CommutativeAlgebra.ValuationInterval.Colimit,
    `SerrePositivity.CommutativeAlgebra.ValuationInterval.Endpoint,
    `SerrePositivity.CommutativeAlgebra.ValuationInterval.FinitePresentation,
    `SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechMilnor,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechOverlap,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechUltraproduct,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcIntervalOverlap,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorDetection,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorTensor,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectCech,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationProduct,
    `SerrePositivity.HomologicalAlgebra.Cech.Basic,
    `SerrePositivity.HomologicalAlgebra.Cech.BaseChange,
    `SerrePositivity.HomologicalAlgebra.Cech.Split,
    `SerrePositivity.HomologicalAlgebra.Cech.Filtered,
    `SerrePositivity.HomologicalAlgebra.Cech.Diagonal,
    `SerrePositivity.HomologicalAlgebra.Cech.Double,
    `SerrePositivity.HomologicalAlgebra.Cech.Composition,
    `SerrePositivity.BhattScholze.Prismatic.PolynomialFrobeniusCech,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.FiniteEtalePerfectoid,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCardinality,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDP,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBaseChange,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBasis,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPFactorial,
    `SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction,
    `SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeMaps,
    `SerrePositivity.BhattScholze.Prismatic.AffinePolynomial,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDelta,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaBounds,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaFlat,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaResidue,
    `SerrePositivity.BhattScholze.Prismatic.Envelope,
    `SerrePositivity.BhattScholze.Prismatic.PrismOver,
    `SerrePositivity.BhattScholze.Prismatic.VariableEnvelope,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedCoefficient,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge,
    `SerrePositivity.CommutativeAlgebra.DeRham.Graded,
    `SerrePositivity.CommutativeAlgebra.DeRham.Polynomial,
    `SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion,
    `SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz,
    `SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinCochains,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.PrincipalShortExact,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.ShortExact,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless mods.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "BS stage II: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "BS stage II: no declarations audited"
  logInfo m!"BS stage II audit passed: {count} declarations, standard three axioms only."
