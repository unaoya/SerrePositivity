module

public import SerrePositivity.KST.Comparison.DoldKanGL
public import SerrePositivity.KST.Comparison.ComponentSubcomplex
public import SerrePositivity.KST.Comparison.DGAlgebra
public import SerrePositivity.KST.Comparison.GammaH0Ring
public import SerrePositivity.KST.Comparison.ConnectiveTruncation
public import SerrePositivity.KST.Comparison.GrouplikeGL
public import SerrePositivity.KST.Comparison.RegularBar
public import SerrePositivity.KST.Comparison.BarEdge
public import SerrePositivity.KST.Comparison.RegularBarContraction
public import SerrePositivity.KST.Comparison.GrouplikeTranslations
public import SerrePositivity.KST.Comparison.BarSegal
public import SerrePositivity.KST.Comparison.RegularBarFiber
public import SerrePositivity.KST.Comparison.RegularBarLoop
public import SerrePositivity.KST.Comparison.GroupCompletionSpace
public import SerrePositivity.KST.Comparison.ActionBarCoordinates
public import SerrePositivity.KST.Comparison.HomotopyPullback
public import SerrePositivity.KST.Comparison.FibrantPullbackComparison
public import SerrePositivity.KST.Comparison.ParametrizedTranslations
public import SerrePositivity.KST.Comparison.TranslationDescent
public import SerrePositivity.KST.Comparison.ReplacementComparison
public import SerrePositivity.KST.Comparison.AlternativePullback
public import SerrePositivity.KST.Comparison.ActionBarSquares
public import SerrePositivity.KST.Comparison.HornPreimage
public import SerrePositivity.KST.Comparison.KanAnodyneBaseChange
public import SerrePositivity.KST.Comparison.KanBasePullback
public import SerrePositivity.KST.Comparison.HomotopyPullbackInvariance
public import SerrePositivity.KST.Comparison.ExInfinity
public import SerrePositivity.KST.Comparison.ExComplexity
public import SerrePositivity.KST.Comparison.SubdivisionDegeneracy
public import SerrePositivity.KST.Comparison.SubdivisionCommutation
public import SerrePositivity.KST.Comparison.ExPairingStep
public import SerrePositivity.KST.Comparison.ExDoublePairing
public import SerrePositivity.KST.Comparison.SubdivisionFaceDegeneracy
public import SerrePositivity.KST.Comparison.SubdivisionFrontFace
public import SerrePositivity.KST.Comparison.SubdivisionFrontDegeneracy
public import SerrePositivity.KST.Comparison.SubdivisionRearDegeneracy
public import SerrePositivity.KST.Comparison.ExPairingNondegenerate
public import SerrePositivity.KST.Comparison.ExPairingProperness
public import SerrePositivity.KST.Comparison.ExPairingCore
public import SerrePositivity.KST.Comparison.ExInfinityAnodyne
public import SerrePositivity.KST.Comparison.NerveChainsLastVertex
public import SerrePositivity.KST.Comparison.DoubleSubdivisionHornMap
public import SerrePositivity.KST.Comparison.HornChainBoundary
public import SerrePositivity.KST.Comparison.HornSubdivisionLastVertex
public import SerrePositivity.KST.Comparison.SubdivisionLastVertexSimplex
public import SerrePositivity.KST.Comparison.DoubleSubdivisionHornBoundary
public import SerrePositivity.KST.Comparison.ExInfinityKan
public import SerrePositivity.KST.Comparison.ExInfinityLocalization
public import SerrePositivity.KST.Comparison.ExInfinityGrouplike
public import SerrePositivity.KST.Comparison.ExInfinityBar
public import SerrePositivity.KST.Comparison.KanBarRows
public import SerrePositivity.KST.Comparison.DoubleMappingCylinderMap
public import SerrePositivity.KST.Comparison.SliceFiberPushouts
public import SerrePositivity.KST.Comparison.CylinderBoundary
public import SerrePositivity.KST.Comparison.DoubleMappingCylinderEquivalence
public import SerrePositivity.KST.Comparison.StrictPushoutCube
public import SerrePositivity.KST.Comparison.StrictCylinderPullbacks
public import SerrePositivity.KST.Comparison.HornFaceInclusionAnodyne
public import SerrePositivity.KST.Comparison.HornSimplexFaceFactorization
public import SerrePositivity.KST.Comparison.ArbitraryBasePullback
public import SerrePositivity.KST.Comparison.ExInfinityHomotopyPullback
public import SerrePositivity.KST.Comparison.StrictCylinderHomotopyPullbacks
public import SerrePositivity.KST.Comparison.KanReplacementSquares
public import SerrePositivity.KST.Comparison.CommonTrivialRefinement
public import SerrePositivity.KST.Comparison.TrivialFibrationExtension

public import SerrePositivity.KST.Comparison.SpanGluing

public import SerrePositivity.KST.Comparison.SimplicialSumHomotopyPullbacks

/-!
# K-L2：比較定理の入口

概要：KST §2 の比較定理に向けた宣言を公開する。
方針：SS03 (2.9) の AW 環、π₀ の環、KST 式 (2.2) の単体的モノイドを公開する。
規約：π₀ĜL の群性と Γ と H⁰ の環比較を証明する。群完備化、H_*、plus、K の比較は残工程。
使われ方：K-L2 の対象ビルドと公理監査。比較定理の完成を主張する入口ではない。
-/
