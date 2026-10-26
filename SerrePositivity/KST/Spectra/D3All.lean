module

public import SerrePositivity.KST.Spectra.SpectrumFiniteLimits
public import SerrePositivity.KST.Spectra.AdjointLoopRelativeDiagramResolution
public import SerrePositivity.KST.Spectra.D3LoopConeRelativeLifting
public import SerrePositivity.KST.Spectra.D3ComparisonHomLifting

/-!
概要：Sp-2 の d3 専用集約。
方針：有限極限・採用済みの全 Hom 比較・指定図式基底と新しい比較充填を集める。
規約：既存 Spectra 集約を変更しない。nativeLoop の同値性と安定性は未提供。
使われ方：K-7 d3 の独立したビルド・公理監査入口。
-/
