module

public import SerrePositivity.KST.Spectra.PointedWeightedEndFunctor
public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitMap
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitMap
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitNaturality
public import SerrePositivity.KST.Spectra.FixedPointNaturality

public import SerrePositivity.KST.Spectra.InternalHomExchangeUnit
public import SerrePositivity.KST.Spectra.PointedWeightedCone
public import SerrePositivity.KST.Spectra.PointedWeightedConeCompatibility
public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitCone
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitCone
public import SerrePositivity.KST.Spectra.FixedPointUnit

public import SerrePositivity.KST.Spectra.PointedWeightedEndMap
public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit
public import SerrePositivity.KST.Spectra.FixedPointSpectra

public import SerrePositivity.KST.Spectra.EndInternalHom
public import SerrePositivity.KST.Spectra.EndRightAdjoint
public import SerrePositivity.KST.Spectra.FreePointedHom
public import SerrePositivity.KST.Spectra.FreePointedHomRestriction
public import SerrePositivity.KST.Spectra.PointedWeightedEnd
public import SerrePositivity.KST.Spectra.PointedWeightedEndCotensor

public import SerrePositivity.KST.Spectra.PointedHomotopyLimitInvariance

public import SerrePositivity.KST.Spectra.GroupAction
public import SerrePositivity.KST.Spectra.FixedPointLevels
public import SerrePositivity.KST.Spectra.FiniteGroupAveraging
public import SerrePositivity.KST.Spectra.RationalGroupCohomology

/-!
概要：群作用・hG と Tot の段ごとの Kan 構成および有理平均化の集約。
方針：作用図式の点つき Bousfield–Kan end と有限群の係数の計算を分けて構成する。
規約：L9e は進行中。BF 対象を含むが、有理 Shapiro と通常の Tot の比較は後続で証明する。
使われ方：BF 1978 §2、HA §1.4.2。有限群作用の固定点の構成。
-/
