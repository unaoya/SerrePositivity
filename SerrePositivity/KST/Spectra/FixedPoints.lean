module

public import SerrePositivity.KST.Spectra.PointedHomotopyLimitInvariance

public import SerrePositivity.KST.Spectra.GroupAction
public import SerrePositivity.KST.Spectra.FixedPointLevels
public import SerrePositivity.KST.Spectra.FiniteGroupAveraging
public import SerrePositivity.KST.Spectra.RationalGroupCohomology

/-!
概要：群作用・hG と Tot の段ごとの Kan 構成および有理平均化の集約。
方針：作用図式の点つき Bousfield–Kan end と有限群の係数の計算を分けて構成する。
規約：L9e は進行中。BF 構造と有理 Shapiro の π_* 比較は後続で証明する。
使われ方：BF 1978 §2、HA §1.4.2。有限群作用の固定点の構成。
-/
