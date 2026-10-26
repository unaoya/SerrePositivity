module
public import SerrePositivity.KST.Fibration.Relative.FiniteCoordinates
public import SerrePositivity.KST.Fibration.Relative.CoordinatePostcomp
public import SerrePositivity.KST.Fibration.Relative.AdditivityFiber
public import SerrePositivity.KST.Fibration.Relative.SingleStageDetection
public import SerrePositivity.KST.Fibration.Relative.ConnectiveInterface
public import SerrePositivity.KST.Fibration.Relative.CanonicalSingleStageDetection
public import SerrePositivity.KST.Fibration.Relative.CanonicalFixedSourceFiber
public import SerrePositivity.KST.Fibration.Relative.CanonicalSuspensionInput
public import SerrePositivity.KST.Fibration.Relative.ConnectiveFibrationTheorem
public import SerrePositivity.KST.Fibration.Relative.ConnectiveFibration

/-!
概要：K-6 b の相対構成と d の単回検出・固定始点比較の集約。
方針：同じ canonical 比較を元の実 fiber と非負次数 π へ接続する。
規約：NonConnective を読む d の葉は主 Fibration 集約から分離する。
使われ方：b・d の対象ビルドと専用監査、K-B3 への公開入力。
-/
