module
public import SerrePositivity.KST.Fibration.Relative.FiniteCoordinates
public import SerrePositivity.KST.Fibration.Relative.CoordinatePostcomp
public import SerrePositivity.KST.Fibration.Relative.ConnectiveInterface
public import SerrePositivity.KST.Fibration.Relative.ClosedStableAll

/-!
概要：K-6 b の相対加法性と S-1 (c) の無条件の閉部分圏 fiber 界面を集約する。
方針：有限座標・単回 fiber・相対核四角形と、無条件 S1 の四つの実データを公開する。
規約：局所化圏値の有限比較から SSet の実現同値を推論しない。
使われ方：K-6 の集約と監査で b の供給を消費し、NonConnective の逆向き import を避ける。
-/
