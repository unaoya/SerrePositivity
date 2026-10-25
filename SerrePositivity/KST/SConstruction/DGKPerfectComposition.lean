module
public import SerrePositivity.KST.SConstruction.DGKPerfectCompositionGeneral
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaEquivalence

/-!
概要：固定 dg 入力の元の主 Perf 延長の合成比較を従来の入口から公開する。
方針：dg 一般入口を public import し、従来の Morita 依存も公開したまま保つ。
規約：既存宣言の名前・型・証明は DGKPerfectCompositionGeneral に保持する。
使われ方：既存の S• 下流の互換入口。D 側は dg 一般入口を直接 import する。
-/
