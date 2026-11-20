module

public import SerrePositivity.Spectra.General.CotensorEvaluation
public import SerrePositivity.Spectra.General.CotensorMapLevels
public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.Simplicial
public import SerrePositivity.Spectra.General.Suspension

/-!
# モデル構造を選ぶ前の対称スペクトルの基盤

段階1の基点付き単体的集合による整合的な作用と、段階2の写像対象、
単体的豊穣構造、tensor・cotensor、懸垂・ループ、構造射の随伴表示の入口。
基点付きの豊穣構造は、忘却関手に沿って既存の圏構造とともに移送できる。

通常の随伴、三変数に自然なHom同値、Δ[0]の単位、直積の反復比較とその自然性、
各段の通常のsmash・内部Homとの一致を公開する。
モデル構造、導来演算、安定ホモトピー群、次数シフトは次の検討に残す。

利用するAPIは `SymmetricSpectrum/README.md`、受入条件との対応は
`formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17` の段階2の最終確認に記載する。
-/
