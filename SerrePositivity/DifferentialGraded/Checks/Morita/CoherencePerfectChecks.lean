module
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Coherence
public import SerrePositivity.DifferentialGraded.Checks.Morita.CriterionChecks

/-! # 既存Perf作用比較の単位・結合coherenceの監査

## 概要
既存Perf合成比較の左右単位・結合の図式を、U16a・c統合と同時に検証する。

## 方針
新しい比較を仮定せず、既存公開比較そのものの型と公理依存を検査する。

## 規約と注意
係数変更の残る3接続と中心作用の受入は含まない。

## 使われ方
U16d担当が主導来作用のcoherenceのPerf移送を再利用する入口。
-/
@[expose] public section
open SerrePositivity.DifferentialGraded.Morita

#check perfectKernelCompositionIso_rightUnit
#check perfectKernelCompositionIso_leftUnit
#check perfectKernelCompositionIso_associator
#print axioms perfectKernelCompositionIso_rightUnit
#print axioms perfectKernelCompositionIso_leftUnit
#print axioms perfectKernelCompositionIso_associator
