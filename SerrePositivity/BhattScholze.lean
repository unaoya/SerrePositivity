module

public import SerrePositivity.BhattScholze.Perfectoid.FiniteProduct
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaTensor
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismTensor
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismResidueTensor
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedBaseChange
public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Excision
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechMilnor
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechOverlap
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCechUltraproduct
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcIntervalOverlap
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorDetection
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcMilnorTensor
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectCech
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationProduct
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.FiniteEtalePerfectoid
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCardinality
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite
public import SerrePositivity.BhattScholze.Prismatic.PolynomialFrobeniusCech
public import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDP
public import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBaseChange
public import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBasis
public import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPFactorial
public import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction
public import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeMaps
public import SerrePositivity.BhattScholze.Prismatic.AffinePolynomial
public import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDelta
public import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaBounds
public import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaFlat
public import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaResidue
public import SerrePositivity.BhattScholze.Prismatic.Envelope
public import SerrePositivity.BhattScholze.Prismatic.PrismOver
public import SerrePositivity.BhattScholze.Prismatic.VariableEnvelope
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
public import SerrePositivity.BhattScholze.Almost.SupportedQuotient
public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.BhattScholze.Andre.Transfinite.Tower
public import SerrePositivity.BhattScholze.Andre.Variants.MonicRootedExtension
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Initiality

/-!
# Bhatt–Scholze の形式化の集約

## 概要
所有範囲外（root の `SerrePositivity.lean`、`scripts/audit_f5.lean`・`audit_f7.lean`）が BS を読み込むための唯一の入口。
2026-10-25 時点で root が個別に import していた BS のモジュール（32 行）を、整理後の名前で 15 本にまとめたもの。

## 方針
BS の中でモジュールを移したりまとめたりしたときは、このファイルだけを直す。所有範囲外の import は変わらないので、転送スタブは要らない。

## 規約
宣言は持たない。BS の全モジュールではなく、root が読み込んでいた範囲（主定理の経路と、選ばれた照合・変種）だけを入れる。

## 使われ方
root の `SerrePositivity.lean`、`scripts/audit_f5.lean`・`audit_f7.lean`（進捗確認チャットが書き換えた後）。
-/
