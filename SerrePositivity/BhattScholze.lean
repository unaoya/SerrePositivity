module

public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaTensor
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismTensor
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismResidueTensor
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedBaseChange
public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Excision
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
public import SerrePositivity.BhattScholze.Almost.SupportedQuotient
public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.BhattScholze.Andre.Transfinite.Basic
public import SerrePositivity.BhattScholze.Andre.Variants.MonicRootedExtension
public import SerrePositivity.BhattScholze.Andre.Remark715.Unoriented

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
