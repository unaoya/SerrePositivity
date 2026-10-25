module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootVarpiPrimeFrobeniusPD
public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalDPTransport
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpiNativePDEnvelope

/-!
# André R1：mod p 入力の分冪構造の移行用 import

## 概要

元の mod p 入力に関する係数比較の import を保持する。BS Rem 7.15(1)（著者版 p.62）。

## 方針

旧 hpR 付き3宣言を削除し、`Unconditional/MonicPDEnvelope.lean` の同名の
`_of_unconditional` 版を集約から公開する。原典とは異なる射影的係数商と構造移送の経路。

## 規約

モニック入力・同じ mod p 入力・同じ指定イデアルを保持し、正次数を追加しない。

## 使われ方

既存の import 経路と係数比較を維持し、実 Frobenius 引戻しに無条件の分冪構造を適用する。
-/
