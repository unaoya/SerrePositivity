module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiPDComparison
public import SerrePositivity.BhattScholze.Andre.PrincipalDPPositiveUniversal

/-!
# André R1：原典の R/ϖ 無限根環上の pd 比較の入口

## 概要

R/ϖ 上のモニック入力の実分冪構造と入力公式には、prism 商の p 正則性を要しない版を使う。
BS Rem 7.15(1)（著者版 p.62）の台環・標準入力を保つ比較を読み込む。

## 方針

旧 hpR 付きの構造・入力公式を削除した。
無条件版は Unconditional.MonicPDEnvelope の射影的係数商による実構造を使い、集約から公開する。
原典の p ねじれなしへの帰着とは異なる線形切断・構造移送による経路。

## 規約

比較の台環・係数作用・正次数イデアルを保持する。
依存順序を保つため、この入口から後続の無条件版を import しない。

## 使われ方

旧ファイルの import 経路を保ち、標準表示の同型と一般の実 pd 普遍性を供給する。
-/
