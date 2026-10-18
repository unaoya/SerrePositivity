module

public import SerrePositivity.KST.Descent.Axioms
public import SerrePositivity.KST.Descent.Transfer
public import SerrePositivity.KST.Descent.RationalFixedPoints

/-!
# K-L8：論文 §3 の降下

## 概要
定理 3.1 の全次数 π_* 比較と、その証明に用いる代数的な基礎を集約する。

## 方針
係数つき次数付き前層、有限平坦 transfer の有理分裂、(3.8) の置換不変部分を公開する。

## 規約
最小公理 (1)–(8)、Čech 降下、主定理の証明、E の実現は未完成。
通常の不変部分を hG と呼ばず、次数ごとの極限を Tot と呼ばない。

## 使われ方
K0・T2 と L9 の導来値域に接続する L8 専用の入口。
-/
