module

public import SerrePositivity.CommutativeAlgebra.PerfectTorIndependence.Basic

/-!
# 完全標数 p 環の Tor 独立性の公開入口

## 概要
BS 著者版 Lemma 10.3（印刷 pp.78–79）で必要となる完全環の正次数 Tor 消滅を公開する。

## 方針
`Basic` が既存の自由完全多項式代数と Tor 底変換の証明を指定の型へ接続する。

## 規約
Mathlib の `Tor (ModuleCat.{u} A) i` を用い、三環の標数と完全性を明示する。

## 使われ方
ルートの集約ファイルと、完全環の Tor 独立性を必要とするレーンから読み込む。
-/
