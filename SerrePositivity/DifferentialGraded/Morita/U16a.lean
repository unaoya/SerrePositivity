module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionDerived
public import SerrePositivity.DifferentialGraded.Morita.CoherenceLeftUnitMain

/-! # U16a：主導来kernelの作用・随伴・単位と結合の整合性

## 概要
任意kernelの主導来作用、実際の右随伴とunit/counit、恒等・合成比較とcoherenceを公開する。

## 方針
準同型局所化上の既存作用と、telescopeから構成した右随伴を一つの入口へまとめる。

## 規約と注意
任意可換環・非有界複体・独立対象宇宙。作用・随伴には局所Hom条件不要。
合成・単位・結合の図式のlocalHomKFlatは各定理に明示し、一般分解変更は含まない。

## 使われ方
U16cの実際の右随伴との統合と、U16dのPerf制限へのcoherence移送。
-/
