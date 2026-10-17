module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameterRelative

/-!
# 中断した厳密化モジュールの互換入口

## 概要
旧importを維持するため、移動した専用モジュールを再公開する。
公開宣言の名前空間・型・証明は移動先に保持する。

## 方針（定義・証明）
Rectification配下の対応するモジュールをpublic importする。
このファイルに定義や証明を重複させない。

## 規約と注意
任意モデル源への一般化は引き続き中断中である。
一般道具はGeneralToolsまたは共有Foundationsから利用する。

## 使われ方
既存の個別importはそのまま利用できる。
新しい専用コードではRectification配下の正規パスを利用する。
対応表はscripts/homotopical_generalization_manifest.jsonを参照。
-/
