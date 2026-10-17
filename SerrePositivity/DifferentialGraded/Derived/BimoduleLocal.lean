module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagon
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionTriangleFamily
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionValueNaturality

/-! # U12e-local：局所Hom K-flat条件下の全導来bimodule合成

## 概要
固定した小さいdg圏の主導来bimodule圏上の合成・単位・結合子とcoherenceの独立入口。

## 方針
指定準同型局所化と右相対K-flat置換による既存の構成・計算定理を公開する。

## 規約と注意
係数は任意可換環、複体は非有界。各対象型にSmall.{u}を明示し、
合成の出力Homに必要なlocalHomKFlatを要求する。dg圏の分解変更のcoherenceは含めない。

## 使われ方
Moritaの局所版とChecks.U12eLocalから利用する。一般分解の入口Resolution.Generalは経由しない。
受入表と中断した一般経路は`formalization-plans/dg-theory-m5-status.md`を参照。
-/
