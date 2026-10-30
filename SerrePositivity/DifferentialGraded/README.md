# DifferentialGraded：dg 理論の入口

## 概要

任意の可換環上の非有界複体から、dg 圏・dg 加群、導来圏、相対テンソル、
perfect 加群、dg 商、Morita 理論までを扱う。Morita（U16）、Verdier 商の比較（U17）、
Perf の実装は完成している。一般の射影モデル構成を扱う U12e-general は中断中であり、
局所条件のもとで完成した経路と区別する。

本番 API の入口は [DifferentialGraded.lean](../DifferentialGraded.lean)。
StageOne〜StageEight の入口は退役し、この集約に置き換えた。

## 方針

| ディレクトリ | 内容 |
| --- | --- |
| Complexes・Category・Functor | 複体の閉対称モノイダル構造、dg 圏と dg 関手 |
| Module・Bimodule・Tensor | dg 加群、双加群、Hom と balanced tensor、単位・結合の整合性 |
| Derived・Resolution | 導来局所化、導来 Hom・テンソル、解像度と比較 |
| Perfect・Endomorphism | perfect・compact 加群、小さい増強と自己準同型の表示 |
| Quotient・Morita・Verdier | dg 商、Morita 同値、Verdier 商と三角構造の比較 |
| Presentation | dg 圏の表示とその構成 |
| Checks | 型照合・example・受入の検査 |

本番の集約は検査と Archive を import しない。全宣言の公理監査は
`scripts/make_area_audits.py` が追跡中のモジュールから生成する `scripts/audit/dg.lean` を使う。
中断した U12e-general の検査は
[Archive/DifferentialGraded/Checks/U12e](../Archive/DifferentialGraded/Checks/U12e/) に全文を保存し、
監査・集約・通常のビルド対象には含めない。

## 規約

- 環は任意の可換環。複体は非有界で、追加の有限性・平坦性・small 性は各 API の仮定に明示する。
- 微分はコチェイン次数 +1、ホモトピーは次数 −1。原論文のホモロジー次数 i はコチェイン次数 −i に対応する。
- 環と Hom 加群の宇宙と、dg 圏の対象の宇宙を区別する。既存の仮定・宇宙・符号規約を維持する。
- Mathlib の豊穣圏の構造と既存の複体・局所化・三角圏の API を再利用する。
- U12e-general の個別の証明済み API と、一般経路全体の未受入を区別する。
- `Verdier/ChecksU17Integration` と `Verdier/ChecksOrderSquare` は D3 の移設まで現在の場所に保持する。

## 使われ方

本番入口と受入検査：

```sh
lake build SerrePositivity.DifferentialGraded
lake build SerrePositivity.DifferentialGraded.Checks.StageSeven SerrePositivity.DifferentialGraded.Checks.StageEight
lake build SerrePositivity.DifferentialGraded.Checks.U12eLocal SerrePositivity.DifferentialGraded.Checks.Morita.U16Checks
lake build SerrePositivity.DifferentialGraded.Verdier.ChecksU17Integration
```

監査の import 先を先にビルドしてから、監査を実行する：

```sh
lake build $(grep '^import ' scripts/audit/dg.lean | sed 's/^import //')
lake env lean scripts/audit/dg.lean
```

監査の再生成はリポジトリルートで `python3 scripts/make_area_audits.py` を実行する。
このスクリプトは他領域の監査も生成するため、所有範囲外の差分を混入させない。
整理の範囲と受入条件は [DG-W1](../../formalization-plans/dg-codex-w1.md)、
中断経路の再開条件は [U12e の目録](../../formalization-plans/dg-theory-u12e-general-inventory.md) を参照する。
