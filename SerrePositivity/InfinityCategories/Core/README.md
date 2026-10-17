# quasicategory の一般論

## 概要

Mathlib の `SSet.Quasicategory` をそのまま用いる。
正本は [計画](../../../formalization-plans/infinity-core.md) §1〜§4。
HTT §1.2.3、Kerodon [Construction 1.4.5.1](https://kerodon.net/tag/004A) と
[Proposition 1.4.5.7](https://kerodon.net/tag/004H) に沿って、
辺のホモトピー類と道の商という二つのホモトピー圏を比較する。

## Conventions

- namespace は `SerrePositivity.InfinityCategories`。
- docstring は「概要／方針／規約／使われ方」の日本語で、主張・前提・証明方針・原典番号を書く。
- 合成の順序は Mathlib の `≫`。左ホモトピーを辺の商に用いる。
- `pathToEdgeHomotopyCategory` と `edgeToPathHomotopyCategory` は
  任意の二切断 quasicategory に対し定義する。比較同値は完全な単体集合に特殊化する。
- 追加公理・引用・`sorry` は使わない。Joyal モデル構造や ∞ 局所化には依存しない。
- join は直接構成する。slice の単体は join からの射の型で表す予定だが、
  A2a・A2b の具体的設計はまだ確定していない。

## 検証と現在の範囲

A1a の比較同値、A1b の関手性・自然性、A1c のホモトピーからの自然変換を実装。
A1d と A2 は未完了。
対象ビルド後、`lake env lean scripts/audit_infinity_core.lean` で
全ての明示的公開宣言の型と公理を確認する。
