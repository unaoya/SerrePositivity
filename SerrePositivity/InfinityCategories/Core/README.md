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
- join は直接構成する。Day 畳み込みは使わない。

## A2a・A2b の設計（2026-10-17）

頂点数 `r : ℕ` に対し `augObj K 0 := PUnit`、
`augObj K (r+1) := K _⦋r⦌` と定める。負の次数を自然数の頂点数で表す。
join の n 単体は厳密に

```text
Σ ℓ : Fin (n+2), augObj K ℓ.val × augObj L (n+1-ℓ.val)
```

とする。計画の切断位置 `k` との対応は `ℓ=k+1`。
`α : [m] → [n]` での引き戻しの切断位置は
`ℓ' = #{i : Fin (m+1) | α(i) < ℓ}`。
単調性によりこの逆像は先頭の `ℓ'` 頂点からなる。
制限 `Fin ℓ' → Fin ℓ` と、残りの区間の制限
`Fin (m+1-ℓ') → Fin (n+1-ℓ)` に沿って二つの因子を引き戻す。
片方の区間が空なら、`augObj K 0` の一点に写す。
`ℓ=n+1` と `ℓ=0` がそれぞれ左右の包含に対応する。

`p : K ⟶ X` に対する slice の n 単体は次の部分型とする。

```text
{σ : join Δ[n] K ⟶ X // joinInr Δ[n] K ≫ σ = p}
```

`α : [m] → [n]` の作用は `joinMap (stdSimplex.map α) (𝟙 K)` との前合成。
射影の n 成分は `joinInl Δ[n] K ≫ σ : Δ[n] ⟶ X` を
`SSet.yonedaEquiv` で X の n 単体に直す。
coslice は `{σ : join K Δ[n] ⟶ X // joinInl K Δ[n] ≫ σ = p}`。
頂点の場合は `K=Δ[0]`、`p=SSet.yonedaEquiv.symm x` を用いる。

この節は型と実装方針の設計であり、join・slice の Lean 実装の完成を意味しない。
A2c・A2h の anodyne 性の正確な文言と証明は未着手。

## 検証と現在の範囲

A1a の比較同値、A1b の関手性・自然性、A1c のホモトピーからの自然変換を実装。
A1d の通常の圏の nerve での具体化も実装。A1a〜A1d は完了、A2 は未完了。
対象ビルド後、`lake env lean scripts/audit_infinity_core.lean` で
全ての明示的公開宣言の型と公理を確認する。

A2a の前段階として `Join.lean` に `augObj`・`augMap` とその恒等・合成則、
次数ごとの型 `Join.Simplex`、切断の逆像 `pullCut` とその特徴づけ・恒等・合成則、
左右の制限写像 `leftMap`・`rightMap`、次数ごとの作用 `simplexMap` を実装した。
`simplexMap` 自身の関手法則は未証明で、`join : SSet → SSet → SSet` はまだ未構成。
包含・標準単体の同型・空 join の同型・射への関手性・slice は未実装。
前段階の 14 宣言を含む累計 30 宣言を監査し、全て標準三公理のみ。
