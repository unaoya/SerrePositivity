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
- 並行作業による停止基準は Core 自身の import 閉包内の破損のみ。
  各保存単位は Core の対象ビルドと `scripts/audit_infinity_core.lean` で検証する。
  全体ビルドは A2 全体の完了等の区切りで行い、他レーンの編集中ファイルでの失敗は
  記録のみとし、α の作業の停止理由にはしない（2026-10-17 のユーザー指示）。

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

### 承認後の追加要件（2026-10-17）

設計 §4 は維持する。単体の ext 補題で切断の命題的等式と左右の cast を扱い、
これを先に実装してから `simplexMap` の合成則を示す。
A2a に部分複体の join を含め、`A₀ ≤ A`・`B₀ ≤ B` に対する
`A₀ ⋆ B` と `A ⋆ B₀` を `A ⋆ B` の部分複体として構成する。
A2c の pushout-join の始域はこの二つの部分複体の和とする。

A2b は任意の単体集合 A に対する普遍性

```text
(A ⟶ sliceOver p) ≃ {F : join A K ⟶ X // joinInr A K ≫ F = p}
```

と coslice の双対を含む。各単体 a の `σ_a : join Δ[dim a] K ⟶ X` を
`F(ℓ,a,k) := σ_a(ℓ,id,k)` により束ねる直接構成を使い、余極限の一般論は使わない。
A2a 完了、A2b 完了、A2c の順に進める。
A2c・A2h は正確な文言を原典と照合してこの README に記録・報告してから実装する。
その報告後の追加承認は不要。

## 検証と現在の範囲

A1a の比較同値、A1b の関手性・自然性、A1c のホモトピーからの自然変換を実装。
A1d の通常の圏の nerve での具体化も実装。A1a〜A1d・A2a は完了、A2b 以降は未完了。
対象ビルド後、`lake env lean scripts/audit_infinity_core.lean` で
全ての明示的公開宣言の型と公理を確認する。

A2a は完了。`Join.Simplex.ext` は切断の等式に伴う左右の cast を明示する。
`simplexMap` の恒等・合成則から `join : SSet → SSet → SSet` を構成済み。
`joinInl`・`joinInr`、`joinMap` とその恒等・合成・単射性・包含との整合性を実装した。
`joinSubcomplexLeft`・`joinSubcomplexRight` は、単射な joinMap の像による部分複体。
`joinUnion` はその和で、各像と元の join との同型および包含との整合性も実装済み。
`emptyJoinIso A L` は、任意の A の空部分複体と L の join が L と同型であることを与える。

`joinStdSimplexIso i j : join Δ[i] Δ[j] ≅ Δ[i+j+1]` を構成した。
`stdAugEquiv` と `concat` で次数ごとの単体を連結した順序写像に表示し、
逆像の切断から復元して単射・全射・単体作用との可換性を証明している。
A2a の直接構成・包含・射への作用・標準単体の同型・空 join の同型・部分複体の join は完了。
A2b の slice・coslice・射影・普遍性、A2c 以降は未実装。
累計 78 明示的公開宣言と生成された整合性補題 2 件、計 80 件を公理監査する。
