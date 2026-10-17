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
各工程を報告したら承認を待たずに次へ進む。停止するのは A2 全体の完了、
§4 に関わる設計変更の提案、Core の import 閉包内の並行作業による破損の場合のみ。
A2c・A2h は正確な文言を原典と照合してこの README に記録・報告してから実装する。
その報告後の追加承認は不要。

## 検証と現在の範囲

A1a の比較同値、A1b の関手性・自然性、A1c のホモトピーからの自然変換を実装。
A1d の通常の圏の nerve での具体化も実装。A1a〜A1d・A2a〜A2b は完了、A2c 以降は未完了。
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
A2b の slice・coslice・射影・頂点上の特殊化と curry を実装した。
`sliceOverEquiv` は任意の単体集合 A に対する slice 側の普遍性を与える。
逆写像は各単体の錐を直接評価して束ね、自然性と両逆関係まで証明した。
`Coslice.lean` の `sliceUnderEquiv` で coslice 側の普遍性も直接構成した。
右単体に付いた錐を `(k,id)` で評価し、自然性・固定条件・両逆関係を証明している。
A2b は完了。A2c 以降は未完了。
累計 120 明示的公開宣言と生成された整合性補題 2 件、計 122 件を公理監査する。

## A2c：pushout-join の正確な文言（2026-10-17、実装前の照合）

原典は [HTT Lemma 2.1.2.3](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
（印刷頁 62）と [Kerodon Proposition 4.3.6.4](https://kerodon.net/tag/018J)。
両者の向きは一致する。A₀ ≤ A、B₀ ≤ B に対し、
`U := joinUnion A₀ B₀ = (A₀ ⋆ B) ∪ (A ⋆ B₀)` と置く。
包含 `U.ι : U ⟶ A ⋆ B` は、次のいずれかの仮定で inner anodyne である。

1. **左因子の包含** `A₀.ι` が **right anodyne**（右因子の包含は任意の単射）。
2. **右因子の包含** `B₀.ι` が **left anodyne**（左因子の包含は任意の単射）。

right anodyne は `Λ[p,i] ⟶ Δ[p]`、`p≥1`・`0<i≤p` で生成される
弱飽和クラス。left anodyne は `p≥1`・`0≤i<p` のホーンで生成される弱飽和クラス。
Lean ではそれぞれのホーンの rlp の llp として定義し、追加のモデル構造は使わない。

基本セルは次の二つで、ともに標準単体の join の同型を通じた内ホーンになる。

- 左が `Λ[p,i]`（`0<i≤p`）、右が `∂Δ[q]`（`q≥0`）なら、
  和の部分複体は `Λ[p+q+1,i]`。欠けた頂点 i は全頂点集合の内点。
- 左が `∂Δ[p]`（`p≥0`）、右が `Λ[q,j]`（`0≤j<q`）なら、
  和の部分複体は `Λ[p+q+1,p+1+j]`。欠けた頂点 p+1+j は全頂点集合の内点。

証明はこれらのホーン・境界セルの計算と、境界包含による単射のセル分解、
ホーン生成クラスの lifting property による弱飽和閉包を用いる方針。
Mathlib の `rlp_monomorphisms` は単射の境界セル分解により証明されており、
このセル分解を利用できる。slice・coslice の直接構成した普遍性で持ち上げ問題を移す。
この節は証明する文言の固定であり、A2c の Lean 証明の完成を意味しない。
A2h の文言の固定と実装はまだ行っていない。

A2c の生成セル二つを `JoinAnodyne.lean` に実装済み。
`joinUnion_rightHorn_boundary_innerAnodyne` と
`joinUnion_boundary_leftHorn_innerAnodyne` は各和の包含の inner anodyne 性を与える。
一般の単射・anodyne 射への閉包は未完了であり、A2c 全体は未完了。
対象ビルドと累計 148 件の公理監査は成功。正確な型・前提は計画 §6 に記録した。

### A2c 完了（2026-10-18）

`JoinAnodyne.lean` の `joinUnion_innerAnodyne_of_rightAnodyne` と
`joinUnion_innerAnodyne_of_leftAnodyne` により、固定した文言の一般形を証明した。
`JoinCells.lean` の生成セルを、`JoinLifting.lean` の pushout と相対 slice・coslice の
持ち上げ問題の往復、単射の境界セル分解を用いて一般の射へ広げている。
A2c まで完了、A2d〜A2i は未完了。Core 対象ビルドと累計 192 件の公理監査は成功。
新規 44 公開宣言の正確な型と仮定は計画 §6 に列挙した。

### A2d 完了（2026-10-18）

`RightFibration.lean` で左右のホーンの rlp を `rightFibrations`・`leftFibrations` として定義した。
`RightFibration`・`LeftFibration` は所属の型クラスで、両方から `InnerFibration` へ接続する。
`[Quasicategory X]` と任意の `p : K ⟶ X` に対し、
`sliceOverProjection_rightFibration` と `sliceUnderProjection_leftFibration` が射影の性質を与え、
`sliceOver_quasicategory`・`sliceUnder_quasicategory` が Mathlib の標的からの引き戻し補題で
quasicategory 性を与える。A2d 完了、A2e〜A2i は未完了。
Core 対象ビルドと累計 216 件の公理監査は成功。型・仮定は計画 §6 に記録した。

### A2e 完了（2026-10-18）

`IsTerminalVertex` は最後の頂点を固定した全正次元の境界の充填、
`IsInitialVertex` は最初の頂点を固定する双対である。
`isTerminalVertex_iff_trivialKanFibration` と `isInitialVertex_iff_trivialKanFibration` が
slice/coslice 射影の trivial Kan fibration 性との同値を、任意の単体集合について与える。
`trivialKanFibrations` は単射の rlp として定義した。モデル構造は使わない。
`[Quasicategory X]` に対する `terminalVertexIso`・`initialVertexIso` は、
それぞれ二つの終対象・始対象の `hoFunctor.obj X` での同型を与える。
片側逆射を二回作り、二単体が与える合成関係から両側逆射に直す証明である。
A2e 完了、A2f〜A2i は未完了。Core ビルドと累計 271 件の公理監査は成功。
新規 55 件の正確な型・前提は計画 §6 に記録した。

### A2f 完了（2026-10-18）

`Limit.lean` の `JoinCone p` は固定条件付きの射 `Δ[0]⋆K ⟶ X` の型で、
定義上 slice の零単体。`IsLimitCone c` は slice の終対象の充填条件、`HasLimit p` はその存在。
`limitConeIso` は h(slice) での一意性、`limitVertexIso` は hX での頂点の同型を与える。
同型の仮定は X が quasicategory であることと両錐の極限性。
A2f 完了、A2g〜A2i は未完了。Core ビルドと累計 279 件の公理監査は成功。
全公開宣言の型・前提は計画 §6 に記録した。

## A2h：始対象による制限の正確な文言（2026-10-18、実装前の照合）

原典は [Kerodon Corollary 4.3.6.14](https://kerodon.net/tag/018L)、
[Corollary 4.7.3.22](https://kerodon.net/tag/02H6) の左右双対、
[§7.2.2](https://kerodon.net/tag/02NQ) と HTT §4.1.1 の必要な場合。
ここでは一般の cofinality の理論全体を前提にせず、次を直接証明する。

任意の小圏 `I : Type u`、`[Category.{u} I]`、対象 `c : I` と `hc : IsInitial c`、
任意の `X : SSet.{u}`、`[Quasicategory X]`、任意の単体集合の射 `F : nerve I ⟶ X` に対し、
`v_c : Δ[0] ⟶ nerve I` を c に対応する頂点包含と置くと、

```text
leftAnodyneExtensions v_c
TrivialKanFibration (sliceOverRestrict F v_c)
-- sliceOver F ⟶ sliceOver (v_c ≫ F)
```

が成立する。制限の向きは **全図式上の slice から c での値上の slice へ**。
`F` が通常の圏の関手の nerve であること、I の有限性、他の前提束は要求しない。
`IsInitial c` は元の 1 圏 I での始対象性である。

証明方針：まず単射 f に対する `Δ[0]⋆f` の left anodyne 性を、
境界セルでの `Λ[n+1,0]` の同定と coslice の普遍性・境界セル分解から示す
（[Kerodon Lemma 4.3.7.8](https://kerodon.net/tag/0196)）。
始対象 c からの一意な射で `Δ[0]⋆nerve I ⟶ nerve I` を直接構成し、
`Δ[0]⋆{c} ⟶ Δ[0]⋆nerve I` から頂点包含 v_c への矢の retract を作る。
この retract では点から `Δ[0]⋆{c}` への射は元の {c} 側の端点を使う。
従って c に入る同型などがある場合にも、c が「厳密な」始対象であるという余分な仮定は不要。
次に A2c により、右因子の left anodyne 射と左の任意の境界包含の pushout-join が
inner anodyne となることを使い、slice の制限が全境界の rlp を持つと示す。
モデル構造は使わない。

これは実装前の文言と証明の固定であり、A2h の証明完了を意味しない。
ユーザー指示に従い、この記録・報告後の追加承認は待たずに実装する。

### A2g 完了（2026-10-18）

`cospanConeSquareIso : join Δ[0] (horn 2 2) ≅ Δ[1] ⊗ Δ[1]` を実装。
二つの三角形の和と対角の交わりの pushout を両側で構成した。
`cospanSquareBoundary` は右辺と上辺からなる cospan で、各脚の式も証明した。
`pullbackCone F` が四角形を錐に直し、`IsPullbackSquare F` はその極限性。
A2g 完了、A2h〜A2i は未完了。Core ビルドと累計 315 件の公理監査は成功。
全 36 新規公開宣言の正確な型・前提は計画 §6 に記録した。
