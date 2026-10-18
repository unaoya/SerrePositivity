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

### A2h 完了（2026-10-18）

`initialCofinality` は、実装前に固定した文言通り、小圏の始対象 c と
任意の `F : nerve I ⟶ X`、`[Quasicategory X]` に対し
`TrivialKanFibration (initialRestriction F c)` を証明する。
`nervePoint_leftAnodyne` は始対象の頂点包含の left anodyne 性。
`sliceOverRestrict_trivialKanFibration` は一般の left anodyne 単射に沿う制限の性質。
点を左から join した単射の left anodyne 性と、始対象の一意な射から作った錐の retract を用いた。
A2h 完了、A2i は未完了。Core ビルドと累計 356 件の公理監査は成功。
全 41 新規公開宣言の正確な型・前提は計画 §6 に記録した。


### A2i 完了・A1/A2 全工程の完了（2026-10-18）

`Checks.lean` は `LimitExamples.lean` を公開 import する。
`LimitChecks.topPair_limit_agreement (v : Fin 2)` は、通常の圏 `0→1` の
二対象離散図式 `(1,1)` への通常の錐の極限性と、その nerve の join の錐の極限性の同値：

```lean
Nonempty (Limits.IsLimit (LimitChecks.topPairOrdinaryCone v)) ↔
  IsLimitCone (LimitChecks.topPairNerveCone v)
```

両側が `v = 1` と同値であり、頂点 1 の正例・頂点 0 の負例を含む。
図式の一致と錐の頂点の一致も証明した。具体例に追加前提はない。
任意の形 K の標準辺の終対象 1 への定数図式も極限錐を持つ。
`TerminalMap.lean` は trivial Kan fibration による終対象性の反映と、
同型・図式の等式による極限錐の移送を整備する。
新規 34 宣言の正確な型・前提は計画 §6 に全件記録した。

A1a–d、A2a–i は全て完了。Core の対象ビルドと累計 390 件の公理監査は成功し、
許した標準三公理以外はない。工程末の全体 `lake build` も終了コード 0（7507 jobs）。
今回の範囲に未完了項目はなく、一般の全極限の比較定理は主張しない。A3 以降は別途指示。


## A3a：同値の正確な文言（2026-10-18、実装前）

[Kerodon Definition 4.5.1.10](https://kerodon.net/tag/01DY) と
[Construction 4.5.1.23](https://kerodon.net/tag/02BZ) に合わせる。
quasicategory X,Y の射 f:X→Y の逆データは g:Y→X と、
`h Fun(X,X)` の f≫g と id_X の同型、`h Fun(Y,Y)` の g≫f と id_Y の同型。
ここで Fun(X,Y) は Mathlib の `(ihom X).obj Y`、射を零単体へ送る写像は
`SSet.unitHomEquiv` と閉構造の `curry'` で直接与える。
これは `QCat.strictBicategory` の可逆 2 胞体による同値の条件であり、
単なる hX≌hY を定義に置くものではない。
逆は X,Y の交換、合成の逆は逆順の合成、単位・余単位は前後合成で写した同型の合成。
評価と h の積保存から `h Fun(X,Y) → Fun(hX,hY)` を構成し、
この逆データを通常の圏同値へ送る。三角恒等式は通常の圏同値の adjointify で整える。
頂点 x,y の同型は定義通り `SSet.HomotopyCategory.mk x ≅ mk y`。
HTT §1.2.10 はこの同値を充満忠実性・本質的全射性と結び付ける段階で使用する。


### A3a 完了（2026-10-18）

`QCatEquivalence`、`IsQCatEquivalence`、`FunctorIso`、`VertexIso` を公開。
`refl`・`symm`・`trans` と `toHoEquivalence` を実装した。
`functorHomotopyEvaluation` が h Fun(X,Y) を Fun(hX,hY) へ送り、
`FunctorIso.toNatIso` が可逆な二胞体を自然同型へ送る。
Core 対象ビルド・累計 414 件の公理監査は成功、追加公理なし。
全公開宣言の正確な型・前提を計画 §6 に追記。A3b–e は未完了。

## A3b：Joyal の定理の正確な文言（2026-10-18、実装前の照合）

[Kerodon Theorem 4.4.2.6](https://kerodon.net/tag/019F)、
[§4.4.3 の core の定義](https://kerodon.net/tag/01D0)、
[HTT Proposition 1.2.4.3](https://www.math.ias.edu/~lurie/papers/HTT.pdf) を照合した。
X を quasicategory、e を始点 x・終点 y の辺とする。以下の三条件はそれぞれ同値：

1. e の類 `SSet.HomotopyCategory.homMk e` が hX で可逆。
2. 全ての n≥2 と σ₀:Λ[n,0]→X について、辺 {0,1} への制限が e なら
   σ₀ は Δ[n]→X に延長する。
3. 全ての n≥2 と σ₀:Λ[n,n]→X について、辺 {n−1,n} への制限が e なら
   σ₀ は Δ[n]→X に延長する。

「二つの条件を同時に仮定すれば可逆」という弱い主張に狭めない。
n≥2 は必要で、n=1 の外側ホーンには対象の辺全体が含まれない。
系は、quasicategory X が Kan 複体であることと hX の全射が可逆であることの同値
（HTT Proposition 1.2.5.1、Kerodon Proposition 4.4.2.1）。
§4.4.3 は全ての辺が可逆な単体の部分複体 core と整合することを確認する参照先であり、
core の一般理論をこの工程の仮定には置かない。

証明は左右ファイブレーションによる可逆辺の反映・持ち上げ、A2 の join の普遍性、
境界と外側ホーンの join 表示を使う（Kerodon Proposition 4.4.2.13、HTT §2.1.2）。
逆向きは二次・三次の外側ホーンの充填から両側の逆射を構成する。
モデル構造は使わない。この記録後、承認を待たずに実装へ進む。


### A3b 前段階の保存（2026-10-18、A3b 全体は未完了）

`hasFinalHornFillers_of_isInvertibleEdge` は quasicategory X の可逆な辺について
全ての n≥2 の最後の外側ホーンの充填を証明する。
左ファイブレーションの可逆辺の反映と終点を固定した持ち上げ、
coslice の制限の左ファイブレーション性、最後のホーンの join 表示を経由した。
追加した 26 公開宣言の型と前提は計画 §6 に記録。
Core ビルドと累計 440 件の公理監査は成功、標準三公理のみ。
逆向き・最初のホーン側・Kan の特徴づけは未完了で、続けて実装する。


### A3b 完了（2026-10-18）

公開入口 `Core/InvertibleEdge.lean` は、以下を追加の前提なしで公開する。

```lean
[Quasicategory X] → (IsInvertibleEdge e ↔ HasInitialHornFillers e)
[Quasicategory X] → (IsInvertibleEdge e ↔ HasFinalHornFillers e)
[Quasicategory X] → (KanComplex X ↔ IsGroupoid (hoFunctor.obj X))
```

実際の宣言名は `isInvertibleEdge_iff_hasInitialHornFillers`・
`isInvertibleEdge_iff_hasFinalHornFillers`・`kanComplex_iff_isGroupoid`。
最初の側を単体集合の反転で移し、最後の側の逆向きは二次・三次ホーンで直接証明した。
`InvertibleEdgeLifting.lean` に前段階の API を分離したが、公開名・型は変えていない。
新規 41 宣言の正確な型は計画 §6 に全件記録。
Core ビルド・累計 481 件の公理監査は成功。A3a・A3b 完了、A3c–e は未完了。

## A3c：pinched 写像空間の文言（2026-10-18、実装前の照合）

[HTT Proposition 1.2.2.3](https://www.math.ias.edu/~lurie/papers/HTT.pdf)、
[Kerodon Construction 4.6.5.1](https://kerodon.net/tag/01KX) と
[Proposition 4.6.5.5](https://kerodon.net/tag/01L0) に合わせる。
quasicategory X と任意の x,y:X₀ に対し、N レーンの `pinchedHom x y` は Kan 複体で、
`π₀ (pinchedHom x y) ≃ (mk x ⟶ mk y)`（右辺は hoFunctor.obj X）。
右模型の n 単体は、先頭 n 面が x に定値で最終頂点が y である X の n+1 単体。
PinchedHom/Basic.lean と Index.lean は読み込みのみで編集しない。
左模型は `((pinchedHom (X := X.op) (opObjEquiv.symm y) (opObjEquiv.symm x))).op` として
Core 内に定義し、同様の Kan 性と π₀ の Hom との同値を示す。
外側の op はパラメータの添字も反転し、最初の頂点 x と残りの定値面 y を持つ通常の左模型にする。

証明方針：右模型を slice 射影 X_{/y}→X の x 上の fiber と直接同定し、
右ファイブレーションの点上の fiber は A3b の Kan 判定により Kan であると示す。
π₀ は零単体を辺と同定し、一次単体の三角形を左右ホモトピーの関係と比較して
A1 の辺のホモトピー類による圏を介して通常の hoFunctor の Hom へ移す。
両端固定模型とのホモトピー同値（A3f）は、この主張の仮定には置かない。


### A3c 完了（2026-10-18）

`MappingSpaceKan.lean` が左右両方の Kan 性と π₀ の比較の公開入口。
`pinchedHom_kanComplex`・`pinchedHomLeft_kanComplex` は
`[Quasicategory X]` と任意の x,y に対して各模型の Kan 性を与える。
`pinchedHomPiZeroEquiv`・`pinchedHomLeftPiZeroEquiv` は各模型の π₀ と hX の x→y の Hom の同値。
右側の Kan 性は先頭の定値面を加えた内ホーンの直接充填で証明した。
左模型は右模型の X とパラメータの二重の反転で定義した。
N レーンの Basic・Index の変更はない。
全 28 新規宣言の正確な型と前提は計画 §6 に記録。
Core ビルド・累計 509 件の公理監査は成功。A3a–c 完了、A3d–e は未完了。

## A3d：終対象と写像空間の可縮性（2026-10-18、実装前の照合）

[HTT Propositions 1.2.12.4・1.2.12.9](https://www.math.ias.edu/~lurie/papers/HTT.pdf)、
[Kerodon §4.7.3](https://kerodon.net/tag/02H6) と
[Proposition 4.4.2.14](https://kerodon.net/tag/01NU) を照合した。
現在の Kerodon では終対象の節は §4.7.3 である（計画の §4.6.7 は旧参照）。

可縮な Kan 複体の条件 `IsContractibleKan K` は、全ての n≥0 の
`∂Δ[n]→K` が `Δ[n]→K` に延長する、という境界の充填条件で定義する。
これは点への射が A2 の TrivialKanFibration であることと同値であり、
Kan 性・非空性・連結性を含む。π₀ が一点であるという弱い条件にはしない。
目標の正確な文言は、`[Quasicategory X]` の下で
`IsTerminalVertex x ↔ ∀ z, IsContractibleKan (pinchedHom z x)`。

系は任意の `e : VertexIso x y` による終対象性の同値。
同じ図式 p 上の錐 c,d については、h(sliceOver p) で c,d が同型なら
`IsLimitCone c ↔ IsLimitCone d`。この仮定を hX での錐頂点だけの同型に弱めない。
さらに終対象の頂点が張る全部分複体が非空なら可縮な Kan 複体となることを示す。
証明は slice の右ファイブレーションとその fiber の境界充填条件、
A3b の可逆辺のホーン充填を用いる。モデル構造は使わない。

A3d 前半：`pinchedHomSliceFiberIso` は任意の単体集合の右 pinched 写像空間を slice 射影の頂点上の fiber と厳密に同定する。`IsTerminalVertex.pinchedHom_isContractibleKan` は quasicategory 性を仮定せず、終対象性から全ての右 pinched 写像空間の可縮性を導く。逆方向と同型不変性は未完了。

A3d 続き：`terminalVertices_isContractibleKan` は終対象が一つ存在すれば終対象の全部分複体の全境界を充填する。周囲の quasicategory 性は不要。`IsTerminalVertex.of_vertexIso` と `IsLimitCone.of_vertexIso` は quasicategory を仮定し、前者は h X、後者は h(sliceOver p) の同型に関する不変性。可縮な右写像空間から終対象性へ戻る方向は引き続き未完了。

A3d 逆方向の準備：Kerodon 4.4.2.14–15（https://kerodon.net/tag/01NU 、https://kerodon.net/tag/01A7 ）の右ファイブレーション版に沿い、`rightFibration_liftBoundaryPrism` で境界を先頭の fiber へ移す。`boundaryPrism_fillZero` はその fiber が可縮なら先頭の境界を充填する。全 prism へのセルごとの延長が残っている。これらはモデル構造を使わない組合せ論の補題。

### A3d 完了（2026-10-18）

`isTerminalVertex_iff_pinchedHom_isContractibleKan` は `[Quasicategory X]` の下で終対象性と全ての右 pinched 写像空間の可縮性を同値にする。逆方向は `rightFibration_trivialKanFibration_of_contractible_fibers` を slice 射影に適用する。右ファイブレーションの判定には base の quasicategory 性を仮定しない。prism を標準単体へ引き戻して証明し、可逆な先頭の垂直辺を持つ外側ホーンは A3b を用いる。同型不変性と終対象全体の可縮性も実装済みであり、上の途中経過に記した未完了箇所は解消した。A3e が残る。
