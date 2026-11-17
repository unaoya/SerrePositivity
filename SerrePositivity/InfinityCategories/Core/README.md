# quasicategory の一般論

## 概要

Mathlib の `SSet.Quasicategory` をそのまま用いる。
正本は [計画](../../../formalization-plans/archive/stage-i/infinity-lanes/infinity-core.md) §1〜§4。
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

### A3e の文言（実装前、2026-10-18）

原典を再照合：計画に記載された旧番号に対応する同値判定は現行 Kerodon Theorem 4.8.4.1（https://kerodon.net/tag/01JX ）、写像空間による充満忠実性は §4.8.3（https://kerodon.net/tag/0578 ）、本質的全射性は §4.8.1。Joyal モデル構造は使わない。

- `pinchedHomMap f x y : pinchedHom x y ⟶ pinchedHom (f.app _ x) (f.app _ y)` を後合成で定義する。
- Kan 複体間の射のホモトピー同値性は、逆射 g と `SSet.Homotopy (f ≫ g) (𝟙 _)`、`SSet.Homotopy (g ≫ f) (𝟙 _)` の存在で表す。
- `IsFullyFaithful f` は、全ての x,y について `pinchedHomMap f x y` がこの意味のホモトピー同値であること。h X の Hom の全単射だけへ弱めない。
- `IsEssentiallySurjective f` は、各 y に対し x と h Y の同型 `VertexIso (f.app _ x) y` が存在すること。
- 主目標は `[Quasicategory X] [Quasicategory Y]` の下で、上の二条件から `IsQCatEquivalence f` を構成すること。
- 同値 e による極限の保存・反映は、任意の p : K ⟶ X と c : JoinCone p に対する `IsLimitCone c ↔ IsLimitCone (mapJoinCone e.hom c)`。ここで像の図式は p ≫ e.hom であり、頂点の h X での同型だけを仮定する主張ではない。

まず写像空間の関手性と上の二条件の API、そのホモトピー圏での帰結を整備し、その後に quasicategory の逆射の構成と極限の保存・反映へ進む。

A3e 前半保存：写像空間の射と π₀ の自然性、実際の単体的ホモトピー逆による充満忠実性、本質的全射性、そのホモトピー圏での帰結、関手単体集合の同型から実際のホモトピーを選ぶ API を実装。`IsFullyFaithful.toHoEquivalence` は通常のホモトピー圏の同値であり、quasicategory の逆射の構成は未完了。同値による極限錐の保存・反映も残る。A3e 完了とは数えない。

A3e 続き：`QCatEquivalence.isTerminalVertex_iff` は同値による終対象性の保存・反映を与える。`FunctorIso.exists_boundaryFilling` は関手単体集合で同型な境界図式間で充填を移す。`IsFullyFaithful.reflects_isTerminalVertex` は本質的全射性を仮定せずに終対象性を反映する。quasicategory の逆射の構成と、任意の極限錐の保存・反映は引き続き未完了。

A3e 続き：trivial Kan fibration と inner anodyne 射から明示的な同値を構成し、同値の二対三則を実装。trivial Kan fibration による任意の極限錐の保存・反映も成立する。可逆な辺の path と端点評価を定義した。新規34宣言の正確な型・前提は計画 §6、監査累計687件。一般の充満忠実＋本質的全射の判定と、一般の同値による極限の保存・反映は未完了。

A3e 続き：可逆 path の始点評価の trivial Kan fibration 性と、任意の単射に沿う可逆なホモトピーの延長を証明。点ごとに可逆なホモトピーの両端は関手単体集合で同型となる。path による関手の置換と同値性の還元も実装。公開23宣言の正確な型・前提を計画 §6 に記録、Core ビルド・累計710宣言の標準3公理監査成功。置換の終点評価の inner fibration 性、一般の同値判定と極限不変性は未完了。

A3e 続き：区間の両端と内ホーンの prism を固定した延長を実装し、path による置換の終点評価の inner fibration 性を証明。本質的全射性から置換の頂点全射性も成立する。新規15宣言の全ての型と前提を計画 §6 に記録。Core ビルド・累計725件の標準3公理監査成功。充満忠実性から全境界の持ち上げへの移行、一般の同値判定・極限不変性は未完了。

A3e 続き：inner fibration が右 pinched 写像空間上に誘導する射の右ファイブレーション性と fiber の Kan 性を証明。相対 coslice の制限の左ファイブレーション性と、両端が quasicategory のときの標的の quasicategory 性も実装。公開9宣言の正確な型と前提を §6 に記録。Core ビルド・累計734宣言の標準3公理監査成功。相対外側ホーンの充填、写像空間の fiber の可縮性への移行、主同値判定と一般の極限不変性は未完了。

A3e 続き：可逆辺を持つ両側の外側ホーンの相対充填、Kan 複体間の右ファイブレーションの全ホーン充填、inner fibration の写像空間の射の全ホーン充填を証明。Mathlib の Fibration はホーンの rlp という定義としてのみ使用し、モデル構造・弱同値は使わない。同値である Fibration の厳密な切断も構成。公開14宣言の正確な型・前提は計画 §6。Core ビルド・累計748件の標準3公理監査成功。写像空間の fiber の可縮性への移行、主同値判定と一般の極限不変性は未完了。

A3e 続き：同値である Fibration は trivial Kan fibration となることを、切断・退化三角形・相対 prism の直接充填で証明。充満忠実な inner fibration の右 pinched 写像空間の射は trivial Kan fibration であり、その各 fiber は可縮な Kan 複体。公開8宣言の正確な型・全前提は計画 §6。Core ビルド・累計756件の標準3公理監査成功。写像空間の基底変換、主同値判定、一般の極限不変性は未完了。

### Π2 対応：始対象 cofinality の二宇宙（2026-10-18）

`initialCofinality` と `initialRestriction` は既存名のまま `{I : Type v} [Category.{w} I]` に一般化した。`nerveVertex`・`nervePoint` から始対象の錐と retract の補題も二宇宙を扱う。`nerve I`、図式の標的 `X`、join・slice は `SSet.{max v w}` に置く。対象 Type (u+1)・Hom Type u の `PerfUnder_u p S` の形では `X : SSet.{u+1}` を取れる。従来の同一宇宙の型は v=w の特殊化でそのまま使用できる。

一般化した19公開宣言の全ての型と前提を計画 §6 に記録。Core ビルドと、一般二宇宙・Π2 の宇宙・従来の宇宙の三つの使用例を含む監査が成功し、累計756宣言は標準3公理のみ。今回の要請は完了し A3e に戻る。

A3e 続き：写像空間の基底変換と標準単体の最後の頂点の終対象性を実装。充満忠実な inner fibration は全正次元境界を持ち上げ、頂点上の全射性を加えれば trivial Kan fibration、従って A3a の同値となる。公開25宣言の正確な型・全前提は計画 §6。Core ビルド・累計781宣言の標準3公理監査成功。一般の関手の path 置換への充満忠実性の移行、主同値判定と一般の極限不変性は未完了。

A3e 続き：右 pinched 写像空間の任意パラメーターに対する普遍性と後合成の自然性を実装。trivial Kan fibration が誘導する写像空間の射は trivial Kan fibration であり、quasicategory 間では充満忠実となる。Kan 複体のホモトピー同値の左右消去則と充満忠実な後合成による検出も成立する。公開18宣言の正確な型・全前提を計画 §6 に記録。Core ビルド・累計799宣言の標準3公理監査成功。主同値判定と一般の極限不変性は引き続き未完了。

A3e 主同値判定完了：`isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective` は quasicategory 間の任意の関手について、右 pinched 写像空間のホモトピー同値性と本質的全射性から A3a の実際の逆射・関手単体集合の可逆二胞体を構成する。`qCatEquivalenceOfFullyFaithfulEssentiallySurjective` は逆データの選択。可逆 path の終点評価の trivial Kan fibration 性と、関手同型による充満忠実性の不変性を経由した。新規18公開宣言の正確な型・全前提は計画 §6。Core ビルド・累計817宣言の標準3公理監査成功。一般の同値による任意の極限錐の保存・反映は未完了であり、A3e 全体は未完了。

担当順は統合計画 foundations.md に従い A3e → A6（関手 ∞ 圏の極限、HTT 5.1.2.2）→ A4・A5。F1 は α2 の担当。Core の既存の公開名・型を変更する場合は事前に報告する。

### A3e 完了（2026-10-18）

`isQCatEquivalence_iff_fullyFaithful_essentiallySurjective` は同値判定の両方向を与える。`IsQCatEquivalence.isFullyFaithful` と `QCatEquivalence.isFullyFaithful` の充満忠実性は、全ての右 pinched 写像空間の実際の単体的ホモトピー逆の存在を意味する。

`IsQCatEquivalence.isLimitCone_iff` と `QCatEquivalence.isLimitCone_iff` は、任意の単体集合 K、図式 p : K ⟶ X、錐 c : JoinCone p について、同値 f による `IsLimitCone c ↔ IsLimitCone (mapJoinCone f c)` を証明する。path 置換の二つの射影を trivial Kan fibration とし、元の関手を厳密な切断と終点射へ分解して、既存の trivial Kan fibration による極限不変性へ還元した。図式や錐の形を制限しない。

公開10宣言の全ての型・前提を計画 §6 に記録。Core ビルド1644 jobs、累計827宣言の標準3公理監査、全体ビルド7911 jobs が成功した。これで A3a–e の必須項目は完了。A3f は任意のまま未完了、A3g は保留。次の担当順は A6 → A4・A5。既存の公開名・型は変更していない。

### A6 の文言と現在地（2026-10-18）

原典は現行 [Kerodon §7.1.8](https://kerodon.net/tag/02X8)、特に [Proposition 7.1.8.3](https://kerodon.net/tag/02X9) の双対。計画の §7.1.6 は現在は相対極限の節である。HTT の対応は Proposition 5.1.2.2。任意の単体集合 J,K と quasicategory X、図式 p : J ⟶ Fun(K,X) について、各頂点 k で評価図式の極限が存在すれば、自然な点ごとの極限錐を構成し、その錐が Fun(K,X) での極限錐であることを示す。既存の自然な錐 c が与えられた場合は、極限性と全ての評価の極限性の同値を目標とする。逆方向でも評価図式の極限の存在仮定を保持する。

評価図式・評価錐、`HasPointwiseLimits`、`IsPointwiseLimitCone` と同じ slice 内の同型による不変性を実装した。`SkeletalExtension` は各次数の境界充填を coproduct と pushout で貼り、互換な射の余極限から全体への延長を作る。`exists_extension_of_terminal_last_vertices` は全頂点を含む指定部分の外で、単体の最後の頂点が終対象へ写れば延長できることを証明する。`isTerminalVertex_functorVertex_of_pointwise` は各点で終対象となる関手が関手単体集合でも終対象になることを証明し、この向きには標的の quasicategory 性を仮定しない。

新規19公開宣言の全型・前提は infinity-core.md §6。Core ビルド1648 jobs、累計846宣言の標準3公理監査が成功。任意図式の自然な極限錐の構成と主同値・評価の保存の一般形は未完了。A4・A5 は未着手。既存の公開名・型は変更していない。

A6 続き：標的を固定した相対骨格の境界持ち上げを貼り合わせる二補題と `TerminalBoundaryLifting p x`、この条件での部分複体からの延長、`terminalBoundaryLifting_ihom_of_pointwise` を実装した。最後の補題は各点の厳密な終点境界充填条件が関手単体集合の射にも移ることを証明する。全て quasicategory 性・fibration 性を仮定しない。この厳密な条件と相対終対象・極限錐の同値はまだ主張しない。公開5宣言の全型・前提は計画 §6、Core ビルド1651 jobs・累計851宣言の標準3公理監査成功。A6 の任意図式の主定理、A4・A5 は未完了。既存の公開名・型は変更していない。

A6 続き：`joinTensorLeft` と自然性・左右包含・一点の計算、join の左右包含の単射性を実装。`coneRestriction J X`（錐の制限）の図式の頂点上の fiber を `coneFamily p` とし、X が quasicategory なら両者の inner fibration 性・fiber の quasicategory 性を得た。`sliceConeFamilyMap p` は既存の slice からこの fiber への比較射で、その零次成分は `coneFamilyVertexEquiv p` に一致する。零単体の全単射だけから同値とは結論していない。比較射の同値性、Kerodon Example 4.6.6.8・Proposition 7.1.6.13 との接続、A6 の主定理は未完了。公開27宣言の全型・前提は計画 §6。Core ビルド1654 jobs、累計878宣言の標準3公理監査成功。既存の公開名・型は変更していない。

A6 続き：円柱の両端を潰す二つの pushout で fat join を構成し、普遍性・包含・円柱上の計算と、通常の join への比較射 `fatJoinComparison` を実装した。比較射の categorical equivalence 性は未完了。内部 Hom の前後合成を表す単体集合の射から `FunctorIso.map_pre`・`map_post` と、`QCatEquivalence.precompose`・`postcompose`、`IsQCatEquivalence` の対応を得た。前合成では新しい標的の quasicategory 性を仮定する。公開40宣言の全型・前提は計画 §6。Core ビルド1658 jobs、累計918宣言の標準3公理監査成功。A6 の任意図式の主定理、A4・A5 は未完了。既存の公開名・型は変更していない。

A6 続き：`isInvertibleEdge_iff_evaluateFunctorAt` は任意のパラメーター K と quasicategory X に対し、関手単体集合の指定された辺の可逆性を全ての頂点での評価で判定する。可逆 path の普遍ホモトピーの辺を定値 path に制限すると恒等となり、前合成の同値によって元の辺の可逆性を反映した。`functorIsoOfPointwiseInvertibleHomotopy` はそのホモトピー自身の辺の類から同型を作る。公開8宣言の全型・前提は計画 §6。Core ビルド1659 jobs・累計926宣言の標準3公理監査成功。fat join 比較・slice 比較の同値性と A6 の主定理は未完了。A4・A5 は未着手。既存の公開名・型は変更していない。

A6 続き：`IsPrecompositionEquivalence f` は任意の quasicategory への前合成が同値となる補助条件。元の単体集合は quasicategory でなくてもよい。合成・二対三則・inner anodyne 射・点ごとに可逆なホモトピー逆を扱い、quasicategory 間では既存の同値条件との同値を証明した。既存の公開名・型は維持。新規15宣言の全型・前提は計画 §6。Core ビルド1661 jobs・累計941宣言の標準3公理監査成功。fat join と slice の比較射の同値性、A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：`IsPrecompositionEquivalence.whiskerLeft`・`whiskerRight` は任意の単体集合との直積による保存。`exists_extension_of_functorIso` は単射に沿う制限の同型の厳密化、`IsPrecompositionEquivalence.trivialKanFibration_pre` は単射である前合成の同値からの全境界持ち上げ、`IsPrecompositionEquivalence.of_isPushout` はその単射の pushout による保存。既存の公開名・型は維持。公開10宣言の全型・前提は計画 §6。Core ビルド1664 jobs・累計951宣言の標準3公理監査成功。fat join と slice の比較射の同値性、A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：fat join の関手性を追加。codiscrete 圏の nerve への射を頂点の割当てから作り、その非空の場合の全境界充填を直接証明した。`equivalenceInterval` は二対象の可逆な区間。その端点は単射であり前合成の同値条件を満たす。`equivalenceMappingCylinderIn` は任意の射に対して単射、`equivalenceMappingCylinderOut` は前合成の同値条件を満たし、両者の合成は元の射。新規32宣言の全型・前提は計画 §6。Core ビルド1669 jobs・累計983宣言の標準3公理監査成功。既存の公開名・型は維持。一般の fat join 比較・slice 比較の同値性と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：固定部分 A→B が単射なら相対円柱の両端は単射であり前合成の同値条件を満たす。相対写像円柱の残った端点は A→B と A→C が単射なら単射。`isPrecompositionEquivalence_map_under_of_mono` は固定部分の単射な対象間での関手による保存を単射上の保存から検出する。`isPrecompositionEquivalence_underPushout_map`・`isPrecompositionEquivalence_of_pushout_fixed_base` は固定基底からの二つの射が単射の図式の比較を pushout 後に保存する。基底も変わる一般の貼り合わせは未完了。新規29宣言の全型・前提は計画 §6。Core ビルド1792 jobs・累計1012宣言の標準3公理監査成功。既存の公開名・型は維持。fat join 比較・slice 比較の同値性と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：`isIso_fatJoinComparison_point` と `isPrecompositionEquivalence_fatJoinComparison_point` は二点 Δ[0]・Δ[0] の fat join 比較の厳密な同型性と前合成の同値条件。一般の標準単体の場合の完成とは数えない。点との直積と join の同型、および前合成の同値条件の二対六則と二つの可逆ホモトピーによる検出を追加した。新規17宣言の全型・前提は計画 §6。Core ビルド1795 jobs・累計1029宣言の標準3公理監査成功。既存の公開名・型は維持。一般の fat join 比較・slice 比較の同値性と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：任意の n、m の `fatJoinStdLeftNormalize` と `fatJoinStdNormalize` を構成し、恒等→左の正規化、左右の正規化→左の正規化の二つのホモトピーを作った。左右の因子を全時間で固定し、各頂点の辺は退化し可逆であることを証明した。両正規化の自己射は前合成の同値条件を満たす。標準単体の比較自体には切断の構成と合成の同一視がまだ必要で、一般の単体集合への貼り合わせも未完了。新規66宣言の全型・前提は計画 §6。Core ビルド1804 jobs・累計1095宣言の標準3公理監査成功。既存の公開名・型は維持。slice 比較と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：`isPrecompositionEquivalence_fatJoinComparison_stdSimplex n m` は任意の自然数 n、m の fat join 比較の前合成の同値条件。切断 `fatJoinStdSection` を構成し、切断→比較は厳密な恒等射、比較→切断は `fatJoinStdNormalize` と同一視した。fat join の quasicategory 性は不要。両因子に頂点がある場合の円柱包含のエピ性と一般の比較の自然性も追加した。新規19宣言の全型・前提は計画 §6。Core ビルド1809 jobs・累計1114宣言の標準3公理監査成功。既存の公開名・型は維持。任意の因子への貼り合わせ、slice 比較と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：`equivalencePathInternalHomIso K X` は X が quasicategory のとき可逆 path と内部 Hom の同型で、両端評価と始域の制限を保つ。`trivialKanFibration_relativeEquivalencePathMap_pre i X` は i が単射なら関手単体集合の制限の相対的な可逆 path の写像が全単射に対して持ち上がること。任意のパラメーターと既定の部分の持ち上げを含む。モデル構造は使用していない。新規32宣言の全型・前提は計画 §6。Core ビルド1816 jobs・累計1146宣言の標準3公理監査成功。既存の公開名・型は維持。一般の貼り合わせ、任意の因子の fat join 比較、slice 比較と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：終点指定の相対可逆 path の持ち上げを持つ inner fibration に沿う同値の引き戻しを、共通の path の解像で証明した。これを関手単体集合の制限に適用し、`IsPrecompositionEquivalence.of_isPushout_of_mono_other`（もう一方の射が単射）と `isPrecompositionEquivalence_of_pushout_gluing`（二つの正方形の同じ側が単射、三頂点の比較が同値条件）を得た。モデル構造は使わない。既存の公開名・型は維持。新規22宣言の全型・前提は計画 §6。Core ビルド1823 jobs・累計1168宣言の標準3公理監査成功。任意の因子の fat join 比較へのセル分解・余極限の接続、slice 比較と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：通常の join と fat join は左右どちらの因子でも二項 pushout を保つ。`fatJoinMap_left_mono` は左因子の単射保存、`isPrecompositionEquivalence_fatJoinComparison_of_pushout_left` は左因子の三つの比較の同値条件から単射の pushout 後の比較の同値条件を得る。右因子の単射保存と無限のセル分解の余極限への接続は未完了。新規21宣言の全型・前提は計画 §6。Core ビルド1829 jobs・累計1189宣言の標準3公理監査成功。既存の公開名・型は維持。任意の因子の fat join 比較、slice 比較と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：`fatJoinMap_right_mono` と `isPrecompositionEquivalence_fatJoinComparison_of_pushout_right` を追加し、左右両方の因子で単射を含む pushout による比較の閉包を得た。零端の貼り合わせと交わらない一端の逆像を計算するため、もう一方の正方形の pullback 性は不要。新規11宣言の全型・前提は計画 §6。Core ビルド1832 jobs・累計1200宣言の標準3公理監査成功。既存の公開名・型は維持。セルの族と無限の骨格の余極限への接続、任意の因子の fat join 比較、slice 比較と A6 の主定理は未完了。A4・A5 は未着手。

A6 続き：反変内部 Hom の自己随伴と持ち上げ問題の交換により、単射の前合成の同値条件を境界の前合成への左持ち上げ性として特徴づけた。`monoPrecompositionEquivalences` の同型・retract・合成・小さい coproduct・整列合成列・自然数の合成列による閉包を得た。モデル構造や small object factorization は使わない。任意の同値な図式の余極限の保存を証明したわけではない。元の比較を自然な相対写像円柱で単射に置換し、関手の余極限保存と接続する作業が残る。新規15宣言の全型・前提は計画 §6。Core ビルド1835 jobs・累計1215宣言の標準3公理監査成功。既存の公開名・型は維持。一般の fat join 比較・slice 比較・A6 主定理・A4・A5 は未完了。

A6 続き：可換正方形の写像円柱の射 `equivalenceMappingCylinderMap` と、元の端点に新しい始域を先に貼った `equivalenceMappingCylinderCornerMap` を追加。相対比較は始域・終域の比較が単射なら単射で、元の二つの射が同値条件を満たせば同値条件を満たす。後者には比較射の単射性は不要。`equivalenceMappingCylinderFunctor` は存在する全ての余極限を保つ。新規21宣言の全型・前提は計画 §6。Core ビルド1840 jobs・累計1236宣言の標準3公理監査成功。既存の公開名・型は維持。join と fat join の関手の連結な余極限保存とセル分解への接続、一般の fat join 比較・slice 比較・A6 主定理・A4・A5 は未完了。

A6 続き：通常の join の under 圏への関手と slice／coslice の随伴を作り、左右両因子の連結な余極限保存を得た。fat join の両因子の関手にも二段の pushout から連結な余極限保存を証明。第一の pushout の左変数の関手は任意の余極限を保つが、右変数には連結性を仮定する。比較射の無限の貼り合わせの完成ではない。新規40宣言の全型・前提は計画 §6。Core ビルド1847 jobs・累計1276宣言の標準3公理監査成功。既存の公開名・型は維持。自然な写像円柱とセルの族・無限の骨格の相対比較への接続、一般の fat join 比較・slice 比較・A6 主定理・A4・A5 は未完了。

A6 続き：自然変換の写像円柱と、二つの可算列・共通部分を持つ任意の族の相対比較の持ち上げの貼り合わせを追加。単射と指定形の余極限を保つ二つの関手の比較について、各対象の同値条件から可算余極限上の条件、初期対象と各対象の条件から coproduct 上の条件を得た。関手に通常の coproduct の保存は要求せず、初期対象を共通部分とする連結な wide pushout の保存を使う。新規20宣言の全型・前提は計画 §6。Core ビルド1855 jobs・累計1296宣言の標準3公理監査成功。既存の公開名・型は維持。初期対象・境界・各骨格への次数による帰納の接続、一般の fat join 比較・slice 比較・A6 主定理・A4・A5 は未完了。

A6 続き：**任意の二つの単体集合の比較 `isPrecompositionEquivalence_fatJoinComparison (A B : SSet.{u}) : IsPrecompositionEquivalence (fatJoinComparison A B)` が完成。** 任意の quasicategory X への前合成が同値。両因子の有限性・非空性・quasicategory 性は不要。初期対象と標準単体の自然な比較を全単体集合へ広げるセルの比較原理を、境界の次数の帰納、セルの族、骨格、可算余極限で証明した。原典は Kerodon Theorem 4.6.2.8、Lemma 4.6.2.10。新規13宣言の全型・前提は計画 §6。Core ビルド1858 jobs・累計1309宣言の標準3公理監査成功。既存の公開名・型は維持。slice 比較の同値性と相対終対象への接続、A6 の任意図式の主定理は未完了。A4・A5 は未着手。

A6 続き：右因子の図式 p を厳密に固定した関手圏でも `isQCatEquivalence_fatJoinComparison_fixedDiagram A K X p` が同値を与える。前合成の間の単射な同値について相対持ち上げから厳密な逆と基底上の可逆ホモトピーを構成し、fiber に制限した。比較射のエピ性、join の左右の普遍的同値条件の保存も追加。既存の公開名・型は維持。新規25宣言の全型・前提は計画 §6。slice 比較と A6 主定理は未完了。A4・A5 は未着手。

上記保存単位の検証：Core ビルド1869 jobs成功、累計1334宣言の公理監査は標準3公理のみ。

A6 続き：可逆円柱による関手の同型の判定と、共通図式を固定した可逆ホモトピーの pushout 上の貼り合わせ・円柱への延長を追加。`exists_joinCylinder_extension_of_relative_homotopy` は join の右因子を全時刻で固定する可逆ホモトピーから、左因子の可逆円柱上の族を作る。新規18宣言の全型・前提は計画 §6。既存 API は維持。slice 比較・A6 主定理は未完了、A4・A5 は未着手。

上記保存単位の検証：Core ビルド1877 jobs成功、累計1352宣言の公理監査は標準3公理のみ。

A6 続き：`nonempty_functorIso_iff_sliceOverFixedDiagramVertexIso` により Kerodon Lemma 4.6.4.25 の同型判定が両方向で完成。任意の A と K、quasicategory X、p : K ⟶ X と f g : A ⟶ sliceOver p に対し、関手の同型の存在と固定図式上の join の関手の同型の存在が同値。新規17宣言の全型・前提は計画 §6。既存 API は維持。fat join の普遍性との接続、slice 比較射の同値性・A6 主定理は未完了、A4・A5 は未着手。

上記保存単位の検証：Core ビルド1883 jobs成功、累計1369宣言の公理監査は標準3公理のみ。

A6 続き：`laxSliceHomEquiv p A : (A ⟶ laxSlice p) ≃ {F : fatJoin A K ⟶ X // fatJoinInr A K ≫ F = p}` を任意の A、K、X で証明。太い slice は太い零単体の join の固定図式上の内部 Hom の fiber で、X が quasicategory なら quasicategory。`coneFamilyLaxSliceMap p` は X が quasicategory のとき同値。太い join と直積の比較と curry・uncurry の両方の逆則も追加。新規34宣言の全型・前提は計画 §6。既存 API は維持。パラメーター付きの同型類の対応・slice 比較射の同値性・A6 主定理は未完了、A4・A5 は未着手。

上記保存単位の検証：Core ビルド1891 jobs成功、累計1403宣言の公理監査は標準3公理のみ。

A6 続き：**`isQCatEquivalence_sliceConeFamilyMap p` が任意の K、quasicategory X、p : K ⟶ X で完成。** 通常の slice と錐の関手単体集合の固定図式上の fiber は既存の比較射で同値。太い slice への `sliceLaxMap` の同値性を任意のパラメーターの関手の同型類の比較で証明し、二つの比較射の厳密な整合性と二対三則を適用した。原典は Kerodon Proposition 4.6.4.19、Example 4.6.6.8。新規27宣言の全型・前提は計画 §6。既存 API は維持。相対終対象への接続・自然な点ごとの極限錐の構成・A6 主定理は未完了、A4・A5 は未着手。

上記保存単位の検証：Core ビルド1901 jobs成功、累計1430宣言の公理監査は標準3公理のみ。

A6 続き：極限錐と `coneFamily` の終対象の同値、相対境界充填からの極限性、同型による相対充填の移送、評価した錐の相対充填を仮定した関手圏の極限性を追加。新規6宣言の全型・前提は計画 §6。最後の仮定は通常の点ごとの極限性より強く A6 完成には数えない。Kerodon Proposition 7.1.6.13 の逆方向には錐の制限の cocartesian な輸送が使われる。一般の inner fibration の fiber の終対象性だけでは相対充填を導けないため、輸送・充填を Core 内で構成する。既存 API・§4 の設計は維持。A6 主定理、A4・A5 は未完了。

上記保存単位の検証：Core ビルド1905 jobs成功、累計1436宣言の公理監査は標準3公理のみ。

A6 続き：cocartesian な辺を先頭の外側ホーンの相対充填で定義し、始点指定の cocartesian な辺の持ち上げを持つ inner fibration を `CocartesianHornFibration` とした。可逆性との整合、引き戻し、恒等射の例と、任意の inner fibration の相対 coslice の left fibration 性を追加。原典は Kerodon Definitions 5.1.1.1・5.1.4.1、Corollary 4.3.6.9。新規13宣言と class の構築子・親構造・射影を合わせた16宣言の全型・前提は計画 §6。既存 API と §4 の設計は維持。錐の制限の cocartesian な輸送・fiber の終対象からの相対境界充填・A6 主定理は未完了、A4・A5 は未着手。

上記保存単位の検証：Core ビルド1909 jobs成功、累計1452宣言の公理監査は標準3公理のみ。追加分は CosliceEndpointFibration.lean とし、既存の RelativeCoslice.lean は変更していない。

F1 の既存 IsCocartesianEdge と同時に import できるよう、Core の今回の補助条件は HasCocartesianHornLifting、輸送の型クラスは CocartesianHornFibration と命名する。既存の F1・Core の API は変更しない。

担当更新（2026-10-18）：α は A6 の完了・報告まで。A4・A5 は D（α-S、InfinityCategories/Stable/）へ移管。Stable/ は他レーンのファイルとして編集しない。A6 後の工程は別途の指示を待つ。

追加の互換性検証：Core 全体と F1.CartesianEdge の同時 import に成功。F1 の既存 IsCocartesianEdge と Core の HasCocartesianHornLifting は両立する。

A6 続き：cocartesian な辺の coslice の射影の trivial Kan fibration 性を、点と境界の join の先頭ホーン表示と辺の持ち上げから証明。quasicategory 性は不要。新規20宣言の正確な型・前提は §6。A6 主定理は未完了。A4・A5 は D チャット α-S の担当。

上記保存単位の検証：Core 対象ビルド1914 jobs成功、累計1472宣言の公理監査は標準3公理のみ。Core 全体と F1.CartesianEdge の同時 import も成功。

A6 続き：固定基底の辺の持ち上げの圏の cocartesian な始対象性、始対象を持つ left fibration の終対象上の fiber の可縮性、固定基底の coslice の射影の left fibration 性を証明。組み合わせて fiber の終対象へ向かう固定基底上の射の空間の可縮性を得た。quasicategory 性は不要。新規10宣言の全型・前提は §6。A6 主定理は未完了。

上記保存単位の検証：Core 対象ビルド1917 jobs成功、累計1482宣言の公理監査は標準3公理のみ。

A6 続き：cocartesian な最初の垂直辺を持つ prism の基底上の延長、cocartesian な path の始点と基底への射の trivial Kan fibration 性、任意の単射上の輸送を固定した相対延長を証明。quasicategory 性は不要。新規16宣言の全型・前提は §6。A6 主定理は未完了。

上記保存単位の検証：Core 対象ビルド1924 jobs成功、累計1498宣言の公理監査は標準3公理のみ。

A6 続き：cocartesian fibration p:E→B、quasicategory E・B に対し、fiber の終対象性と TerminalBoundaryLifting p x.val の同値を証明。最後の頂点を固定して境界を fiber へ輸送・充填し、終点側の prism の相対延長で戻す。一般の inner fibration には逆向きを主張しない。新規24宣言の全型・前提は §6。錐の制限の cocartesian 性と A6 主定理は未完了。

上記保存単位の検証：Core 対象ビルド1929 jobs成功、累計1522宣言の公理監査は標準3公理のみ。

A6 続き：錐の制限 coneRestriction K X の CocartesianHornFibration 性、錐の頂点で可逆な辺の cocartesian 性、IsLimitCone と相対境界充填の同値を証明し、通常の IsPointwiseLimitCone から IsLimitCone への方向を得た。X の quasicategory 性のみ、添字 J・K は任意。新規23宣言の全型・前提は §6。HasPointwiseLimits からの自然な錐の存在と、存在仮定の下での逆方向は未完了。

上記保存単位の検証：Core 対象ビルド1940 jobs成功、累計1545宣言の公理監査は標準3公理のみ。

A6 完了：HTT 5.1.2.2 の極限側。`exists_pointwiseLimitCone` により各頂点の通常の極限の存在から自然な点ごとの極限錐を構成し、`hasLimit_of_hasPointwiseLimits` により関手 ∞ 圏での極限の存在を得た。`isLimitCone_iff_pointwise_of_hasPointwiseLimits` は同じ存在仮定の下で任意の錐の極限性と点ごとの極限性の同値。X の quasicategory 性のみ、J・K は任意、点ごとの錐の自然性は仮定しない。今回の新規11宣言と前段階の23宣言を含む全型・前提は §6。A6 の残件はなし。A4・A5 は D（α-S）の担当で、本チャットは A6 後の指示を待つ。

最終統合検証で F1 と重複した Core の4宣言は事前報告の上で改名：IsCocartesianPathVertex → IsCocartesianHornPathVertex、cocartesianPathVertex → cocartesianHornPathVertex、cocartesianPathVertex_zero → cocartesianHornPathVertex_zero、vertexFiber_quasicategory_of_innerFibration → innerFibration_vertexFiber_quasicategory。型と instance 属性は維持し、F1 側の既存名・型は変更していない。正確な型は §6。

最終検証：Core 対象ビルド1944 jobs成功（exit 0）、lake env lean scripts/audit_infinity_core.lean 成功（累計1556宣言、propext・Classical.choice・Quot.sound の標準3公理のみ）、Core 全体と F1 全体の同時 import 成功、全体 lake build 9993 jobs成功（exit 0）。最初の全体ビルドで検出した Core/F1 の宣言名の重複は上記の事前報告済み改名で解消した。再ビルド中の一時的な .olean の読み取り競合はソース変更なしで再生成し復旧。A6 に未完了事項なし。
