# Kerodon 引用の集計

走査した .lean: 30978、Kerodon を含む行: 8671、そのファイル数: 1851、抽出した参照（項目）: 9711

一行に複数の番号（`Kerodon A、B`、`Proposition X、Lemma Y`）があるときは別の行として数える。範囲 `A–B` は始点で数え、終点は range_end 列に。

## 番号の形の内訳

| 形 | 件数 |
|---|---|
| item | 6179 |
| subsection | 3378 |
| section | 148 |
| chapter | 2 |
| bare | 4 |

（item = 章.節.小節.項、subsection = 章.節.小節（`§4.6.2` など）、section = 章.節、chapter = 章のみ（`第8章` 含む）、bare = 番号なし）

ラベルの内訳: (なし/§) 5253、Corollary 1283、Proposition 1244、Theorem 511、Lemma 454、Construction 355、Remark 259、Example 140、Definition 80、Prop 54、Notation 27、Def 15、Cor 13、Variant 6、Warning 3、Theorems 3、Propositions 2、Definitions 1、Corollaries 1、Lemmas 1、Examples 1、Chapter 1

範囲（–）付き: 189

## 章ごと

| 章 | 参照数 | ファイル数 | 行数 |
|---|---|---|---|
| 1 | 31 | 9 | 31 |
| 2 | 793 | 210 | 769 |
| 3 | 608 | 157 | 594 |
| 4 | 3100 | 534 | 2950 |
| 5 | 3240 | 734 | 3068 |
| 6 | 114 | 38 | 103 |
| 7 | 1594 | 375 | 1325 |
| 8 | 208 | 43 | 204 |
| 9 | 9 | 6 | 9 |
| 11 | 10 | 1 | 10 |

## ディレクトリ（第二階層まで）× 章

| ディレクトリ | 計 | ファイル | ch1 | ch2 | ch3 | ch4 | ch5 | ch6 | ch7 | ch8 | ch9 | ch11 | 番号なし |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| InfinityCategories/F1 | 4033 | 767 | 1 | 59 | 125 | 765 | 2877 |  | 1 | 203 |  |  | 2 |
| InfinityCategories/Core | 1920 | 296 | 26 |  | 2 | 1582 | 118 |  | 190 |  | 2 |  |  |
| InfinityCategories/HomotopyLimits | 1706 | 244 |  | 1 | 6 | 370 | 121 |  | 1208 |  |  |  |  |
| InfinityCategories/DoldKanComparison | 500 | 152 |  | 405 |  | 95 |  |  |  |  |  |  |  |
| InfinityCategories/F1B | 422 | 157 |  |  | 22 | 17 | 103 | 114 | 166 |  |  |  |  |
| InfinityCategories/Kan | 307 | 50 | 4 |  | 266 | 3 | 19 |  |  | 5 |  | 10 |  |
| InfinityCategories/Coherent | 297 | 40 |  | 295 |  |  |  |  |  |  |  |  | 2 |
| InfinityCategories/DGNerve | 253 | 45 |  | 26 |  | 227 |  |  |  |  |  |  |  |
| KST/Spectra | 198 | 73 |  | 1 | 166 | 5 | 2 |  | 24 |  |  |  |  |
| InfinityCategories/PinchedHom | 35 | 4 |  |  |  | 35 |  |  |  |  |  |  |  |
| InfinityCategories/Simplicial | 20 | 9 |  | 2 | 18 |  |  |  |  |  |  |  |  |
| KST/SConstruction | 6 | 6 |  |  |  | 1 |  |  | 5 |  |  |  |  |
| InfinityCategories/Stable | 5 | 3 |  |  |  |  |  |  |  |  | 5 |  |  |
| EInfinity/FrameHom | 3 | 1 |  |  | 3 |  |  |  |  |  |  |  |  |
| Archive/InfinityCategories | 2 | 1 |  |  |  |  |  |  |  |  | 2 |  |  |
| InfinityCategories | 2 | 2 |  | 2 |  |  |  |  |  |  |  |  |  |
| InfinityCategories/Derived | 2 | 1 |  | 2 |  |  |  |  |  |  |  |  |  |

## 節（章.節）ごと

| 節 | 参照数 | ファイル数 | 主なディレクトリ |
|---|---|---|---|
| 1.2 | 4 | 1 | InfinityCategories/Kan 4 |
| 1.3 | 1 | 1 | InfinityCategories/F1 1 |
| 1.4 | 21 | 5 | InfinityCategories/Core 21 |
| 1.5 | 5 | 2 | InfinityCategories/Core 5 |
| 2.4 | 357 | 66 | InfinityCategories/Coherent 295、InfinityCategories/F1 59、KST/Spectra 1 |
| 2.5 | 436 | 144 | InfinityCategories/DoldKanComparison 405、InfinityCategories/DGNerve 26、InfinityCategories/Derived 2 |
| 3.1 | 157 | 54 | InfinityCategories/F1 101、InfinityCategories/F1B 22、KST/Spectra 15 |
| 3.2 | 450 | 110 | InfinityCategories/Kan 258、KST/Spectra 151、InfinityCategories/F1 24 |
| 3.5 | 1 | 1 | InfinityCategories/Core 1 |
| 4.1 | 5 | 2 | InfinityCategories/Core 5 |
| 4.2 | 26 | 9 | InfinityCategories/Core 13、InfinityCategories/F1 6、InfinityCategories/F1B 4 |
| 4.3 | 372 | 57 | InfinityCategories/Core 219、InfinityCategories/HomotopyLimits 107、InfinityCategories/F1 46 |
| 4.4 | 196 | 38 | InfinityCategories/Core 167、InfinityCategories/F1 22、InfinityCategories/HomotopyLimits 4 |
| 4.5 | 329 | 80 | InfinityCategories/Core 263、InfinityCategories/HomotopyLimits 30、InfinityCategories/F1 27 |
| 4.6 | 1886 | 342 | InfinityCategories/Core 680、InfinityCategories/F1 664、InfinityCategories/DGNerve 227 |
| 4.7 | 114 | 22 | InfinityCategories/Core 78、InfinityCategories/HomotopyLimits 28、InfinityCategories/F1B 8 |
| 4.8 | 172 | 45 | InfinityCategories/Core 157、InfinityCategories/HomotopyLimits 11、KST/Spectra 4 |
| 5.1 | 222 | 51 | InfinityCategories/F1 149、InfinityCategories/Core 71、InfinityCategories/F1B 2 |
| 5.2 | 739 | 184 | InfinityCategories/F1 713、InfinityCategories/Kan 18、InfinityCategories/F1B 5 |
| 5.3 | 829 | 215 | InfinityCategories/F1 582、InfinityCategories/HomotopyLimits 119、InfinityCategories/F1B 86 |
| 5.5 | 64 | 21 | InfinityCategories/F1 63、InfinityCategories/Core 1 |
| 5.6 | 1386 | 355 | InfinityCategories/F1 1370、InfinityCategories/F1B 10、InfinityCategories/Core 4 |
| 6.1 | 8 | 2 | InfinityCategories/F1B 8 |
| 6.2 | 98 | 35 | InfinityCategories/F1B 98 |
| 6.3 | 8 | 4 | InfinityCategories/F1B 8 |
| 7.1 | 212 | 72 | InfinityCategories/Core 184、InfinityCategories/F1B 18、KST/SConstruction 5 |
| 7.2 | 91 | 33 | InfinityCategories/F1B 87、InfinityCategories/Core 4 |
| 7.3 | 63 | 44 | InfinityCategories/F1B 61、InfinityCategories/Core 2 |
| 7.4 | 312 | 84 | InfinityCategories/HomotopyLimits 312 |
| 7.5 | 916 | 205 | InfinityCategories/HomotopyLimits 894、KST/Spectra 22 |
| 8.1 | 206 | 41 | InfinityCategories/F1 201、InfinityCategories/Kan 5 |
| 9.1 | 9 | 6 | InfinityCategories/Stable 5、Archive/InfinityCategories 2、InfinityCategories/Core 2 |
| 11.9 | 10 | 1 | InfinityCategories/Kan 10 |

## 小節（章.節.小節）ごと上位 40

| 小節 | 参照数 |
|---|---|
| 5.6.0 | 997 |
| 7.5.4 | 616 |
| 4.6.7 | 603 |
| 4.6.2 | 447 |
| 5.2.4 | 443 |
| 4.6.5 | 396 |
| 4.6.6 | 341 |
| 7.4.1 | 312 |
| 2.4.5 | 293 |
| 7.5.3 | 281 |
| 2.5.9 | 235 |
| 5.3.3 | 223 |
| 4.3.5 | 206 |
| 5.3.5 | 194 |
| 8.1.1 | 193 |
| 5.3.1 | 191 |
| 4.5.3 | 180 |
| 4.4.2 | 159 |
| 3.2.3 | 135 |
| 2.5.8 | 134 |
| 4.8.4 | 125 |
| 5.2.2 | 123 |
| 3.2.5 | 122 |
| 4.3.6 | 122 |
| 5.6.2 | 121 |
| 3.2.2 | 120 |
| 4.7.3 | 114 |
| 5.2.3 | 105 |
| 4.6.4 | 99 |
| 5.6.8 | 95 |
| 4.5.1 | 94 |
| 5.1.1 | 93 |
| 5.6.5 | 88 |
| 5.3.4 | 79 |
| 6.2.1 | 79 |
| 5.3.2 | 78 |
| 7.1.8 | 72 |
| 7.2.1 | 67 |
| 5.2.5 | 64 |
| 2.4.3 | 62 |

## 項（章.節.小節.項）上位 40

| 番号 | 参照数 | ラベル |
|---|---|---|
| 5.6.0.6 | 984 | -/Corollary |
| 7.5.4.6 | 553 | - |
| 5.2.4.5 | 335 | Proposition |
| 7.4.1.6 | 312 | - |
| 7.5.3.12 | 235 | - |
| 4.6.7.23 | 216 | Proposition |
| 2.4.5.8 | 181 | - |
| 5.3.5.7 | 165 | -/Theorem/Theorems |
| 8.1.1.13 | 118 | Corollary |
| 4.6.7.16 | 114 | Proposition |
| 4.6.2.10 | 112 | Lemma |
| 5.2.4.1 | 98 | Theorem |
| 5.6.2.5 | 93 | Remark |
| 5.3.3.1 | 87 | -/Definition |
| 5.2.2.8 | 76 | Proposition |
| 4.6.7.3 | 66 | Construction |
| 4.6.6.8 | 56 | Example/- |
| 4.6.7.5 | 55 | Theorem/- |
| 4.8.4.1 | 54 | -/Theorem |
| 4.4.2.15 | 54 | Lemma |
| 5.3.1.5 | 54 | Construction/- |
| 2.4.5.4 | 53 | - |
| 6.2.1.17 | 52 | Prop |
| 4.6.4.25 | 51 | Lemma |
| 4.5.3.24 | 51 | Corollary/- |
| 7.5.4.1 | 46 | - |
| 4.4.2.6 | 46 | Theorem |
| 4.6.5.1 | 46 | Construction |
| 5.2.5.1 | 44 | Proposition |
| 4.3.6.4 | 40 | Proposition |
| 3.1.2.12 | 39 | Lemma |
| 5.2.2.13 | 38 | Lemma |
| 3.1.6.3 | 37 | Remark |
| 5.3.4.7 | 36 | -/Construction |
| 5.6.9.1 | 35 | Lemma |
| 5.6.5.15 | 34 | Corollary |
| 4.6.2.8 | 33 | Theorem |
| 5.1.6.7 | 33 | Proposition |
| 5.6.8.10 | 31 | Lemma |
| 4.7.3.22 | 30 | Corollary/- |

異なる項番号の数: 216

## Tag 形式

Tag 形式（`Tag 01HU` など）の引用は 0 件。


## 番号なしの「Kerodon」

4 件。

| ディレクトリ | 件数 |
|---|---|
| InfinityCategories/Coherent | 2 |
| InfinityCategories/F1 | 2 |

- SerrePositivity/InfinityCategories/Coherent/Cube.lean:10: 規約：Mathlib の包含順序を保つ。Kerodon の逆包含では上下が逆になる。
- SerrePositivity/InfinityCategories/Coherent/HollowCube.lean:12: 規約：Mathlib の包含順序を保つ。Kerodon の逆包含では上下が逆になる。
- SerrePositivity/InfinityCategories/F1/Coherent/PathMaximum.lean:9: 規約：Mathlib は包含順序なので最大元は単調。Kerodon の逆包含規約から向きを調整する。
- SerrePositivity/InfinityCategories/F1/Coherent/ResolutionFlags.lean:8: 規約：Mathlib の包含順序に合わせ、Kerodon の旗の順序を反転した右模型を使う。

## 文脈

doc 7493、module-doc 2218
