# Higher Topos Theory 目次・段 0 集計

- 原典は Jacob Lurie の IAS 公開版（版面の日付 2017-04-09、取得日 2026-11-07、PDF 949 ページ）。[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf)・[著者の更新記録](https://www.math.ias.edu/~lurie/)
- PDF の SHA-256 は `58855f3a0ad6d9c470ded74a38938b9468927592e9ae1209bab6a068e67ede6e`。
- 第 1〜7 章と付録 A の全 29 Section、168 Subsection、番号付き項目 1,730 件。ページは原典の印刷ページ。
- 本文の太字ラベルと PDF の名前付きリンク先を突合した。リンク先が先頭ページを指す 11 件は本文でページを確かめ、リンク先一覧にない Proposition 2.4.2.3（p. 121）も本文から採った。全項目で番号と kind を本文のテキストでも照合した。
- `items.csv` は番号付き環境ごとに一行。見出しはこの目次に掲載した。`section` は項目番号の先頭 3 要素で、`x.0.0` は章の導入、`x.y.0` は節の導入を表す。`title` は原典に項目名がある場合に記入した。
- 引用数は二つの入力 CSV から番号完全一致で行数を数えた。`goal` は計画の引用元で分類し、BS、∞ 基盤、K の順に優先した。Verdier リファクタ計画は ∞ 基盤に含めた。節見出しへの引用は配下の項目へ配分していない。
- `kerodon` は Lean の docstring で当該 HTT 項目と並ぶ番号の集合（16 行、延べ 54 番号）。節番号と範囲内の番号も含み、複数の番号は ` | ` で区切った。数学的な対応は本文照合で確認する。

## 目次

- Preface（p. vii）

### 第 1 章 An Overview of Higher Category Theory（p. 1、110 件）

- 1.1 Foundations for Higher Category Theory（p. 1、44 件）
  - 1.1.1 Goals and Obstacles（p. 1、7 件）
  - 1.1.2 ∞-Categories（p. 7、7 件）
  - 1.1.3 Equivalences of Topological Categories（p. 15、8 件）
  - 1.1.4 Simplicial Categories（p. 18、4 件）
  - 1.1.5 Comparing ∞-Categories with Simplicial Categories（p. 20、18 件）
- 1.2 The Language of Higher Category Theory（p. 26、66 件）
  - 1.2.1 The Opposite of an ∞-Category（p. 26、0 件）
  - 1.2.2 Mapping Spaces in Higher Category Theory（p. 26、5 件）
  - 1.2.3 The Homotopy Category（p. 28、9 件）
  - 1.2.4 Objects, Morphisms, and Equivalences（p. 33、3 件）
  - 1.2.5 ∞-Groupoids and Classical Homotopy Theory（p. 35、6 件）
  - 1.2.6 Homotopy Commutativity versus Homotopy Coherence（p. 37、2 件）
  - 1.2.7 Functors Between Higher Categories（p. 38、3 件）
  - 1.2.8 Joins of ∞-Categories（p. 40、4 件）
  - 1.2.9 Overcategories and Undercategories（p. 41、6 件）
  - 1.2.10 Fully Faithful and Essentially Surjective Functors（p. 43、2 件）
  - 1.2.11 Subcategories of ∞-Categories（p. 44、1 件）
  - 1.2.12 Initial and Final Objects（p. 44、9 件）
  - 1.2.13 Limits and Colimits（p. 46、8 件）
  - 1.2.14 Presentations of ∞-Categories（p. 49、3 件）
  - 1.2.15 Set-Theoretic Technicalities（p. 50、1 件）
  - 1.2.16 The ∞-Category of Spaces（p. 51、4 件）

### 第 2 章 Fibrations of Simplicial Sets（p. 53、177 件）

- 章の導入（`2.0.0.*`、7 件）
- 2.1 Left Fibrations（p. 55、34 件）
  - 2.1.1 Left Fibrations in Classical Category Theory（p. 55、6 件）
  - 2.1.2 Stability Properties of Left Fibrations（p. 60、11 件）
  - 2.1.3 A Characterization of Kan Fibrations（p. 66、5 件）
  - 2.1.4 The Covariant Model Structure（p. 68、12 件）
- 2.2 Simplicial Categories and ∞-Categories（p. 72、42 件）
  - 節の導入（`2.2.0.*`、1 件）
  - 2.2.1 The Straightening and Unstraightening Constructions (Unmarked Case)（p. 73、2 件）
  - 2.2.2 Straightening Over a Point（p. 74、13 件）
  - 2.2.3 Straightening of Right Fibrations（p. 79、15 件）
  - 2.2.4 The Comparison Theorem（p. 88、1 件）
  - 2.2.5 The Joyal Model Structure（p. 89、10 件）
- 2.3 Inner Fibrations（p. 95、39 件）
  - 節の導入（`2.3.0.*`、1 件）
  - 2.3.1 Correspondences（p. 96、5 件）
  - 2.3.2 Stability Properties of Inner Fibrations（p. 98、5 件）
  - 2.3.3 Minimal Fibrations（p. 101、8 件）
  - 2.3.4 n-Categories（p. 106、20 件）
- 2.4 Cartesian Fibrations（p. 114、55 件）
  - 2.4.1 Cartesian Morphisms（p. 115、12 件）
  - 2.4.2 Cartesian Fibrations（p. 121、14 件）
  - 2.4.3 Stability Properties of Cartesian Fibrations（p. 127、2 件）
  - 2.4.4 Mapping Spaces and Cartesian Fibrations（p. 130、9 件）
  - 2.4.5 Application: Invariance of Undercategories（p. 134、1 件）
  - 2.4.6 Application: Categorical Fibrations over a Point（p. 136、5 件）
  - 2.4.7 Bifibrations（p. 139、12 件）

### 第 3 章 The ∞-Category of ∞-Categories（p. 144、128 件）

- 章の導入（`3.0.0.*`、5 件）
- 3.1 Marked Simplicial Sets（p. 146、38 件）
  - 節の導入（`3.1.0.*`、2 件）
  - 3.1.1 Marked Anodyne Morphisms（p. 147、11 件）
  - 3.1.2 Stability Properties of Marked Anodyne Morphisms（p. 151、3 件）
  - 3.1.3 The Cartesian Model Structure（p. 154、9 件）
  - 3.1.4 Properties of the Cartesian Model Structure（p. 160、6 件）
  - 3.1.5 Comparison of Model Categories（p. 163、7 件）
- 3.2 Straightening and Unstraightening（p. 168、58 件）
  - 節の導入（`3.2.0.*`、1 件）
  - 3.2.1 The Straightening Functor（p. 170、16 件）
  - 3.2.2 Cartesian Fibrations over a Simplex（p. 178、14 件）
  - 3.2.3 Straightening over a Simplex（p. 187、4 件）
  - 3.2.4 Straightening in the General Case（p. 192、2 件）
  - 3.2.5 The Relative Nerve（p. 195、21 件）
- 3.3 Applications（p. 204、27 件）
  - 3.3.1 Structure Theory for Cartesian Fibrations（p. 204、8 件）
  - 3.3.2 Universal Fibrations（p. 210、8 件）
  - 3.3.3 Limits of ∞-Categories（p. 214、5 件）
  - 3.3.4 Colimits of ∞-Categories（p. 217、6 件）

### 第 4 章 Limits and Colimits（p. 222、162 件）

- 4.1 Cofinality（p. 222、34 件）
  - 4.1.1 Cofinal Maps（p. 223、13 件）
  - 4.1.2 Smoothness and Right Anodyne Maps（p. 228、18 件）
  - 4.1.3 Quillen’s Theorem A for ∞-Categories（p. 236、3 件）
- 4.2 Techniques for Computing Colimits（p. 239、40 件）
  - 4.2.1 Alternative Join and Slice Constructions（p. 239、9 件）
  - 4.2.2 Parametrized Colimits（p. 242、7 件）
  - 4.2.3 Decomposition of Diagrams（p. 248、16 件）
  - 4.2.4 Homotopy Colimits（p. 257、8 件）
- 4.3 Kan Extensions（p. 260、44 件）
  - 4.3.1 Relative Colimits（p. 260、16 件）
  - 4.3.2 Kan Extensions along Inclusions（p. 271、18 件）
  - 4.3.3 Kan Extensions along General Functors（p. 285、10 件）
- 4.4 Examples of Colimits（p. 292、44 件）
  - 4.4.1 Coproducts（p. 293、1 件）
  - 4.4.2 Pushouts（p. 294、9 件）
  - 4.4.3 Coequalizers（p. 299、3 件）
  - 4.4.4 Tensoring with Spaces（p. 300、10 件）
  - 4.4.5 Retracts and Idempotents（p. 303、21 件）

### 第 5 章 Presentable and Accessible ∞-Categories（p. 314、427 件）

- 章の導入（`5.0.0.*`、1 件）
- 5.1 ∞-Categories of Presheaves（p. 315、39 件）
  - 節の導入（`5.1.0.*`、2 件）
  - 5.1.1 Other Models for P(S)（p. 316、1 件）
  - 5.1.2 Colimits in ∞-Categories of Functors（p. 317、4 件）
  - 5.1.3 Yoneda’s Lemma（p. 319、2 件）
  - 5.1.4 Idempotent Completions（p. 321、10 件）
  - 5.1.5 The Universal Property of P(S)（p. 324、8 件）
  - 5.1.6 Complete Compactness（p. 328、12 件）
- 5.2 Adjoint Functors（p. 334、77 件）
  - 5.2.1 Correspondences and Associated Functors（p. 335、6 件）
  - 5.2.2 Adjunctions（p. 340、12 件）
  - 5.2.3 Preservation of Limits and Colimits（p. 345、6 件）
  - 5.2.4 Examples of Adjoint Functors（p. 350、7 件）
  - 5.2.5 Adjoint Functors and Overcategories（p. 354、5 件）
  - 5.2.6 Uniqueness of Adjoint Functors（p. 359、7 件）
  - 5.2.7 Localization Functors（p. 364、12 件）
  - 5.2.8 Factorization Systems（p. 369、22 件）
- 5.3 ∞-Categories of Inductive Limits（p. 379、82 件）
  - 節の導入（`5.3.0.*`、1 件）
  - 5.3.1 Filtered ∞-Categories（p. 381、22 件）
  - 5.3.2 Right Exactness（p. 389、11 件）
  - 5.3.3 Filtered Colimits（p. 393、3 件）
  - 5.3.4 Compact Objects（p. 395、18 件）
  - 5.3.5 Ind-Objects（p. 403、16 件）
  - 5.3.6 Adjoining Colimits to ∞-Categories（p. 411、11 件）
- 5.4 Accessible ∞-Categories（p. 417、75 件）
  - 5.4.1 Locally Small ∞-Categories（p. 418、8 件）
  - 5.4.2 Accessibility（p. 423、18 件）
  - 5.4.3 Accessibility and Idempotent Completeness（p. 428、6 件）
  - 5.4.4 Accessibility of Functor ∞-Categories（p. 431、3 件）
  - 5.4.5 Accessibility of Undercategories（p. 434、16 件）
  - 5.4.6 Accessibility of Fiber Products（p. 443、7 件）
  - 5.4.7 Applications（p. 449、17 件）
- 5.5 Presentable ∞-Categories（p. 456、153 件）
  - 節の導入（`5.5.0.*`、2 件）
  - 5.5.1 Presentability（p. 457、9 件）
  - 5.5.2 Representable Functors and the Adjoint Functor Theorem（p. 462、10 件）
  - 5.5.3 Limits and Colimits of Presentable ∞-Categories（p. 466、18 件）
  - 5.5.4 Local Objects（p. 472、20 件）
  - 5.5.5 Factorization Systems on Presentable ∞-Categories（p. 485、14 件）
  - 5.5.6 Truncated Objects（p. 492、28 件）
  - 5.5.7 Compactly Generated ∞-Categories（p. 501、11 件）
  - 5.5.8 Nonabelian Derived Categories（p. 505、26 件）
  - 5.5.9 Quillen’s Model for $P_{\Sigma}(\mathcal{C})$（p. 516、15 件）

### 第 6 章 ∞-Topoi（p. 527、297 件）

- 6.1 ∞-Topoi: Definitions and Characterizations（p. 528、67 件）
  - 節の導入（`6.1.0.*`、7 件）
  - 6.1.1 Giraud’s Axioms in the ∞-Categorical Setting（p. 530、6 件）
  - 6.1.2 Groupoid Objects（p. 535、15 件）
  - 6.1.3 ∞-Topoi and Descent（p. 544、20 件）
  - 6.1.4 Free Groupoids（p. 556、8 件）
  - 6.1.5 Giraud’s Theorem for ∞-Topoi（p. 560、3 件）
  - 6.1.6 ∞-Topoi and Classifying Objects（p. 565、8 件）
- 6.2 Constructions of ∞-Topoi（p. 570、51 件）
  - 6.2.1 Left Exact Localizations（p. 571、6 件）
  - 6.2.2 Grothendieck Topologies and Sheaves in Higher Category Theory（p. 577、18 件）
  - 6.2.3 Effective Epimorphisms（p. 586、21 件）
  - 6.2.4 Canonical Topologies（p. 595、6 件）
- 6.3 The ∞-Category of ∞-Topoi（p. 600、71 件）
  - 6.3.1 Geometric Morphisms（p. 600、13 件）
  - 6.3.2 Colimits of ∞-Topoi（p. 603、3 件）
  - 6.3.3 Filtered Limits of ∞-Topoi（p. 604、8 件）
  - 6.3.4 General Limits of ∞-Topoi（p. 610、10 件）
  - 6.3.5 Étale Morphisms of ∞-Topoi（p. 616、28 件）
  - 6.3.6 Structure Theory for ∞-Topoi（p. 635、9 件）
- 6.4 n-Topoi（p. 638、42 件）
  - 6.4.1 Characterizations of n-Topoi（p. 639、8 件）
  - 6.4.2 0-Topoi and Locales（p. 642、7 件）
  - 6.4.3 Giraud’s Axioms for n-Topoi（p. 644、8 件）
  - 6.4.4 n-Topoi and Descent（p. 649、9 件）
  - 6.4.5 Localic ∞-Topoi（p. 654、10 件）
- 6.5 Homotopy Theory in an ∞-Topos（p. 657、66 件）
  - 節の導入（`6.5.0.*`、1 件）
  - 6.5.1 Homotopy Groups（p. 658、20 件）
  - 6.5.2 ∞-Connectedness（p. 665、22 件）
  - 6.5.3 Hypercoverings（p. 674、14 件）
  - 6.5.4 Descent versus Hyperdescent（p. 681、9 件）

### 第 7 章 Higher Topos Theory in Topology（p. 688、203 件）

- 7.1 Paracompact Spaces（p. 689、55 件）
  - 節の導入（`7.1.0.*`、2 件）
  - 7.1.1 Some Point-Set Topology（p. 690、4 件）
  - 7.1.2 Spaces over X（p. 692、3 件）
  - 7.1.3 The Sheaf Condition（p. 694、15 件）
  - 7.1.4 The Main Result（p. 698、5 件）
  - 7.1.5 Base Change（p. 703、10 件）
  - 7.1.6 Higher Topoi and Shape Theory（p. 713、16 件）
- 7.2 Dimension Theory（p. 717、77 件）
  - 7.2.1 Homotopy Dimension（p. 717、17 件）
  - 7.2.2 Cohomological Dimension（p. 724、31 件）
  - 7.2.3 Covering Dimension（p. 737、7 件）
  - 7.2.4 Heyting Dimension（p. 741、22 件）
- 7.3 The Proper Base Change Theorem（p. 749、71 件）
  - 7.3.1 Proper Maps of ∞-Topoi（p. 750、19 件）
  - 7.3.2 Closed Subtopoi（p. 757、13 件）
  - 7.3.3 Products of ∞-Topoi（p. 763、9 件）
  - 7.3.4 Sheaves on Locally Compact Spaces（p. 768、13 件）
  - 7.3.5 Sheaves on Coherent Spaces（p. 777、4 件）
  - 7.3.6 Cell-Like Maps（p. 780、13 件）

### 付録 A（p. 787、226 件）

- A.1 Category Theory（p. 787、37 件）
  - A.1.1 Compactness and Presentability（p. 788、4 件）
  - A.1.2 Lifting Problems and the Small Object Argument（p. 789、8 件）
  - A.1.3 Monoidal Categories（p. 792、7 件）
  - A.1.4 Enriched Category Theory（p. 796、5 件）
  - A.1.5 Trees（p. 799、13 件）
- A.2 Model Categories（p. 809、74 件）
  - A.2.1 The Model Category Axioms（p. 810、2 件）
  - A.2.2 The Homotopy Category of a Model Category（p. 811、2 件）
  - A.2.3 A Lifting Criterion（p. 812、1 件）
  - A.2.4 Left Properness and Homotopy Pushout Squares（p. 814、5 件）
  - A.2.5 Quillen Adjunctions and Quillen Equivalences（p. 817、1 件）
  - A.2.6 Combinatorial Model Categories（p. 818、16 件）
  - A.2.7 Simplicial Sets（p. 827、4 件）
  - A.2.8 Diagram Categories and Homotopy (Co)limits（p. 829、12 件）
  - A.2.9 Reedy Model Structures（p. 835、31 件）
- A.3 Simplicial Categories（p. 850、115 件）
  - A.3.1 Enriched and Monoidal Model Categories（p. 851、12 件）
  - A.3.2 The Model Structure on S-Enriched Categories（p. 856、28 件）
  - A.3.3 Model Structures on Diagram Categories（p. 869、17 件）
  - A.3.4 Path Spaces in S-Enriched Categories（p. 884、15 件）
  - A.3.5 Homotopy Colimits of S-Enriched Categories（p. 891、15 件）
  - A.3.6 Exponentiation in Model Categories（p. 897、18 件）
  - A.3.7 Localizations of Simplicial Model Categories（p. 905、10 件）

- Bibliography（p. 915）
- General Index（p. 921）
- Index of Notation（p. 929）

## kind 別件数

| kind | 1 | 2 | 3 | 4 | 5 | 6 | 7 | A | 計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Construction | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| Convention | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| Corollary | 2 | 26 | 20 | 34 | 32 | 15 | 29 | 17 | 175 |
| Counterexample | 0 | 0 | 0 | 1 | 0 | 3 | 0 | 0 | 4 |
| Definition | 20 | 14 | 10 | 12 | 41 | 34 | 25 | 29 | 185 |
| Example | 16 | 12 | 1 | 5 | 30 | 7 | 16 | 26 | 113 |
| Fact | 0 | 1 | 0 | 0 | 0 | 2 | 0 | 0 | 3 |
| Lemma | 0 | 27 | 15 | 24 | 113 | 65 | 29 | 37 | 310 |
| Notation | 3 | 2 | 6 | 4 | 10 | 10 | 3 | 7 | 45 |
| Proposition | 19 | 48 | 38 | 51 | 105 | 71 | 23 | 39 | 394 |
| Remark | 45 | 42 | 33 | 26 | 90 | 78 | 63 | 67 | 444 |
| Theorem | 1 | 4 | 2 | 2 | 3 | 9 | 10 | 3 | 34 |
| Variant | 0 | 0 | 0 | 2 | 0 | 0 | 0 | 0 | 2 |
| Warning | 3 | 1 | 3 | 1 | 3 | 2 | 5 | 1 | 19 |
| 計 | 110 | 177 | 128 | 162 | 427 | 297 | 203 | 226 | 1730 |

## 引用表の照合

| 入力 | 項目に一致（行数／番号数） | 目次の見出しに一致（行数／番号数） | 原典に番号なし（行数／番号数） |
| --- | ---: | ---: | ---: |
| `citations.csv` | 1,359／64 | 1,015／26 | 0／0 |
| `plan-citations.csv` | 158／51 | 64／30 | 1／1 |

`items.csv` に行がない番号は以下のとおり。括弧内は引用行数。

- `citations.csv` の見出し参照は `1.1.5` (10), `1.2.2` (5), `1.2.3` (34), `1.2.4` (5), `1.2.8` (243), `1.2.10` (6), `1.2.12` (114), `1.2.13` (444), `2.1.1` (1), `2.1.2` (31), `2.2` (37), `4.1` (1), `4.1.1` (29), `4.3.2` (6), `4.4.5` (3), `5.1.3` (4), `5.1.4` (2), `5.2` (8), `5.2.2` (1), `5.2.7` (2), `5.3.4` (1), `5.4.2` (9), `5.5.1` (3), `5.5.3` (2), `5.5.4` (12), `5.5.8` (2)。
- `plan-citations.csv` の見出し参照は `1.1.5` (2), `1.2.3` (2), `1.2.8` (2), `1.2.10` (1), `2.2` (1), `2.4.1` (1), `2.4.4` (1), `3.2` (5), `3.3.3` (2), `4.1.3` (1), `4.3` (1), `5.1.3` (2), `5.1.4` (4), `5.1.5` (3), `5.2` (2), `5.2.4` (3), `5.2.7` (2), `5.3.1` (1), `5.3.3` (3), `5.3.4` (3), `5.4` (4), `5.5` (3), `5.5.1` (1), `5.5.2` (1), `5.5.8` (3), `5.5.9` (1), `6.2.2` (6), `6.4` (1), `6.5.1` (1), `6.5.2` (1)。
- 原典に番号がない引用は `plan-citations.csv` の `3.0` (1) のみ。引用元は [infinity-core-F1.md の 225 行目](../../formalization-plans/archive/stage-i/infinity-lanes/infinity-core-F1.md#L225)。第 3 章の導入部に `3.0` の見出しはない。
- 番号が一致する引用のうち、Lean 側の 3 行は `2.1.2.2` を Proposition と記す。項目表の kind は原典の Corollary を採用した。
- `goal` の内訳は BS 17 件、inf 33 件、K 1 件、`-` 1,679 件。
