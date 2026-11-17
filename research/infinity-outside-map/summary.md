# InfinityCategoriesの外にある一般論のファイル分類（⑤d、2026-11-16）

指示書：`formalization-plans/stage-ii/consolidation/infinity-outside-map.md`。最新main **`8c75c2ee8`** から枝 **`codex/infinity-outside-map`** を切った。対象はKST・HomotopicalAlgebra・SpectraのLeanファイル全体。EInfinityおよびArchiveは分類対象に含めない。

## 結果

**10,071ファイル・800,964行を1ファイル1行で分類した。** `files.csv` は指定の8列を持ち、全行に主な宣言の型または再公開先、docstringと判定理由を記録する。分類は主な型の対象と用途による配置案であり、定理の正しさ・原典の全項目の完成・実際の移動の完了の判定ではない。Leanの起動・ビルド・ソース変更はしていない。

| 分類 | 本数 | 行数 | 外部importありの本数 | InfinityCategoriesからのimportあり |
|---|---|---|---|---|
| 一般の ∞ 圏論 | 1725 | 135433 | 168 | 152 |
| 一般のホモトピー論・モデル圏 | 2415 | 209768 | 211 | 143 |
| 模型 | 3776 | 274811 | 80 | 65 |
| K 理論に固有 | 912 | 73347 | 14 | 14 |
| 未定 | 1243 | 107605 | 18 | 3 |
| 合計 | 10071 | 800964 | 491 | 377 |

同じファイルに一般補題と利用側の構成が同居する場合、主型が具体的なΩスペクトル・対称スペクトル・厳密dg圏に固定されるものは模型、S構成やK群そのものが出るものはK固有とする。一般の部分とBF段の専用比較が混ざり、移動単位を確定できないものは未定。KST配下であること自体をK固有の根拠にはしない。

## 範囲と行数

| 範囲 | ファイル数 | 行数 | Git subtree |
|---|---|---|---|
| KST | 8645 | 667013 | aced2e5f84b10228f8c600d3d6b2a3d3ead3e7a4 |
| HomotopicalAlgebra | 1147 | 109269 | 1b76c7169d0cc6693574127c0cdea27655141f6c |
| Spectra | 279 | 24682 | f577b4859e7c21868c07e1eea4e78b3dd4f40543 |

`lines` はUTF-8ソースの `splitlines()` の件数で、コメント・空行を含む。型・docstring・importの静的読取りだけを行った。`Archive` というパス成分を持つソースは対象にも利用側集計にも含めない。

## 分類方法とCSVの読み方

- 全ファイルから公開宣言（def・abbrev・lemma・theorem・structure・class・instance等）の型、variableの仮定、module docstringを抽出した。コメントと文字列、括弧内の `:=` を区別し、証明本文の語を主張の型と取り違えないようにした。各行の `basis` の `L番号` はそのソースの1始まりの行番号。長い型は表示を省略し、一般性を判定するために使用した入力も併記する。
- 主型にS構成・K群・Kスペクトルの構成がある場合はK固有、ΩSpectrum・Sp・対称列／対称スペクトル・厳密dg圏／加群等の具体的対象に依存する場合は模型として抽出した。一般のモデル圏・Quillen・function complexは一般のホモトピー論・モデル圏に置く。純粋な通常の代数・幾何は自動的にK固有や∞圏一般論へ入れない。
- 任意のquasicategory・Kan複体・単体的圏の局所化、安定性、Hom、図式、cofinality等は対応する文献の節へ分類する。数式の型とdocstringから主題を選ぶ規則で全件を分類し、主なまとまり・境界例の型を個別に照合した。全10,071ファイルを人手で一行ずつ再証明したという意味ではない。
- `coverage_items` は対応表にある**番号だけ**。元の文献属性・docstring・対応表の宣言リンクによる番号に加えて、同じ構成を実装する補助層には定義・構成の番号を案として付けた。したがって、補助法則のファイル1本がその番号の定理全体に一致する、または完成している、とは解釈しない。特別な模型のファイルに番号が付く場合も一般の主張への比較が済んだことを意味しない。対応表の状態列は使用・複製しない。
- `destination` はディレクトリ案。一般の∞圏論はInfinityCategoriesのHAまたはKerodonの該当する節を指定した。既存ファイルとの同名衝突、namespaceの改名、依存の切り分けは移動を実施する段階の作業であり、この分類では適用しない。
- `external_importers` は、そのファイルの**上位の対象ディレクトリ**（KST／HomotopicalAlgebra／Spectra）の外から、そのmoduleを直接importするプロジェクト内Leanファイルの異なる本数。配下の別サブディレクトリからのimportは内部として数える。InfinityCategories・EInfinity・root `SerrePositivity.lean` は利用側に含む。推移的importや文字列参照は数えず、Mathlib・drafts・research・Archiveは利用側に含めない。
- 宣言なしの単独再公開入口は、再公開先の型が対象内で確定する場合にその分類を継ぐ。複数の主題をまとめる入口や対象外への互換入口は未定とし、理由を残した。

宣言を持たない入口は163本、単独の再公開先から分類を継いだものは121本。import集計は基準mainの非Archiveのプロジェクトモジュール33,254本を読み取り、同一利用側の重複importを一つに数えた。

## サブディレクトリごとの本数・行数

各セルは **本数 / 行数**。ここは各対象の直下のサブディレクトリで排他的に集計し、深い配下も含む。`(直下)` は対象ディレクトリに直接置かれた入口等。

| サブディレクトリ | 一般の ∞ 圏論 | 一般のホモトピー論・モデル圏 | 模型 | K 理論に固有 | 未定 | 計 |
|---|---|---|---|---|---|---|
| SerrePositivity/HomotopicalAlgebra/(直下) | 0 / 0 | 1 / 84 | 0 / 0 | 0 / 0 | 2 / 499 | 3 / 583 |
| SerrePositivity/HomotopicalAlgebra/Diagram | 20 / 1,074 | 109 / 8,217 | 0 / 0 | 0 / 0 | 0 / 0 | 129 / 9,291 |
| SerrePositivity/HomotopicalAlgebra/Enriched | 0 / 0 | 5 / 373 | 0 / 0 | 0 / 0 | 0 / 0 | 5 / 373 |
| SerrePositivity/HomotopicalAlgebra/Generated | 0 / 0 | 3 / 213 | 0 / 0 | 0 / 0 | 0 / 0 | 3 / 213 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex | 7 / 509 | 150 / 14,097 | 0 / 0 | 0 / 0 | 2 / 20 | 159 / 14,626 |
| SerrePositivity/HomotopicalAlgebra/Localization | 1 / 150 | 59 / 4,776 | 0 / 0 | 0 / 0 | 0 / 0 | 60 / 4,926 |
| SerrePositivity/HomotopicalAlgebra/Monoidal | 0 / 0 | 16 / 1,232 | 0 / 0 | 0 / 0 | 0 / 0 | 16 / 1,232 |
| SerrePositivity/HomotopicalAlgebra/Pointed | 0 / 0 | 6 / 642 | 0 / 0 | 0 / 0 | 0 / 0 | 6 / 642 |
| SerrePositivity/HomotopicalAlgebra/Quillen | 0 / 0 | 19 / 1,547 | 0 / 0 | 0 / 0 | 0 / 0 | 19 / 1,547 |
| SerrePositivity/HomotopicalAlgebra/Rectification | 7 / 759 | 403 / 50,552 | 0 / 0 | 0 / 0 | 5 / 602 | 415 / 51,913 |
| SerrePositivity/HomotopicalAlgebra/Replacement | 0 / 0 | 2 / 225 | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 225 |
| SerrePositivity/HomotopicalAlgebra/Simplicial | 47 / 4,408 | 234 / 15,126 | 0 / 0 | 0 / 0 | 3 / 72 | 284 / 19,606 |
| SerrePositivity/HomotopicalAlgebra/Smith | 2 / 296 | 35 / 2,998 | 0 / 0 | 0 / 0 | 0 / 0 | 37 / 3,294 |
| SerrePositivity/HomotopicalAlgebra/Topological | 0 / 0 | 2 / 169 | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 169 |
| SerrePositivity/HomotopicalAlgebra/Transfer | 0 / 0 | 5 / 434 | 0 / 0 | 0 / 0 | 0 / 0 | 5 / 434 |
| SerrePositivity/HomotopicalAlgebra/Under | 0 / 0 | 2 / 195 | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 195 |
| SerrePositivity/KST/(直下) | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 10 / 9,040 | 10 / 9,040 |
| SerrePositivity/KST/Comparison | 76 / 6,709 | 175 / 17,016 | 19 / 1,954 | 0 / 0 | 10 / 917 | 280 / 26,596 |
| SerrePositivity/KST/DerivedBlowup | 0 / 0 | 0 / 0 | 146 / 11,697 | 0 / 0 | 197 / 16,030 | 343 / 27,727 |
| SerrePositivity/KST/DerivedGeometry | 5 / 304 | 14 / 1,048 | 23 / 2,736 | 0 / 0 | 296 / 24,505 | 338 / 28,593 |
| SerrePositivity/KST/Descent | 4 / 374 | 17 / 2,115 | 0 / 0 | 0 / 0 | 169 / 18,601 | 190 / 21,090 |
| SerrePositivity/KST/Fibration | 348 / 24,090 | 61 / 4,368 | 18 / 1,275 | 227 / 16,589 | 15 / 729 | 669 / 47,051 |
| SerrePositivity/KST/LocalizingInvariants | 284 / 21,286 | 60 / 4,634 | 1309 / 84,928 | 50 / 3,575 | 115 / 6,255 | 1818 / 120,678 |
| SerrePositivity/KST/NonConnective | 8 / 557 | 1 / 27 | 171 / 13,964 | 80 / 7,659 | 6 / 314 | 266 / 22,521 |
| SerrePositivity/KST/ProExcision | 15 / 1,141 | 87 / 7,386 | 58 / 4,084 | 0 / 0 | 150 / 12,270 | 310 / 24,881 |
| SerrePositivity/KST/SConstruction | 561 / 44,754 | 414 / 30,985 | 1243 / 88,293 | 552 / 45,273 | 185 / 10,842 | 2955 / 220,147 |
| SerrePositivity/KST/Spectra | 340 / 29,022 | 488 / 36,782 | 564 / 46,468 | 3 / 251 | 71 / 6,166 | 1466 / 118,689 |
| SerrePositivity/Spectra/(直下) | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 2 / 350 | 2 / 350 |
| SerrePositivity/Spectra/General | 0 / 0 | 1 / 72 | 44 / 3,600 | 0 / 0 | 1 / 27 | 46 / 3,699 |
| SerrePositivity/Spectra/ModelCategory | 0 / 0 | 8 / 552 | 16 / 1,320 | 0 / 0 | 0 / 0 | 24 / 1,872 |
| SerrePositivity/Spectra/Pointed | 0 / 0 | 21 / 2,511 | 0 / 0 | 0 / 0 | 2 / 349 | 23 / 2,860 |
| SerrePositivity/Spectra/PointedSimplicialSet | 0 / 0 | 10 / 594 | 0 / 0 | 0 / 0 | 0 / 0 | 10 / 594 |
| SerrePositivity/Spectra/Stable | 0 / 0 | 0 / 0 | 17 / 1,545 | 0 / 0 | 0 / 0 | 17 / 1,545 |
| SerrePositivity/Spectra/SymmetricSequence | 0 / 0 | 7 / 798 | 70 / 6,798 | 0 / 0 | 2 / 17 | 79 / 7,613 |
| SerrePositivity/Spectra/SymmetricSpectrum | 0 / 0 | 0 / 0 | 78 / 6,149 | 0 / 0 | 0 / 0 | 78 / 6,149 |

<details>
<summary>実際の親ディレクトリごとの詳細（深いサブディレクトリを別計上）</summary>

| 親ディレクトリ | 分類 | 本数 | 行数 |
|---|---|---|---|
| SerrePositivity/HomotopicalAlgebra | 一般のホモトピー論・モデル圏 | 1 | 84 |
| SerrePositivity/HomotopicalAlgebra | 未定 | 2 | 499 |
| SerrePositivity/HomotopicalAlgebra/Diagram | 一般の ∞ 圏論 | 20 | 1074 |
| SerrePositivity/HomotopicalAlgebra/Diagram | 一般のホモトピー論・モデル圏 | 109 | 8217 |
| SerrePositivity/HomotopicalAlgebra/Enriched | 一般のホモトピー論・モデル圏 | 5 | 373 |
| SerrePositivity/HomotopicalAlgebra/Generated | 一般のホモトピー論・モデル圏 | 3 | 213 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex | 一般の ∞ 圏論 | 1 | 75 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex | 一般のホモトピー論・モデル圏 | 72 | 6655 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex | 未定 | 2 | 20 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy | 一般の ∞ 圏論 | 6 | 434 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy | 一般のホモトピー論・モデル圏 | 78 | 7442 |
| SerrePositivity/HomotopicalAlgebra/Localization | 一般の ∞ 圏論 | 1 | 150 |
| SerrePositivity/HomotopicalAlgebra/Localization | 一般のホモトピー論・モデル圏 | 59 | 4776 |
| SerrePositivity/HomotopicalAlgebra/Monoidal | 一般のホモトピー論・モデル圏 | 16 | 1232 |
| SerrePositivity/HomotopicalAlgebra/Pointed | 一般のホモトピー論・モデル圏 | 6 | 642 |
| SerrePositivity/HomotopicalAlgebra/Quillen | 一般のホモトピー論・モデル圏 | 19 | 1547 |
| SerrePositivity/HomotopicalAlgebra/Rectification | 未定 | 1 | 452 |
| SerrePositivity/HomotopicalAlgebra/Rectification/CategoryTheory | 一般の ∞ 圏論 | 1 | 122 |
| SerrePositivity/HomotopicalAlgebra/Rectification/CategoryTheory | 一般のホモトピー論・モデル圏 | 7 | 605 |
| SerrePositivity/HomotopicalAlgebra/Rectification/CategoryTheory/Presentation | 一般のホモトピー論・モデル圏 | 15 | 1503 |
| SerrePositivity/HomotopicalAlgebra/Rectification/CategoryTheory/Quiver | 一般のホモトピー論・モデル圏 | 2 | 179 |
| SerrePositivity/HomotopicalAlgebra/Rectification/HomotopyFunctionComplex | 一般の ∞ 圏論 | 1 | 103 |
| SerrePositivity/HomotopicalAlgebra/Rectification/HomotopyFunctionComplex | 一般のホモトピー論・モデル圏 | 266 | 34660 |
| SerrePositivity/HomotopicalAlgebra/Rectification/HomotopyFunctionComplex | 未定 | 1 | 38 |
| SerrePositivity/HomotopicalAlgebra/Rectification/Simplicial | 一般の ∞ 圏論 | 5 | 534 |
| SerrePositivity/HomotopicalAlgebra/Rectification/Simplicial | 一般のホモトピー論・モデル圏 | 113 | 13605 |
| SerrePositivity/HomotopicalAlgebra/Rectification/Simplicial | 未定 | 3 | 112 |
| SerrePositivity/HomotopicalAlgebra/Replacement | 一般のホモトピー論・モデル圏 | 2 | 225 |
| SerrePositivity/HomotopicalAlgebra/Simplicial | 一般の ∞ 圏論 | 47 | 4408 |
| SerrePositivity/HomotopicalAlgebra/Simplicial | 一般のホモトピー論・モデル圏 | 234 | 15126 |
| SerrePositivity/HomotopicalAlgebra/Simplicial | 未定 | 3 | 72 |
| SerrePositivity/HomotopicalAlgebra/Smith | 一般の ∞ 圏論 | 2 | 296 |
| SerrePositivity/HomotopicalAlgebra/Smith | 一般のホモトピー論・モデル圏 | 35 | 2998 |
| SerrePositivity/HomotopicalAlgebra/Topological | 一般のホモトピー論・モデル圏 | 2 | 169 |
| SerrePositivity/HomotopicalAlgebra/Transfer | 一般のホモトピー論・モデル圏 | 5 | 434 |
| SerrePositivity/HomotopicalAlgebra/Under | 一般のホモトピー論・モデル圏 | 2 | 195 |
| SerrePositivity/KST | 未定 | 10 | 9040 |
| SerrePositivity/KST/Comparison | 一般の ∞ 圏論 | 76 | 6709 |
| SerrePositivity/KST/Comparison | 一般のホモトピー論・モデル圏 | 175 | 17016 |
| SerrePositivity/KST/Comparison | 模型 | 19 | 1954 |
| SerrePositivity/KST/Comparison | 未定 | 10 | 917 |
| SerrePositivity/KST/DerivedBlowup | 模型 | 146 | 11697 |
| SerrePositivity/KST/DerivedBlowup | 未定 | 197 | 16030 |
| SerrePositivity/KST/DerivedGeometry | 一般の ∞ 圏論 | 5 | 304 |
| SerrePositivity/KST/DerivedGeometry | 一般のホモトピー論・モデル圏 | 14 | 1048 |
| SerrePositivity/KST/DerivedGeometry | 模型 | 6 | 782 |
| SerrePositivity/KST/DerivedGeometry | 未定 | 296 | 24505 |
| SerrePositivity/KST/DerivedGeometry/DGResolution | 模型 | 17 | 1954 |
| SerrePositivity/KST/Descent | 一般の ∞ 圏論 | 4 | 374 |
| SerrePositivity/KST/Descent | 一般のホモトピー論・モデル圏 | 17 | 2115 |
| SerrePositivity/KST/Descent | 未定 | 169 | 18601 |
| SerrePositivity/KST/Fibration | 一般の ∞ 圏論 | 330 | 22303 |
| SerrePositivity/KST/Fibration | 一般のホモトピー論・モデル圏 | 61 | 4368 |
| SerrePositivity/KST/Fibration | 模型 | 14 | 994 |
| SerrePositivity/KST/Fibration | K 理論に固有 | 221 | 15985 |
| SerrePositivity/KST/Fibration | 未定 | 11 | 647 |
| SerrePositivity/KST/Fibration/Relative | 一般の ∞ 圏論 | 18 | 1787 |
| SerrePositivity/KST/Fibration/Relative | 模型 | 4 | 281 |
| SerrePositivity/KST/Fibration/Relative | K 理論に固有 | 6 | 604 |
| SerrePositivity/KST/Fibration/Relative | 未定 | 4 | 82 |
| SerrePositivity/KST/LocalizingInvariants | 一般の ∞ 圏論 | 283 | 21239 |
| SerrePositivity/KST/LocalizingInvariants | 一般のホモトピー論・モデル圏 | 59 | 4577 |
| SerrePositivity/KST/LocalizingInvariants | 模型 | 1309 | 84928 |
| SerrePositivity/KST/LocalizingInvariants | K 理論に固有 | 49 | 3538 |
| SerrePositivity/KST/LocalizingInvariants | 未定 | 113 | 6225 |
| SerrePositivity/KST/LocalizingInvariants/CoreFlag | 一般の ∞ 圏論 | 1 | 47 |
| SerrePositivity/KST/LocalizingInvariants/CoreFlag | 一般のホモトピー論・モデル圏 | 1 | 57 |
| SerrePositivity/KST/LocalizingInvariants/CoreFlag | K 理論に固有 | 1 | 37 |
| SerrePositivity/KST/LocalizingInvariants/CoreFlag | 未定 | 2 | 30 |
| SerrePositivity/KST/NonConnective | 一般の ∞ 圏論 | 8 | 557 |
| SerrePositivity/KST/NonConnective | 一般のホモトピー論・モデル圏 | 1 | 27 |
| SerrePositivity/KST/NonConnective | 模型 | 171 | 13964 |
| SerrePositivity/KST/NonConnective | K 理論に固有 | 80 | 7659 |
| SerrePositivity/KST/NonConnective | 未定 | 6 | 314 |
| SerrePositivity/KST/ProExcision | 一般の ∞ 圏論 | 15 | 1141 |
| SerrePositivity/KST/ProExcision | 一般のホモトピー論・モデル圏 | 87 | 7386 |
| SerrePositivity/KST/ProExcision | 模型 | 58 | 4084 |
| SerrePositivity/KST/ProExcision | 未定 | 150 | 12270 |
| SerrePositivity/KST/SConstruction | 一般の ∞ 圏論 | 537 | 42747 |
| SerrePositivity/KST/SConstruction | 一般のホモトピー論・モデル圏 | 414 | 30985 |
| SerrePositivity/KST/SConstruction | 模型 | 1243 | 88293 |
| SerrePositivity/KST/SConstruction | K 理論に固有 | 469 | 38453 |
| SerrePositivity/KST/SConstruction | 未定 | 184 | 10808 |
| SerrePositivity/KST/SConstruction/Cofinality | 一般の ∞ 圏論 | 24 | 2007 |
| SerrePositivity/KST/SConstruction/Cofinality | K 理論に固有 | 83 | 6820 |
| SerrePositivity/KST/SConstruction/Cofinality | 未定 | 1 | 34 |
| SerrePositivity/KST/Spectra | 一般の ∞ 圏論 | 340 | 29022 |
| SerrePositivity/KST/Spectra | 一般のホモトピー論・モデル圏 | 488 | 36782 |
| SerrePositivity/KST/Spectra | 模型 | 548 | 44454 |
| SerrePositivity/KST/Spectra | K 理論に固有 | 3 | 251 |
| SerrePositivity/KST/Spectra | 未定 | 71 | 6166 |
| SerrePositivity/KST/Spectra/Limits | 模型 | 16 | 2014 |
| SerrePositivity/Spectra | 未定 | 2 | 350 |
| SerrePositivity/Spectra/General | 一般のホモトピー論・モデル圏 | 1 | 72 |
| SerrePositivity/Spectra/General | 模型 | 44 | 3600 |
| SerrePositivity/Spectra/General | 未定 | 1 | 27 |
| SerrePositivity/Spectra/ModelCategory | 一般のホモトピー論・モデル圏 | 8 | 552 |
| SerrePositivity/Spectra/ModelCategory | 模型 | 16 | 1320 |
| SerrePositivity/Spectra/Pointed | 一般のホモトピー論・モデル圏 | 21 | 2511 |
| SerrePositivity/Spectra/Pointed | 未定 | 2 | 349 |
| SerrePositivity/Spectra/PointedSimplicialSet | 一般のホモトピー論・モデル圏 | 10 | 594 |
| SerrePositivity/Spectra/Stable | 模型 | 17 | 1545 |
| SerrePositivity/Spectra/SymmetricSequence | 一般のホモトピー論・モデル圏 | 7 | 798 |
| SerrePositivity/Spectra/SymmetricSequence | 模型 | 70 | 6798 |
| SerrePositivity/Spectra/SymmetricSequence | 未定 | 2 | 17 |
| SerrePositivity/Spectra/SymmetricSpectrum | 模型 | 78 | 6149 |

</details>

## 一般の∞圏論の主なまとまりと移す先

### 零対象・安定性・余fiber・閉じた安定部分圏

364本・30,458行。移す先案：`SerrePositivity/InfinityCategories/HA/StableInfinityCategories/`。HA 1.1.1、1.1.3の定義・性質。Verdier商の分数やspan族を含む場合は局所化の節との分割も検討する。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/SimplexTerminalPullbackFamily.lean | terminalPullbackColumnVertex; exists_simplexTerminalPullbackFamily; L33 def terminalPullbackColumnVertex [Quasicategory X] [IsStable X] : (pullbackDiagrams X) _⦋0⦌ / L46 lemma exists_simplexTerminalPullbackFamily [Quasicategory X] [IsStable X] : ∃  | HA 1.1.1.1; HA 1.1.3.4 | 5 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/RelativeArrow.lean | relativeLatchingArrow; relativeMatchingArrow; L25 abbrev relativeLatchingArrow (j : J) [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] : Arrow (J ⥤ C) ⥤ Arrow C / L29 abbrev relativeMatchingArrow (j : J) [HasLimitsO | HA 1.1.1.1; HA 1.1.3.4 | 3 |
| SerrePositivity/HomotopicalAlgebra/Simplicial/EvaluationMorphismProperties.lean | detected; generators; L26 def detected (P : MorphismProperty C) : MorphismProperty D / L30 def generators (P : MorphismProperty C) : MorphismProperty D; 入力: variable {C : Type u} [Category.{v} C] {D : T | HA 1.1.1.1; HA 1.1.3.4 | 1 |

### necklace・coherent nerve・豊穣図式の復号

285本・22,523行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/ExamplesOfInfinityCategories/SimplicialCategories/`。任意の単体的圏／necklaceの構成とその法則。厳密dg圏のHomに固定された版は模型側に分ける。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/SConstruction/EnrichedFunctorCollageNerve.lean | EnrichedFunctorCollageCategory; enrichedFunctorCollage_simplicialCategory; L23 abbrev EnrichedFunctorCollageCategory (R : EnrichedFunctor SSet.{u} C D) / L27 instance enrichedFunctorCollage_simplicialCategory (R : EnrichedFunctor SSet.{u} C D) : Simplicia | HTT 1.1.5.5; Kerodon 2.4.5.1 | 1 |
| SerrePositivity/KST/Fibration/CoherentSimplexHomVertices.lean | simplicialHomVertex_comp; coherentTriangleLongHom; L18 theorem simplicialHomVertex_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : SimplicialCategory.homEquiv' X Z (f ≫ g) = (eComp SSet X Y Z).app (Opposite.op ⦋0⦌) (SimplicialCategory.h | HTT 1.1.5.5; Kerodon 2.4.5.1 | 0 |
| SerrePositivity/KST/LocalizingInvariants/CoherentCompositionConstantSimplex.lean | coherentComposition_constant_simplex; L22 lemma coherentComposition_constant_simplex {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : coherentCompositionSimplex (constant (Simp | HTT 1.1.5.5; Kerodon 2.4.5.1 | 0 |

### 完全関手・安定圏の射・Verdier列の一般部分

246本・18,114行。移す先案：`SerrePositivity/InfinityCategories/HA/StableInfinityCategories/`。HA 1.1.4の完全関手の補助層。NSやBGT・Tammeの分数定理そのものをHAの当該命題の完成としては数えない。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/LaxInclusions.lean | fromD; fromC; L27 def fromD : D.obj ⟶ (laxCategory p q).obj / L35 def fromC : C.obj ⟶ (laxCategory p q).obj; 入力: variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E) | HA 1.1.4.1 | 8 |
| SerrePositivity/KST/Fibration/FractionKanQuotientDescent.lean | fractionKanQuotientDiagram; fractionKanQuotientDiagram_restrictionIso; L19 def fractionKanQuotientDiagram : (SSet.uliftFunctor.{u + 1, u}).obj C.obj ⟶ SpaceInfinity.{u} / L25 def fractionKanQuotientDiagram_restrictionIso : FunctorIso ((SSet.uliftFunct | HA 1.1.4.1 | 2 |
| SerrePositivity/KST/SConstruction/ClosedPredicateOperations.lean | PreservesCofiberData.isExactFunctor; ClosedStablePredicate.comap; L21 lemma PreservesCofiberData.isExactFunctor {C D : SSet.{u}} {f : C ⟶ D} (hf : PreservesCofiberData f) : IsExactFunctor f / L26 def ClosedStablePredicate.comap {X Y : StableModel | HA 1.1.4.1 | 0 |

### Kan複体のπ群・基点・自然性・相対的計算

228本・19,324行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/HomotopyGroups/`。任意のKan複体の群を計算する層。Ωスペクトルの安定π群に固定された版は模型側。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/Spectra/UnbasedHomotopyIsomorphism.lean | curry_evaluation; transpose; L30 theorem curry_evaluation {A X : SSet.{u}} (h : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (t : Fin 2) : MonoidalClosed.curry h ≫ evaluation X t = (λ_ A).inv ≫ endpoint t ▷ A ≫ h / L38 def tran | Kerodon 3.2.1.1 | 3 |
| SerrePositivity/KST/Comparison/BarFundamentalComparison.lean | monoidBarFundamentalEquiv; stableHatGLBarFundamentalEquiv; L31 def monoidBarFundamentalEquiv (M : SimplicialObject MonCat.{u}) (hM : SimplicialMonoid.IsGrouplike M) : π₀ (monoidSpace M) ≃ KanHomotopyGroup (monoidBarKanPointed M).right 0 (m | Kerodon 3.2.1.1 | 0 |
| SerrePositivity/KST/Descent/MainAugmentedHomotopyLimit.lean | AugmentedLimitDiagram; underlyingAugmentationCone; L38 abbrev AugmentedLimitDiagram / L46 def underlyingAugmentationCone (A : AugmentedLimitDiagram I) : Cone (A.right ⋙ PointedSimplicialSet.forget); 入力: variable (I : Type u) [Small | Kerodon 3.2.1.1; Kerodon 7.5.4.1 | 0 |

### anodyne射・Kan充填と延長

111本・9,330行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/`。特定のBF模型に依存しない相対充填・延長の道具。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/HomotopicalAlgebra/Simplicial/AnodyneHomotopyLocalization.lean | endpoint_projection_zero; endpoint_projection_one; L47 lemma endpoint_projection_zero (X : SSet.{v}) : SSet.ι₀ ≫ fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) = 𝟙 X / L55 lemma endpoint_projection_one (X : SSet.{v}) : SSet.ι₁  | Kerodon 3.1.2.1; Kerodon 3.1.8.6 | 29 |
| SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanEndFibration.lean | bousfieldKanParameterSwap; bousfieldKanParameter_hasLiftingProperty; L25 def bousfieldKanParameterSwap (A : SSet.{u}) : ((pointwise K (curriedTensor SSet.{u})).obj A).obj (bousfieldKanWeight K) ≅ (weightedParameterFunctor (bousfieldKanWeight K)).obj | HTT 4.2.4.4; Kerodon 3.1.2.1 | 1 |
| SerrePositivity/KST/Comparison/PairContractionAnodyne.lean | intervalEndpoint_zero_eq; intervalEndpoint_one_eq; L33 @[simp] theorem intervalEndpoint_zero_eq (X : SSet.{u}) : intervalEndpoint X 0 = SSet.ι₁ / L42 @[simp] theorem intervalEndpoint_one_eq (X : SSet.{u}) : intervalEndpoint X 1 = S | Kerodon 3.1.2.1 | 1 |

### 関手∞圏・core・評価と自然変換

91本・7,275行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/TheLanguageOfInfinityCategories/FunctorsOfInfinityCategories/`。内部Homと実自然変換の一般法則。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/CoconeFamilyCoreComparison.lean | spanFunctorEdgeUnflip_invertsAllEdges; spanFunctorEdgeUnflipCoreHomotopy; L26 lemma spanFunctorEdgeUnflip_invertsAllEdges {K L X : SSet.{u}} [Quasicategory X] {F G : K ⟶ (ihom L).obj X} (l : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj ((ihom K) | Kerodon 1.5.3.1 | 4 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/ExtensionRestriction.lean | Map.degreeRestriction_naturality; ofFunctor_restriction; L20 lemma Map.degreeRestriction_naturality (m : Map d e τ) (hinj : Function.Injective r.deg) : Functor.whiskerLeft (lowerToUpper r j) (Functor.whiskerLeft (degreeIndex r j hinj) m. | Kerodon 1.5.3.1 | 0 |
| SerrePositivity/KST/DerivedGeometry/CechFunctorComparison.lean | alternatingCofaceCompMapIso; finiteCechFunctorIso; L30 def alternatingCofaceCompMapIso : AlgebraicTopology.alternatingCofaceMapComplex A ⋙ F.mapHomologicalComplex (.up ℕ) ≅ (CosimplicialObject.whiskering A B).obj F ⋙ AlgebraicTopol | Kerodon 1.5.3.1 | 0 |

### 輸送表現・straighteningの実単体計算

62本・4,038行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/`。5.6の比較の補助層。通常圏上のものは5.3、covariant transportそのものは5.2への細分も必要。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/Fibration/ScaffoldCocartesianBaseChange.lean | scaffoldCocartesianBaseChangeClassificationIso; scaffoldCocartesianBaseChangeClassificationIso_pointHom; L22 def scaffoldCocartesianBaseChangeClassificationIso : FunctorIso (cocartesianKanCoherentDiagram (pullback.snd p k)) ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfi | Kerodon 5.6.2.1 | 2 |

### Kan複体のhomotopy pullbackの一般計算

58本・4,184行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/HomotopyPullbackAndHomotopyPushoutSquares/`。具体的な代数やスペクトルに固定されない引き戻し・貼り合わせ。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/Comparison/ActionBarSquares.lean | actionBarBase; actionBarTotal; L33 abbrev actionBarBase (M : SimplicialObject MonCat.{u}) : SimplicialObject SSet.{u} / L42 abbrev actionBarTotal (M : SimplicialObject MonCat.{u}) : SimplicialObject SSet.{u} | Kerodon 3.4.1.1 | 0 |
| SerrePositivity/KST/Fibration/ContractibleBaseFiberComparison.lean | pointFiberToContractiblePullback; pointFiberToContractiblePullback_localized_isIso; L17 def pointFiberToContractiblePullback {X Y B : SSet.{u}} (f : X ⟶ B) (g : Y ⟶ B) (z : Δ[0] ⟶ Y) : homotopyPullbackObject f (z ≫ g) ⟶ homotopyPullbackObject f g / L23 theorem poi | Kerodon 3.4.1.1 | 0 |
| SerrePositivity/KST/SConstruction/ConnectedDiagramRetractions.lean | naturality_homotopyPullback_retraction_of_section_of_kan; naturality_homotopyPullback_retraction_of_section; L22 lemma naturality_homotopyPullback_retraction_of_section_of_kan {D : Type v} [Category.{w} D] {F G : D ⥤ SSet.{u}} (α : F ⟶ G) {d e : D} (s : d ⟶ e) (r : e ⟶ d) (hsr : s ≫ r = 𝟙 | Kerodon 3.4.1.1 | 0 |

### Bousfield–Kan end・重み付き極限・Totの一般部分

43本・2,934行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/`。任意の空間値図式の計算。BFの構造射や安定群との比較は模型側。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanDoubleOpposite.lean | bousfieldKanOpOpWeightSectionsIso; bousfieldKanOpOpIso; L24 def bousfieldKanOpOpWeightSectionsIso (H : I ⥤ SSet.{u}) : weightedSections (opOp I ⋙ bousfieldKanWeight Iᵒᵖᵒᵖ) H ≅ bousfieldKanHolim H / L34 def bousfieldKanOpOpIso (H : Iᵒᵖᵒᵖ | HTT 4.2.4.4; Kerodon 7.5.1.1 | 2 |
| SerrePositivity/KST/Descent/MainAugmentedWeightedEnd.lean | augmentationCone; weightedEndComparison; L37 def augmentationCone (A : AugmentedLimitDiagram I) : Cone A.right / L44 def weightedEndComparison (W : I ⥤ SSet.{u}) (A : AugmentedLimitDiagram I) : A.left ⟶ PointedWeightedEnd | Kerodon 7.5.1.1 | 0 |
| SerrePositivity/KST/SConstruction/CoherentDiagramFamilyPasting.lean | diagramFamilyTranspose; diagramUniversalFamily; L24 def diagramFamilyTranspose {I : Type u} [SmallCategory I] {W D : I ⥤ SSet.{u}} {P : SSet.{u}} (s : W ⊗ (Functor.const I).obj P ⟶ D) : W ⟶ D ⋙ ihom P / L37 def diagramUniversalF | Kerodon 7.5.1.1 | 0 |

### 通常の圏のnerveの法則

40本・3,336行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/TheLanguageOfInfinityCategories/FromCategoriesToSimplicialSets/`。反対圏・関手・自然変換のnerveの構成の補助。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/HomotopicalAlgebra/Simplicial/NerveHomotopy.lean | interval; hom; L48 abbrev interval : Fin 2 × C ⥤ D / L50 def hom : nerve C ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶ nerve D; 入力: variable {C D : Type u} [Category.{v} C] [Category | Kerodon 1.3.1.1 | 14 |
| SerrePositivity/HomotopicalAlgebra/Diagram/ElementsBousfieldKanWeight.lean | overOpUnderIso; overNerveIso; L22 def overOpUnderIso {K : Type w} [SmallCategory K] (e : K) : Cat.of (Over (Opposite.op e)) ≅ Cat.of ((Under e)ᵒᵖ) / L30 def overNerveIso : nerve (Over (Opposite.op e)) ≅ nerve ( | HTT 4.2.4.4; Kerodon 1.3.1.1 | 2 |
| SerrePositivity/KST/ProExcision/NerveOppositeIso.lean | oppositeNerveSimplexEquiv; nerveOppositeIso; L22 def oppositeNerveSimplexEquiv (n : ℕ) : ComposableArrows Cᵒᵖ n ≃ ComposableArrows C n / L32 def nerveOppositeIso : nerve Cᵒᵖ ≅ (nerve C).op; 入力: variable (C : Type u) [Category | Kerodon 1.3.1.1 | 3 |

### 辺集合に関する∞局所化と降下・一意性

35本・2,042行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/Localization/`。任意のquasicategoryと辺集合に対する主張。K理論の不変量の定義はK固有側。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/LocalizationFactorization.lean | localization_exists_factorization; localizationDescend; L22 lemma localization_exists_factorization {X Q Y : SSet.{u}} [Quasicategory Q] [Quasicategory Y] (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : IsLocalization F W) (H : X ⟶ Y) (hH : Invert | Kerodon 6.3.1.9 | 5 |
| SerrePositivity/KST/Fibration/GroupoidCompletionKanMaps.lean | groupoidCompletionMapOf_anodyneQ_isIso_iff; strictKanCompletion_map_isQCatEquivalence_of_groupoidCompletion; L16 theorem groupoidCompletionMapOf_anodyneQ_isIso_iff {X Y : SSet.{u}} (f : X ⟶ Y) : IsIso (AnodyneHomotopy.anodyneQ.map (groupoidCompletionMapOf f)) ↔ IsIso (AnodyneHomotopy.anod | Kerodon 6.3.1.9 | 1 |
| SerrePositivity/HomotopicalAlgebra/Rectification/Simplicial/SmallKanHomotopy.lean | Object; comp; L45 structure Object / L49 def comp {X Y Z : Object.{v}} (f : HomotopyClasses.obj X.value Y.value) (g : HomotopyClasses.obj Y.value Z.value) : HomotopyClasses.obj X.value Z.value;  | Kerodon 6.3.1.9 | 0 |

### 任意のquasicategoryの単体的道具

33本・2,612行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/TheLanguageOfInfinityCategories/InfinityCategories/`。内角充填・合成の具体的補助。定義1.4.0.1との関係として挙げ、独立の完成済み定理とはしない。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/PathComparisonSquare.lean | diagonal_eq; square; L25 lemma diagonal_eq : stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex = stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm (compositionDiagonalTransport s H).triangle.si | Kerodon 1.4.0.1 | 2 |
| SerrePositivity/KST/Fibration/FixedRestrictionFunctorComponent.lean | FixedRestrictionFunctorEdge.component_at; L25 theorem FixedRestrictionFunctorEdge.component_at {A B Z : SSet.{u}} [Quasicategory Z] {i : A ⟶ B} {f g : B ⟶ Z} (E : FixedRestrictionFunctorEdge i f g) (a : A _⦋0⦌) : (simplici | Kerodon 1.4.0.1 | 0 |
| SerrePositivity/KST/SConstruction/ContractiblePathComparison.lean | contractibleKan_parallel_homMk; contractibleKan_three_edge_fac; L22 lemma contractibleKan_parallel_homMk {P : SSet.{u}} (hP : IsContractibleKan P) {x y : P _⦋0⦌} (e f : P.Edge x y) : SSet.HomotopyCategory.homMk e = SSet.HomotopyCategory.homMk f | Kerodon 1.4.0.1 | 0 |

### ∞圏の同値・可逆辺・頂点同型

31本・2,177行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/Equivalence/`。同値／同型の構成の補助法則。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/EquivalenceArrowFamily.lean | pathLift; pathLift_inclusion; L26 def pathLift : A ⟶ equivalencePath X / L28 lemma pathLift_inclusion : pathLift a ha ≫ equivalencePathι X = a; 入力: variable {A X : SSet.{u}} [Quasicategory X] (a : A ⟶ (ihom (Δ[ | Kerodon 4.5.1.1 | 2 |
| SerrePositivity/KST/SConstruction/FunctorIsoEquivalenceReflection.lean | functorIsoReflectPreEquivalence; functorIsoReflectPostEquivalence; L17 def functorIsoReflectPreEquivalence {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) {f g : Y ⟶ Z} (h : FunctorIso (e.hom ≫ f) (e.hom ≫ g)) : Fu | Kerodon 4.5.1.1 | 2 |
| SerrePositivity/KST/Fibration/CofiberFamilyComparison.lean | cofiberFamilyComparison; cofiberFamilyCornerIso; L21 def cofiberFamilyComparison {X : SSet.{u}} [Quasicategory X] (t s : ZeroTriangle X) (ht : IsCofiberSequence t) (hs : IsCofiberSequence s) (h : squareBottomEdge ≫ t.square = squ | Kerodon 4.5.1.1 | 0 |

### 極限・余極限・錐・四角形

30本・2,493行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/`。一般のquasicategoryの普遍性。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/SquareFramePathExtension.lean | comparison; target_isPullback; L30 def comparison : FunctorIso Q w.target / L34 lemma target_isPullback (hQ : IsPullbackSquare Q) : IsPullbackSquare w.target; 入力: variable {X : SSet.{u}} [Quasicategory X] (f : S | Kerodon 7.1.1.1 | 1 |
| SerrePositivity/KST/SConstruction/ColimitBaseTransport.lean | exists_initialCoconeVertex_over_invertible_edge; HasColimit.of_functorIso; L23 lemma exists_initialCoconeVertex_over_invertible_edge (K X : SSet.{u}) [Quasicategory X] (v : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌) (hv : InitialBoundaryLifting (coco | Kerodon 7.1.1.1 | 0 |
| SerrePositivity/KST/Spectra/DiagramLimitExistenceTransport.lean | restrict; vertex_restrict; L24 def restrict {K L X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (f : L ⟶ K) : JoinCone (f ≫ p) / L32 lemma vertex_restrict {K L X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (f : L ⟶ | HTT 4.2.4.1; Kerodon 7.1.1.1 | 0 |

### join・slice・coslice

16本・1,434行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/`。実単体を保持する錐・sliceの一般的計算。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/CoconeFamilyCoreCriterion.lean | coconeFamily_invertsAllEdges_of_prefix_apex; L26 lemma coconeFamily_invertsAllEdges_of_prefix_apex {P L X : SSet.{u}} [Quasicategory X] (F : P ⟶ (ihom (join L (Δ[0] : SSet.{u}))).obj X) (z : X _⦋0⦌) (hp : InvertsEdges (F ≫ (p | Kerodon 4.3.1.1 | 2 |
| SerrePositivity/KST/Fibration/FixedFractionCosliceTransport.lean | fixedFractionCosliceEvaluation_transport; fixedFractionCosliceEvaluation_transport_vertex; L18 theorem fixedFractionCosliceEvaluation_transport {y z : X _⦋0⦌} (e : y = z) : eqToHom (congrArg (fun a => fixedMarkedSpans X W x a) e) ≫ fixedFractionCosliceEvaluation F W hF x | Kerodon 4.3.1.1 | 1 |
| SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/ExtensionComparison.lean | ofFunctorObjIso; ofFunctor_inverseMap; L20 abbrev ofFunctorObjIso (x : Adjoin r j) : (ofFunctor r j F).object x ≅ F.obj (adjoinObj r j x) / L24 lemma ofFunctor_inverseMap {x y : Adjoin r j} (f : x ⟶ y) (hf : inverse f.h | Kerodon 4.3.1.1 | 0 |

### ∞圏の随伴・単位余単位・opposite

14本・674行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/`。関手∞圏の可逆辺を用いる随伴の一般部分。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/AdjointLocalizationFactor.lean | factorIso; factorIso_hom_arrow; L25 def factorIso : FunctorIso T ((F ≫ G) ≫ T) / L42 lemma factorIso_hom_arrow : Arrow.mk (factorIso a T hT).hom = Arrow.mk ((hoFunctor.map ((ihom X).map T)).toFunctor.map a.unitHo | Kerodon 6.2.1.1 | 0 |

### Ex∞の構成と一般法則

12本・637行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheExInfinityFunctor/`。特定のK／dg／BF入力に固定しないEx∞。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/Comparison/ExInfinityBar.lean | exInfinitySimplicialMonoid_bar_localized_isIso; L31 instance exInfinitySimplicialMonoid_bar_localized_isIso (M : SimplicialObject MonCat.{u}) : IsIso (AnodyneHomotopy.anodyneQ.map (monoidBarMap (exInfinitySimplicialMonoidUnit.ap | Kerodon 3.3.6.1 | 0 |
| SerrePositivity/KST/Fibration/KanClosedEvaluation.lean | pointedKanForgetEnriched; exInfinityClosedKanEnrichedFunctor; L19 def pointedKanForgetEnriched : EnrichedFunctor SSet.{u} PointedKanObject.{u} KanObject.{u} / L27 def exInfinityClosedKanEnrichedFunctor : EnrichedFunctor SSet.{u} SSetInternalO | Kerodon 3.3.6.1 | 0 |
| SerrePositivity/KST/SConstruction/ExInfinityPointedEnrichedFunctor.lean | exInfinityPointedEnrichedFunctor; exInfinityPointedKanEnrichedFunctor; L19 def exInfinityPointedEnrichedFunctor : EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} / L24 def exInfinityPointedKanEnrichedFunctor : EnrichedFunctor SSet | Kerodon 3.3.6.1 | 0 |

### 左右のfibrationの一般的な持ち上げ

10本・598行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/`。任意のquasicategory上のleft/right fibrationとslice。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/Fibration/RelativeComparisonRightSection.lean | exists_relativeRightSection_of_compositeIso; L15 theorem exists_relativeRightSection_of_compositeIso {A E F B : SSet.{u}} [Quasicategory B] (pA : A ⟶ B) (pE : E ⟶ B) (pF : F ⟶ B) [LeftFibration pA] [LeftFibration pF] (u : A ⟶ | Kerodon 4.2.1.1 | 1 |
| SerrePositivity/KST/LocalizingInvariants/RightFibrationConeTransport.lean | sliceOverPostcomp_rightFibration; rightFibration_isContractibleKan_of_terminal; L25 lemma sliceOverPostcomp_rightFibration {K E B : SSet.{u}} (a : K ⟶ E) (r : E ⟶ B) [RightFibration r] : RightFibration (sliceOverPostcomp a r) / L37 lemma rightFibration_isContr | Kerodon 4.2.1.1 | 1 |
| SerrePositivity/KST/Spectra/D3ConeForwardTransport.lean | d3_rightFibration_liftEdge_source; L23 lemma d3_rightFibration_liftEdge_source {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [RightFibration p] (x : E _⦋0⦌) {y : B _⦋0⦌} (e : Truncated.Edge (X := (truncation 2).obj | Kerodon 4.2.1.1 | 0 |

### Cartesian・coCartesian fibration

8本・608行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/`。指定された底の図式・辺を保持する一般補題。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/Fibration/CocartesianKanDiagram.lean | cocartesianKanDiagram; cocartesianKanCoherentDiagram; L18 def cocartesianKanDiagram {I : Type u} [Category.{u} I] {E : SSet.{u}} (p : E ⟶ nerve I) : I ⥤ KanObject.{u} / L23 def cocartesianKanCoherentDiagram {I : Type u} [Category.{u}  | Kerodon 5.1.4.1 | 1 |
| SerrePositivity/KST/LocalizingInvariants/ArrowPullbackCartesianEdge.lean | arrowTarget_isCartesianEdge_of_pullback; L24 lemma arrowTarget_isCartesianEdge_of_pullback {X : SSet.{u}} [Quasicategory X] (e : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋1⦌) (he : IsPullbackSquare (uncurry (SSet.yonedaEquiv.sym | Kerodon 5.1.4.1 | 0 |

### 写像空間・pinched Hom

6本・471行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/`。一般の∞圏のHomと端点の比較。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/FixedFractionPinchedEvaluation.lean | fixedFractionPinchedEvaluation; fixedFractionPinchedComparisonHomotopy; L25 def fixedFractionPinchedEvaluation : fixedMarkedSpans X W x y ⟶ pinchedHom (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) / L30 def fixedFractionPinchedComparisonHomot | Kerodon 4.6.1.1 | 1 |

### 共終性・Quillen A

1本・123行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/`。一般の単体的圏／∞圏に対するcofinality判定の補助。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/LocalizingInvariants/FiniteQuotientConeRecoveryCofinality.lean | exists_corePullback_finiteCone_of_quotientConeRecovery; corePreimageProjection_isLeftCofinal_of_quotientConeRecovery; L23 lemma exists_corePullback_finiteCone_of_quotientConeRecovery {X Z : SSet.{u}} [Quasicategory X] [Quasicategory Z] (q : X ⟶ Z) (h : ∀ (K : SSet.{u}) [K.Finite] (p : K ⟶ X) (t :  | Kerodon 7.2.3.1 | 0 |

### Kan複体のWhitehead型判定

1本・48行。移す先案：`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/HomotopyGroups/`。Kanのπ群同型による比較。

| 代表ファイル | 型の要点・宣言 | 対応表番号 | 外部import数 |
|---|---|---|---|
| SerrePositivity/KST/ProExcision/WhiteheadBlockFactorization.lean | blockUpperUnit; blockLowerUnit; L20 def blockUpperUnit (A : Matrix ι ι R) : (Matrix (ι ⊕ ι) (ι ⊕ ι) R)ˣ / L29 def blockLowerUnit (A : Matrix ι ι R) : (Matrix (ι ⊕ ι) (ι ⊕ ι) R)ˣ; 入力: variable {R : Type u} [Ring R | Kerodon 3.2.8.1 | 0 |

## Kerodonの章ごとの対応

一般の∞圏論に分類した行の `coverage_items` にあるKerodon番号について、章ごとに異なるファイルを集計した。同一ファイルが複数章の番号を持つ場合は各章に一回ずつ現れるため、この表の合計は一般分類の総数と必ずしも一致しない。HA・HTTだけに番号を付けた行はここには含まない。実装状態は集計していない。

| 章 | 主題 | 対応ファイル数 | 行数 | 異なる対応番号数 |
|---|---|---|---|---|
| 1 | The Language of ∞-Categories | 167 | 13530 | 6 |
| 2 | Examples of ∞-Categories | 285 | 22523 | 3 |
| 3 | Kan Complexes | 412 | 33749 | 33 |
| 4 | The Homotopy Theory of ∞-Categories | 73 | 5394 | 15 |
| 5 | Fibrations of ∞-Categories | 72 | 4828 | 5 |
| 6 | Adjoint Functors | 49 | 2716 | 2 |
| 7 | Limits and Colimits | 84 | 6307 | 11 |

<details>
<summary>章ごとの対応番号</summary>

- Chapter 1: 1.2.1.19, 1.3.1.1, 1.4.0.1, 1.5.3.1, 1.5.5.5, 1.5.6.7
- Chapter 2: 2.4.5.1, 2.4.6.10, 2.4.6.13
- Chapter 3: 3.1.2.1, 3.1.3.14, 3.1.5.1, 3.1.5.9, 3.1.5.10, 3.1.8.1, 3.1.8.2, 3.1.8.6, 3.1.8.7, 3.1.8.8, 3.2.1.1, 3.2.8.1, 3.3.0.1, 3.3.5.7, 3.3.6.1, 3.3.6.2, 3.3.6.10, 3.3.7.6, 3.3.7.7, 3.4.0.3, 3.4.0.7, 3.4.0.9, 3.4.1.1, 3.4.1.2, 3.4.1.5, 3.4.1.6, 3.4.1.9, 3.4.1.11, 3.4.1.13, 3.4.2.10, 3.4.2.16, 3.4.4.3, 3.4.4.4
- Chapter 4: 4.2.1.1, 4.3.1.1, 4.4.3.6, 4.4.3.14, 4.4.3.17, 4.4.3.18, 4.5.1.1, 4.5.1.5, 4.5.3.18, 4.5.3.19, 4.5.3.20, 4.5.3.27, 4.5.7.11, 4.6.1.1, 4.8.4.1
- Chapter 5: 5.1.4.1, 5.2.1.1, 5.3.1.9, 5.5.2.8, 5.6.2.1
- Chapter 6: 6.2.1.1, 6.3.1.9
- Chapter 7: 7.1.1.1, 7.1.5.12, 7.1.5.13, 7.1.5.22, 7.2.3.1, 7.5.1.1, 7.5.4.1, 7.5.4.6, 7.5.4.13, 7.7.0.4, 7.7.6.1

</details>

## OE-W1と同じ節に集まる案

OE-W1は基準mainには未取り込み。兄弟枝 `refactor/organize-einfinity` の **`d216f410b`** を読み取り、`formalization-plans/stage-ii/organize-einfinity-w1/module-map.json` の移動先と照合した（取得したJSONのSHA256 `07cbab5697f108135f0baf171c9a817df35adaae76ab05e76af471e649658518`）。他枝へ書き込んでいない。段2の分類表は主用途による紙の表で移動先の列がないため、具体的な重なりは段1のmodule-mapから取った。

| 同じ配置先の節 | 今回の一般分類の本数 | OE-W1の移動本数 | 今回の例 | OE-W1の例 |
|---|---|---|---|---|
| SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/ | 8 | 1 | SerrePositivity/KST/Fibration/CocartesianKanDiagram.lean | SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexFirstVertexZero → SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexFirstVertexZero |
| SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/ | 62 | 11 | SerrePositivity/KST/Fibration/BaseChangeImageSectionValue.lean | SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFiberEvaluationEdge → SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFiberEvaluationEdge |
| SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheExInfinityFunctor/ | 12 | 1 | SerrePositivity/KST/Comparison/ExInfinityBar.lean | SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityUnitLeftAnodyne → SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityUnitLeftAnodyne |
| SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/ | 111 | 2 | SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanEndFibration.lean | SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection → SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection |
| SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/ | 1 | 2 | SerrePositivity/KST/LocalizingInvariants/FiniteQuotientConeRecoveryCofinality.lean | SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationComparison → SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationComparison |
| SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/ | 43 | 13 | SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanAugmentationHom.lean | SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanUniverseSections → SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanUniverseSections |
| SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/ | 10 | 1 | SerrePositivity/KST/Fibration/LeftFibrationInvertedBaseChange.lean | SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.AnodyneKanTarget → SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.AnodyneKanTarget |
| SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/ | 6 | 1 | SerrePositivity/KST/LocalizingInvariants/CompositionTriangleRelativePrism.lean | SerrePositivity.EInfinity.FrameHom.AnodyneFamilyHomotopy → SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.AnodyneFamilyHomotopy |
| SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/ | 16 | 1 | SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/ExtensionComparison.lean | SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTargetNaturality → SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTargetNaturality |
| SerrePositivity/InfinityCategories/Kerodon/TheLanguageOfInfinityCategories/InfinityCategories/ | 33 | 1 | SerrePositivity/KST/Fibration/FixedRestrictionFunctorComponent.lean | SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.NerveHomUniverseIso → SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.NerveHomUniverseIso |

上の一致は同じ節・ディレクトリに集める案であり、宣言が重複することを証明したものではない。特にcoherent図式・Kanの充填・局所化の補助では、片方が他方をimportすることや、同じ入力を異なる表現で包んでいることがある。

OE-W1のFrameHomは `HomotopicalAlgebra/HomotopyFunctionComplex/FrameHom/`、HomotopyWeightは `HomotopicalAlgebra/Diagram/HomotopyWeight/` へ移す計画である。今回のHomotopicalAlgebraの一般のfunction complex・Reedy・diagramの分類と近い。こちらはKerodonの同じ節という一致とは別に、模型圏の入力層を統合する際の接点となる。OE-W1のSimplicialLocalizationは `InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/` に置かれるため、今回の一般の辺局所化（Kerodon6.3）とは比較を分けて扱う。

## 未定の理由と残る判断

| 未定の理由 | 本数 | 行数 | 代表ファイル |
|---|---|---|---|
| 再公開・互換入口で主型がこのファイルにない | 42 | 11423 | SerrePositivity/HomotopicalAlgebra/Foundations.lean; SerrePositivity/HomotopicalAlgebra/GeneralTools.lean |
| 通常の圏論・組合せ論等：原典項目または固有性が未同定 | 417 | 28480 | SerrePositivity/KST/Comparison/CoefficientMatrixStabilization.lean; SerrePositivity/KST/Comparison/FiniteCoverInduction.lean |
| 通常の代数・複体・幾何：五分類への割当が未確定 | 764 | 65514 | SerrePositivity/KST/Comparison/ConnectiveTruncation.lean; SerrePositivity/KST/Comparison/FiberCoefficientAdjunction.lean |
| 任意の∞圏の補題とBF専用比較の混在 | 20 | 2188 | SerrePositivity/KST/Spectra/D3CommonStageCanonicalCoherence.lean; SerrePositivity/KST/Spectra/D3CommonStageLoop.lean |

未定を一般の∞圏論やK固有の数へ算入してはいない。たとえばsheafification・acyclic複体の短完全列・可換環のチャート座標・ブロック行列の純代数的補題は、KSTから利用されるだけではK固有にならず、InfinityCategoriesの該当項目もこの型だけでは指定できない。HomologicalAlgebra・DifferentialGraded・AlgebraicGeometry・通常のCategoryTheoryへの配置も含めて判断すべきものとして理由を残す。

## 検収と停止

指定3ディレクトリの全Leanファイル集合とCSVのpath集合の完全一致、10,071個の一意なpath/module、行数の一致、5分類、一般分類の移動先・対応番号の欠落0、番号の既存対応表への存在、型の根拠位置、外部import数、集計の再計算を検査した。対応表の状態は複製せず、同じ節の案と原典の定理全体の同定を区別した。出力は指定どおりこの `files.csv` と `summary.md` の2ファイルだけ。Lean変更・ビルド・移動・大きい監査は行わず、この紙をコミットして停止する。
