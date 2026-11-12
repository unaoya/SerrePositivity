# KL-W1 段 0〜段 3・取り込み前検証報告

2026-11-12 更新。**停止点 3**。main `f654cdc11` を取り込み、`1304c688ff9e4b2486f547310d07bfc25a2780d7` で root・全 103 監査・verify が成功した。保存比較 v3b 14,606 本の未説明差分 0、Kerodon 属性 672 組一致、5 段の層の違反 0。最新の結果と §9 の配置判断は末尾の「停止点 3」に記載した。

以下の初期調査と経過記録は、その時点の件数・停止点を表す。§15 により共有鍵を使わず、取り込み前の重い検査まで作業枝で完了した。個別の逆向き import の例外案は、停止点 3 での調整役の確認対象。

## 初期記録（停止点 1、2026-11-07）

2026-11-07。調査対象は開始時の main `c56adeef7`。配置・依存・規模の集計はこのスナップショットで固定し、途中で追加された §6 と既存の型確認結果は main `33ce6cfca` から反映した。ここが停止点 1。段 2 の前に Kerodon 対応表の確認が全章 main に入った時点で、暫定の割り当てを一度見直す。

## 停止点 0 — 項目 Tag

[item-tags.csv](../../research/kerodon-coverage/item-tags.csv) に **6,613 件**（`number,kind,tag`）。Ch 1–10 の小節 418・節 57・章 10 の各ページから、項目本体の `environment-identifier` のリンクを取得した。リンク先の Tag、番号の `data-tag`、項目の `article id` が一致することを確認した。章・節のページに直接載る小節番号 `0` の項目は 197 件。番号・Tag の重複は各 0 件。元の `items.csv` 3,553 件をすべて含み、種別の差は 0 件。残り 3,060 件には例・演習・注記等も含む。各章 5 件ずつ固定 seed `20261107` で抜き、独立に取得した個別 Tag ページで 50/50 件が番号・種別・Tag と一致した。抜き取り結果は [照合表](kerodon-layout-tag-sample.csv)。[Kerodon](https://kerodon.net/)、[見出しの例](https://kerodon.net/tag/04ZB)、[個別ページの例](https://kerodon.net/tag/04ZC)。

| 章 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 項目 | 370 | 532 | 623 | 1,176 | 652 | 273 | 872 | 807 | 1,038 | 270 |

## (a) 割り当て

[割り当て表](kerodon-layout-assignment.csv) は既存の `InfinityCategories/` の Lean 14,659 本、文書 10 本と、外部の Lean 候補 297 本を含む。各行に旧パス、候補の新パス、節、節 Tag、根拠、配置案の扱いを記録した。Kerodon 内の Lean は章・節までとし、小節はファイル名や module docstring に出す。数字付きの章・節名は置かない。同一の候補パスが生じる 28 組 68 本は旧パスの区分をファイル名に付けて区別した。宣言名の衝突は、名前空間の改名表で別途検査する。

- Ch 1 の宣言対応は `review/ch1.csv` の `status_new` と `declarations_new` を採用した。Ch 2 以降は `items.csv` を用いた。選択した節に確認済みの宣言対応がある 25 行は `basis=review`。Ch 1 でも根拠が引用や主題だけの行と、全未確認章の行は `basis=items`。
- `own`・`both` の項目を優先し、次に `partial`、ソースの docstring にある Kerodon の項目・小節・節参照、既存のファイル群の主題を使った。節が競合したときは対応項目数と引用の支持で主節を選んだ。引用は module docstring を 3、宣言 docstring を 1 として集計した。引用集計 9,711 件は全体の傾向の照合に使い、割り当ての行には実際のソースから拾った番号を記録した。`none` の比較用の記載、Mathlib のみの宣言、節番号 `0` の章序文項目は節への割り当て根拠から外した。既存の対応表が示す SerrePositivity の宣言ソースの欠損は 0 件。
- 主節以外の宣言名は `other_declarations` に残した。既存の ∞ 圏で `split-proposed` の 23 本は、複数の節に異なる `own`・`both` の宣言が載る。切り出す宣言と共通の前提を選び、段 3 で `split_module.py` と保存比較 v3b を使う。残りの複数節ファイルは `main-section` を基本とし、引用だけが複数ある場合は主節の module docstring に関連小節を併記する。
- 既存の ∞ 圏では、パスから主題を推定した `topic-confirm` が 5,340 本。既存の系列を根拠に出どころ別へ振った `origin-confirm` が 7,066 本。例えば `F2/Ind/` は §9.3、`Derived/CoherentBar/` の HA 由来部分は `HA/DerivedCategoryModels/CoherentBar/`、G8 の集合値重みは `Project/SetWeightedTensors/`。この粒度では補助の所属を推定した行が多く、章確認後はまず Ch 2 以降の宣言根拠と、`topic-confirm`・`origin-confirm` で利用先と主題が異なる系列を見直す。
- `entry-or-check` 53 本は入口・監査コマンド等の候補。現行の公開入口とその import 範囲、独立している straightening 入口、旧 alias 登録用の meta import を区別して整理する。文書はルート README を索引にし、残りは `Project/Documentation/` に寄せる暫定案とした。

### §6 — モデル圏の仮定

割り当て表の `model_category` に宣言名ごとの印を置き、[宣言別の型・ソース根拠](kerodon-layout-model-category.csv) に元の位置、仮定、根拠の種類を記録した。

| 印 | 件数 | 段 2 の扱い |
| --- | ---: | --- |
| `exclude-sset` | 2 | `[ModelCategory SSet]` を要求する宣言。属性の対象外 |
| `verify-instance` | 16 | 項目で使う具体圏の instance が本体に実在することを、Kerodon 確認で確かめてから対象にする |
| `verify-section-scope` | 848 | モデル圏の section variable がスコープ内にある宣言。型に取り込まれるかを確認するまで保留 |

段 1′ で既に型を確認した 14 宣言（`SSet` 1、一般圏 13）を採用した。残りはコメントを除いた宣言ヘッダの明示 binder または有効な `variable` を拾った静的候補。とくに section variable は実際の型に入らない場合がある。空欄はこの走査で該当が見つからなかった行で、型検査の結果を表さない。別名や間接的な型クラス引数、`ModelCategory` 以外の満たせない仮定は、段 2 の対象ごとの型確認で扱う。`exclude-sset` の対象例は `SimplicialModel.simplicial_anodyne_eq_trivialCofibrations` と `SimplicialModel.UniverseLift.anodyneQ_map_isIso_of_weakEquivalence`。

## (b) ディレクトリの木

割り当てのある章・節と出どころ別の区分。括弧の本数は外部の保留候補を含む。ファイル名と `HA/`・`Project/` の下位区分は割り当て表に記載した。

```text
InfinityCategories/
├── Kerodon/
│   ├── TheLanguageOfInfinityCategories/
│   │   ├── SimplicialSets/  (1.1, 0004, 18 本)
│   │   ├── FromTopologicalSpacesToSimplicialSets/  (1.2, 0508, 4 本)
│   │   ├── FromCategoriesToSimplicialSets/  (1.3, 002L, 3 本)
│   │   ├── InfinityCategories/  (1.4, 0039, 6 本)
│   │   └── FunctorsOfInfinityCategories/  (1.5, 0055, 11 本)
│   ├── ExamplesOfInfinityCategories/
│   │   ├── SimplicialCategories/  (2.4, 00JN, 174 本)
│   │   └── DifferentialGradedCategories/  (2.5, 00ND, 391 本)
│   ├── KanComplexes/
│   │   ├── TheHomotopyTheoryOfKanComplexes/  (3.1, 00SZ, 92 本)
│   │   ├── HomotopyGroups/  (3.2, 00V2, 120 本)
│   │   ├── TheExInfinityFunctor/  (3.3, 00XF, 66 本)
│   │   ├── HomotopyPullbackAndHomotopyPushoutSquares/  (3.4, 0106, 24 本)
│   │   ├── TruncationsAndPostnikovTowers/  (3.5, 0513, 1 本)
│   │   └── ComparisonWithTopologicalSpaces/  (3.6, 012Y, 2 本)
│   ├── TheHomotopyTheoryOfInfinityCategories/
│   │   ├── InnerFibrations/  (4.1, 01B8, 6 本)
│   │   ├── LeftAndRightFibrations/  (4.2, 014H, 34 本)
│   │   ├── TheSliceAndJoinConstructions/  (4.3, 015M, 190 本)
│   │   ├── IsomorphismsAndIsofibrations/  (4.4, 01EM, 39 本)
│   │   ├── Equivalence/  (4.5, 01DE, 88 本)
│   │   ├── MorphismSpaces/  (4.6, 01J3, 419 本)
│   │   ├── TruncatedObjectsAndHigherHomotopyCategories/  (4.7, 05EA, 21 本)
│   │   ├── FullFaithfulAndEssentiallySurjectiveFunctors/  (4.8, 0578, 28 本)
│   │   └── SizeConditionsOnInfinityCategories/  (4.9, 03PP, 32 本)
│   ├── FibrationsOfInfinityCategories/
│   │   ├── CartesianFibrations/  (5.1, 01T1, 310 本)
│   │   ├── CovariantTransport/  (5.2, 019A, 140 本)
│   │   ├── FibrationsOverOrdinaryCategories/  (5.3, 035A, 170 本)
│   │   ├── TheInfinityCategoryQC/  (5.5, 01YV, 264 本)
│   │   └── ClassificationOfCocartesianFibrations/  (5.6, 027M, 966 本)
│   ├── AdjointFunctors/
│   │   ├── AdjunctionsInTwoCategories/  (6.1, 02CA, 4 本)
│   │   ├── AdjointFunctorsBetweenInfinityCategories/  (6.2, 02EH, 95 本)
│   │   └── Localization/  (6.3, 01M4, 661 本)
│   ├── LimitsAndColimits/
│   │   ├── LimitsAndColimits/  (7.1, 02H1, 455 本)
│   │   ├── Cofinality/  (7.2, 02MZ, 62 本)
│   │   ├── KanExtensions/  (7.3, 02Y1, 241 本)
│   │   ├── LimitsAndColimitsOfSpaces/  (7.4, 02SX, 74 本)
│   │   ├── HomotopyLimitsAndColimits/  (7.5, 039Y, 123 本)
│   │   ├── ExamplesOfLimitsAndColimits/  (7.6, 03E8, 22 本)
│   │   └── UniversalityOfColimits/  (7.7, 05SB, 4 本)
│   ├── TheYonedaEmbedding/
│   │   ├── TwistedArrowsAndCospans/  (8.1, 03JB, 86 本)
│   │   ├── CouplingsOfInfinityCategories/  (8.2, 043P, 1 本)
│   │   ├── TheYonedaEmbedding/  (8.3, 03LZ, 179 本)
│   │   ├── Cocompletion/  (8.4, 03V7, 5 本)
│   │   └── RetractsAndIdempotents/  (8.5, 03Y9, 170 本)
│   ├── LargeInfinityCategories/
│   │   ├── FilteredInfinityCategories/  (9.1, 05WY, 58 本)
│   │   ├── FinitaryFunctorsAndCompactObjects/  (9.2, 0639, 108 本)
│   │   ├── IndCompletionsOfInfinityCategories/  (9.3, 06FR, 724 本)
│   │   ├── CompactGenerationAndAccessibility/  (9.4, 06GT, 127 本)
│   │   ├── PresentableInfinityCategories/  (9.5, 06NC, 983 本)
│   │   ├── FactorizationSystems/  (9.6, 04KF, 3 本)
│   │   └── TensorProductsOfInfinityCategories/  (9.7, 06ZD, 31 本)
│   └── ExactnessAndAnimation/
│       └── SimplicialObjectsOfInfinityCategories/  (10.1, 04QJ, 2 本)
├── HA/
│   ├── DerivedCategoryModels/  (616 本)
│   ├── ModelCategoryComparison/  (10 本)
│   ├── StableInfinityCategories/  (712 本)
│   └── StablePresentableInfinityCategories/  (5 本)
├── HTT/
│   ├── ModelCategoryAdjunctions/  (29 本)
│   └── PointedSimplicialSets/  (9 本)
└── Project/
    ├── DerivedCategories/  (3687 本)
    ├── Entrypoints/  (53 本)
    ├── FibrationAuxiliaries/  (268 本)
    ├── FilteredExchange/  (297 本)
    ├── HomotopyDiagramComparison/  (683 本)
    ├── KanComplexAuxiliaries/  (156 本)
    ├── LocalizationAndKanExtensionAuxiliaries/  (181 本)
    ├── ModelCategoryComparison/  (140 本)
    ├── PointedSpaces/  (26 本)
    ├── QuasicategoryAuxiliaries/  (105 本)
    ├── SetWeightedTensors/  (32 本)
    └── SimplicialCombinatorics/  (110 本)
```

## (c) 逆向きの import

`importer → imported` の向きで、両端に Kerodon の節があり、import 元の節が先に出る辺を [逆向き一覧](kerodon-layout-reverse-imports.csv) にすべて列挙した。**1,462 辺**（既存の ∞ 圏どうし 1,431、両端に `own`・`both` の宣言根拠があるもの 60）。章・節番号は比較にのみ使った。出どころ別の区分をまたぐ辺と外部への辺は、(d) と (d′) の境界として扱う。

| 節の組 | 辺数 | 配置・分割案 |
| --- | ---: | --- |
| §5.1 → §5.6 | 79 | `RightFibrationOppositeComparison` は分類の双対化を行うので §5.6 に寄せ、§5.1 には cartesian／cocartesian 辺と輸送の核を置く。 |
| §4.3 → §4.6 | 49 | `JoinTensorPoint` と `FatJoinFunctor` はともに §4.6.2 を参照するので同節に置く案。 `CosliceRestrictionEquivalence` が使う join の同値保存そのものは §4.6.2 の結果として扱う。 |
| §9.2 → §9.5 | 37 | `CompactFunctorRestriction` から `kappaCompactRestriction` とその制限の補題を §9.2 に寄せ、presentable な引き戻しへの適用を §9.5 に置く。 |
| §9.4 → §9.5 | 35 | `AccessibleEquivalence` が使う `GeneratorEquivalence` の生成族の輸送を §9.4 に置き、presentability の帰結を §9.5 に残せるかを確認する。 |
| §2.4 → §4.6 | 33 | `CompositionDiagonal` と `CompositionCorrespondence` の Hom・合成の比較を §4.6.7–8 にまとめ、coherent nerve の構成は §2.4 に置く。 |
| §5.5 → §7.1 | 33 | `ConeHomotopyDiagonalEdge` などの錐を使う応用と Cat∞ の定義を分ける。Cat∞ 固有の極限比較が `Core/Limit` を使う辺は §7.1 の定義への個別辺として記録する。 |
| §9.5 → §9.7 | 32 | `SiftedInfinity` と PΣ の積・余極限の交換を §9.7 にまとめる。`FiniteCoherentProductNativeCone` は PΣ 用の比較として再配置候補。 |
| §2.4 → §5.6 | 30 | `CollageRepresentationRecovery` の left fibration による表現回収を §5.6 側に置く案。enriched/coherent nerve 本体と分離する。 |
| §4.3 → §7.1 | 27 | `SliceOpposite` が使う `ConeDiagramReverse` の join と op の Hom 同値を §4.3 に切り出し、普遍錐の帰結は §7.1 に残す。 |
| §7.1 → §8.3 | 26 | `ConstantDiagramSectionTransport` が使う定値図式の輸送を §5.2 の共通部品として切り出し、presheaf density の適用は §8.3 に置く。 |
| §5.1 → §5.2 | 25 | `LeftFibrationFiberComparison` の相対 join 円柱の同型を §4.3 か §4.2 の前提として切り出し、輸送の比較を §5.2 に置く案。 |

各辺の `decision` は §0 の配置を優先した検討の入口で、`proposal` に移す側または分割する側を記した。225 辺に分割、452 辺に主題による暫定配置の見直しを提案した。残る 785 辺は、import 行だけでは必要な宣言を絞れない。まず使われる宣言と前提を調べ、共通部品として取り出せる場合は分割する。節固有の結果自体を使う辺は配置を保ち、理由付きで個別に許す。例えば §9.7.2 の `IsSiftedInfinity` が命題の型に現れる §9.5 の補題は、import を絞っても依存自体が残る。`SiftedInfinity.lean` の配置は §9.7 に保つ。

## (d) 外から移す候補と閉包

[候補別集計](kerodon-layout-external-candidates.csv) に、直接の外部 import・推移的閉包の本数・下流の本数・K 理論側へ達する経路を載せた。[外部閉包の一覧](kerodon-layout-external-closure.csv) は、到達する外部ファイルごとに、到達元候補の全リスト `reachable_from`、代表の最短 import 経路、移動・分割・境界確認の扱いを示す。既存の ∞ 圏配下の依存は割り当て表に全件あり、候補別集計の `infinity_closure` に数えた。

- 根拠のある外部ファイルは 187 本。さらに AW・shuffle、局所化、Ex∞ に属する依存 110 本を閉包から拾って割り当てた。全候補を根にした外部の和集合は根を含め 1,576 本、うち割り当てのない境界レビューが 1,279 本。表の候補は、追加移動により旧層の禁止辺が増える場合も調査対象とした。
- `hold-K-theory` は S 構成等の実装に達した 7 本。`hold-large-closure` は 21 本。後者の目印は外部を根込みで 100 本超、または Barratt–Eccles の operad 実装を引く場合。100 本は検討用の閾値。閉包の件数はファイル単位で、分割後の必要宣言の閉包は段 3 で確かめる。
- `move`・`main-section` は移動案、`split-or-confirm` は特殊化や引用だけからの候補などで、該当宣言と前提を確認してから切り出す。`shared-foundation-review` は保持する共通基盤の候補、`inspect-generic-slice` は同じ Kerodon 主題の宣言を探して取り出す境界。既存の KST・モデル圏の大きな入口を Kerodon 側の汎用部品が import する形は、部品の分割で解く。

| 外部の現ディレクトリ | 候補 | 既存 ∞ 依存 | 候補群を除く外部依存 | 全候補表の外 |
| --- | ---: | ---: | ---: | ---: |
| `CategoryTheory/Simplex` | 1 | 0 | 0 | 0 |
| `DifferentialGraded/Category` | 1 | 0 | 8 | 7 |
| `DifferentialGraded/Complexes` | 1 | 0 | 2 | 2 |
| `DifferentialGraded/Functor` | 1 | 0 | 12 | 10 |
| `EInfinity/AlexanderWhitney` | 16 | 0 | 7 | 6 |
| `EInfinity/BarrattEccles` | 1 | 0 | 79 | 78 |
| `EInfinity/FrameHom` | 2 | 1,035 | 4 | 2 |
| `EInfinity/Hammock` | 4 | 941 | 21 | 17 |
| `EInfinity/SimplicialLocalization` | 1 | 2,990 | 728 | 658 |
| `HomotopicalAlgebra/Diagram` | 5 | 2 | 49 | 49 |
| `HomotopicalAlgebra/Simplicial` | 11 | 9 | 37 | 37 |
| `HomotopicalAlgebra/Topological` | 1 | 0 | 0 | 0 |
| `KST/Comparison` | 85 | 176 | 292 | 263 |
| `KST/Descent` | 1 | 566 | 66 | 50 |
| `KST/Fibration` | 4 | 1,478 | 557 | 450 |
| `KST/LocalizingInvariants` | 14 | 630 | 1 | 0 |
| `KST/ProExcision` | 56 | 0 | 0 | 0 |
| `KST/SConstruction` | 16 | 498 | 321 | 296 |
| `KST/Spectra` | 75 | 720 | 225 | 219 |
| `Spectra/PointedSimplicialSet` | 1 | 0 | 1 | 1 |

### 一緒に動かせる候補

- **§2.5.7–8 の AW・shuffle・EZ。** `KST/ProExcision/NormalizedEZHomotopy` から辿る 55 本はすべて同じディレクトリ。起点と合わせた 56 本を §2.5 に配置する案。`AWChainMap`・`ShuffleChainMap` に加え、`IntegerTensorAdditivity`・`SimplexPairModel`・`LinearizedHomotopy` も含めた。現閉包から K 理論本体へは達しない。EInfinity の AW は 16 本の候補と 7 本の外部依存を持つ。`ChainDiagonal → … → NormalizedChains` の側から Barratt–Eccles の `Simplicial`・`Nondegenerate`・`Orbits`・`Normalized` に届く。鎖対角の一般部分だけが使う正規化鎖の API を切り出す案を先に調べ、Barratt–Eccles の演算に特化した結果は保留する。
- **§6.3.2 の局所化の存在。** `LocalizationResolution → InverseAttachmentUniversal → InverseAttachmentLifting → InverseAttachmentRestriction → InverseAttachment → WalkingEquivalenceUniversal`。起点の外部 9 本には、`WalkingEquivalenceRestriction`・`WalkingEquivalence`・`PinchedPrecomposeEquivalence` および `HomotopicalAlgebra/Simplicial/ModelCompatibility` が含まれる。前者の一般部品と `GeneralLocalization` は §6.3 へ一緒に移す案。後者は §1.2 の候補に残し、`[ModelCategory SSet]` を持つ宣言を型・利用先で分離できるかを確認する。既に ∞ 圏にある `Kan/InnerAnodyneReplacement` と `F1B/Localization/ParametricDiagramGluing` は割り当て表で追跡した。局所化の利用者である Verdier 商や Land–Tamme の構成は下流に置く。
- **§7.1.8 の関手圏の各点ごとの余極限。** S 構成の候補 16 本のうち、`RelativeInitialExtension` は外部依存 0 本、`FunctorPointwiseColimitExistence` は 4 本ですべて同じ候補群。 `FunctorPointwiseColimits`・`FunctorInitialBoundary`・`FunctorInitialVertices`・`RelativeInitialExtension` を一緒に取り出す案。§1.1.2 の `CategoryTheory/Simplex/GenRelEquivalence` も外部のプロジェクト内前提 0 本で、確認済みの §1.1 への移動候補。
- **§3.3 の Ex∞。** `ExInfinity` の外部 2 本、`ExInfinityKan` の外部 22 本を含め、`ExUnit`、二重細分の horn 充填、`HornChain*` と `NerveChainsLastVertex` まで §3.3 の候補とした。`ExInfinityHomotopyPullback` は外部 150 本に達するため、Ex∞ の構成・Kan 性と、モデル圏を使う引き戻し比較を分け、後者は閉包の見直しまで保留。

### 停止点 1 で判断が必要な境界

- **KST の S 構成・Fibration。** `AnodyneExtensionChoices → GappedPointwiseColimit`、`STrivialFibration → SOneExact` に実装への直接辺がある。`CoreFactorization`（§1.5 の確認済み宣言あり）も `WeakStringsStability` 以下で `RelativeAdditivity`・`CoreAdditivity` を経て `GappedEquivalenceDiagramSwap` に達する。一般の inner anodyne 延長や各点ごとの普遍性の宣言だけを切り出し、S 構成に関する帰結は KST 側に残す方針を確認したい。
- **KST/Spectra と Comparison。** `LoopHomotopyGroups` の外部 46 本には `Spectra/Pointed` 20 本と `Spectra/PointedSimplicialSet` 7 本が含まれる。§3.2 へは単体的なループ・球面の比較を優先し、`OmegaSpectrumZeroGroups` 等はスペクトル固有の型と汎用部分の境界を確認する。Comparison も Ex∞ の核、自由退化・実現、ホモトピー引き戻しの三群に切って進める案。後二群は Smith・モデル圏の比較まで届くため一括移動を保留する。
- **HomotopicalAlgebra・DG・EInfinity。** `HomotopicalAlgebra/Diagram/FilteredHomotopyColimit` から外部 43 本（Smith 27 本）に達する。§7.5・§9.1 の比較宣言とモデル圏の生成基盤を分ける。`EInfinity/SimplicialLocalization/ModelBifibrantRightKanReduction` は外部 728 本（Hammock 268 本）に達するので保留。§7.3 の一般の Kan 拡張判定と、frame・局所化に依存する適用部分の切れ目を調べる。`DifferentialGraded/Category/Basic` 等は §2.5 の対応が明確で、DG の基盤としての利用も広い。移す場合は (e) の下流を一束に組み込む。

## (d′) 新しい層の案

パスは Kerodon の章・節と `HTT`・`HA`・`Project` に割り当て、依存の層はファイル単位にする。仮のパスで節・出どころ別の区分に辺を集約すると、65 区分を含む強連結成分ができる。個々のファイルの import グラフでは循環 0。例えば §4.3 の `CosliceRestrictionEquivalence` は §4.6 の `JoinEquivalenceFunctor` を使い、§4.6 の `CosliceCoconeFamilyEquivalence` は §4.3 の `Slice` を使うため、節全体に一つの rank を割り当てると両方を表せない。

| 層名 | 順序 | 許す import |
| --- | ---: | --- |
| `SharedFoundation` | 0 | Mathlib 等と、合意した共有基盤内。汎用の圏・単体・鎖複体の低水準ファイルを明示して登録する |
| `Portable` | 1 | 0 と同層。Kerodon 各節および HTT・HA・Project の自立する部分。残留する KST 本体・スペクトル・モデル圏実装に直接・推移的に届く辺を検査する |
| `Comparison` | 2 | 0–2 と、登録した実装境界。モデル圏・DG・EInfinity・スペクトルの比較は、参照する実装ファイルと理由を指定する |
| `Entrypoints` | 3 | 0–3。集約 import、監査用入口、互換のための meta import。宣言モジュールからの逆流は入口を細分化して解く |
| `Consumers` | 4 | 0–4。KST・BS・CLMST・drafts 等から利用。移していない実装は既存の境界を保つ |

`layers.json` にはパスの区分、ファイルごとの層の指定、許可する実装境界、承認済みの個別逆向き辺と理由を分けて載せる案。移動後に `layer_check.py` が検査する順序は、実際の import DAG のトポロジカル順と上表の層の順序。節番号の逆向きは別欄で検出し、分割後に残った個別辺を記録する。モデル圏への到達を章まるごとの免除にせず、必要な比較を `Comparison` としてファイル単位で指定する。既存の直接禁止と推移的閉包の監査は、移動先で境界を引き直して引き継ぐ。

## (e) 規模と再ビルドの見込み

| 対象案 | 移動する Lean | 公開名つきソース宣言 | private・local | 無名 instance | 対象外の直接利用側 | 対象外の推移的利用側 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 既存の ∞ 圏のみ | 14,659 | 55,284 | 1,013 | 31 | 2,975 | 11,638 |
| ∞ 圏＋ProExcision・局所化系・単体圏の候補 | 14,730 | 55,704 | 1,013 | 36 | 2,997 | 11,677 |
| ∞ 圏＋DG 3 本 | 14,662 | 55,458 | 1,013 | 31 | 3,118 | 13,560 |
| ∞ 圏＋全外部候補（上振れの比較用） | 14,956 | 56,813 | 1,043 | 36 | 3,431 | 13,629 |

公開名つきソース宣言数を名前空間の改名数と、旧名 alias の一次見積もりに使った（∞ 圏のみで約 5.5 万ずつ）。既存 alias・外部に残す宣言・分割、構造体の projection、帰納型の recursor、`@[simps]` 等の生成宣言で増減する。段 I の F-2 では公開名つき 3,692 に対し alias 7,526 だった。同じ比率で粗く換算すると今回の alias は約 11 万で、名前空間衝突と生成宣言の確定は v3b のスナップショットと改名表を待つ。既存の旧名を二重登録しないよう、F-2 の改名表・alias と突き合わせる。

∞ 圏のみでも移動元と下流の和集合は 26,297 本。そのうち下流は KST 7,252 本、EInfinity 1,366 本、HomotopicalAlgebra 820 本、Archive 1,718 本、scripts 363 本を含む。既定の `SerrePositivity.lean` の静的閉包は 24,640 本（入口自身を含む）で、実際にコンパイルする対象は入口・監査とキャッシュに依存する。DG 3 本も移すと、全追跡ファイルで影響候補が 28,222 本に広がる。時間の実測は今回なし。調整規則 §2-5 の土台変更の目安（3〜8 時間）と同じ規模以上なので、段 2・3 を同じ束とし、全体の下流ビルド・verify は調整役の合図で一回行う。

## 検算と停止点 1

追跡済みの Lean 31,479 本の import を、コメントと文字列をマスクして解析した。修飾付き import と改行された import を含む。プロジェクト内の解決済み辺 108,408 本を使い、直接辺・推移閉包・逆閉包を集計した。解決できないプロジェクト内のモジュール名 13 種は Archive/WIP と research/kt-devissage の 11 本に限られ、解決済みのグラフから除外した。 数値は静的なソースグラフ上の見積もり。ビルド、保存比較、Lean の型・公理の再監査は未実施。

確認事項は、(b) の木と主題・出どころによる暫定配置、(c) で分割後にも残る節間の依存の扱い、(d) の KST 本体・大きな閉包・DG 基盤を含む候補の線引き。§6 の保留印と対応表の章確認を反映した上で段 2 へ進む。本コミットで停止点 1 に止まる。

## 停止点 1.5 — 段 3 の道具

作業枝に `a0e4c7d36` と `81e593fb9` を取り込んだ。指示書 §7 の決定を前提とする。段 2・3 の開始条件は、対応表のやり直しと独立した交差検査の完了。既存の割り当て表は停止点 1 の記録として保持した。

| 道具 | 入出力と検査 |
| --- | --- |
| [参照収集器](../../scripts/refactor/klw1_collect_refs.lean) と [名前空間移行](../../scripts/refactor/klw1_namespace.py) の `collect`・`rewrite` | Lean が実際に解決した定数名、所有モジュール、UTF-8 バイト位置、名前空間・`open` の構文を収集する。ソースが収集時とバイト単位で一致することを確認してから、相対名と完全修飾名を移行先へ差し替え、`namespace`・`end`・`open`・import を更新したプレビューを出す。同じ綴りのローカル変数、コメント、文字列は保持する |
| 同 `aliases` | main・drafts・作業中の枝を別々のマニフェストで収集し、移動後も ∞ 圏の外にある利用側から参照された旧名だけを採る。既存 alias への参照を別に記録し、重複生成を避ける。成果物は利用側のパスと位置を含む `aliases.json` と、F-2 の `deprecated_alias` を使った `Aliases.lean` |
| [新しい層検査](../../scripts/refactor/klw1_layer_check.py) | 追跡済み Lean の import DAG を検査する。ファイルごとに 5 層を指定し、循環、未解決 import、層の順序、Portable・SharedFoundation から実装に届く経路を検出する。実装境界と Kerodon の逆向き辺は理由付きの個別辺で管理する |
| [割り当て更新](../../scripts/refactor/klw1_review_assignment.py) | `items.csv`、章別 review、目次、停止点 1 の割り当てを読み、確認済みの宣言対応で `basis` と主節を更新する。配置・根拠の変更、撤回、新規の対応元、パス衝突を `changes.csv` に出す。モデル圏の印を引き継ぎ、外部移動は承認済みの 4 群の確定パスを別入力とする |

### 割り当ての見直しと段 3 での使い方

Python の道具はリポジトリ直下から `python3 scripts/refactor/<ファイル名>` で起動する。

1. やり直しと交差検査を確認したら `klw1_review_assignment.py --assignment ASSIGNMENT.csv --coverage research/kerodon-coverage --approved-external APPROVED.txt --accept-cross-review --output-dir REFRESH` を実行する。承認済みの外部パスは 1 行 1 本。K 理論本体に届く 7 本と閉包の大きい 21 本には移動可の印を付けない。正式モードは章別の全項目、仮定・結論の記載、kernel・none 探索の資料、Ch 4–10 の交差報告の存在を検査する。交差報告の判定と必要な再確認の完了は人が確かめる。途中で使う `--allow-incomplete` はプレビュー用。
2. 同じソースから作られた依存の Lean 成果物を使う。各 worktree の対象パスを JSON 配列で列挙し、`klw1_namespace.py collect --root ROOT --files FILES.json --output INDEX` で収集する。移動モジュールを推移的に import する外部ソースを対象にし、main・drafts と走っている枝をそれぞれ列挙する。範囲はマニフェスト単位で検算される。
3. 保存比較用の改名表と揃えた `plan.json` を作る。`rows` の各行は `module`・`old`・`new` を持ち、分割時は `new_module` も指定する。モジュール改名は `modules`、旧モジュールごとの名前空間は `namespaces`、旧 `open` の解決先ごとの方針は `opens` に記す。旧名前空間を残す場合は同名を指定する。既存の互換名は `existing_aliases` に置く。
4. `rewrite --root ROOT --files FILES.json --index INDEX --plan PLAN.json --output PREVIEW` で、移動先のディレクトリ構成にプレビューを出す。同じ構文に異なる定数解決がある、選択的 `open` のメンバーが別々に移る、名前空間を途中まで閉じる、引用やマクロで確かな編集位置が取れない場合は `review.json` に理由を出し、そのファイルのプレビューを保留する。集められるのは Lean が元のソース位置と関連付けた参照で、すべてのマクロや暗黙に生成される依存を網羅するわけではない。段 3 では残った箇所を解消し、再検査と保存比較 v3b を通す。
5. `aliases --scope LABEL ROOT FILES.json INDEX --plan PLAN.json --helper MODULE --since YYYY-MM-DD --output COMPAT` で互換名を生成する。`--scope` は worktree ごとに繰り返せる。選ばれた別の旧名を型の中で使う場合は、改名表の `type_dependencies` に型の依存を旧名で指定する。同時に選ばれた型の alias を先に生成する。通常の main 側利用者も同じ束で `rewrite` の対象とする。
6. 層検査は `klw1_layer_check.py --root ROOT --config FILE.json`。設定の `schema_version` は 1。`modules` は完全なモジュール名から層名への表で、∞ 圏の全モジュールを指定する。表外の追跡済みファイルは `Consumers`。`sections` は Kerodon の節パス接頭辞から `[章, 節]` への表。`external_prefixes` は Mathlib 等、`implementation_prefixes` は保持する KST・モデル圏等の実装境界。`implementation_edges` と `reverse_edges` の各行は `from`・`to`・`reason`。監査対象外の履歴は `exclude_prefixes` で明記する。最終的なファイル別設定は、承認済みの移動と分割を反映したグラフで作る。

### 検証

- Python の単体試験 10 件が通過。バイト位置とローカル変数の区別、曖昧な参照・未収集の完全修飾名・古い収集結果の拒否、外部利用だけの alias 選択、型の依存順、逆向きの節辺、実装への推移閉包、循環、章の更新と交差検査のゲートを確認した。
- ビルド鍵を通した小規模 Lean 統合試験 2 件が通過。相対名・完全修飾名・選択的／局所／scoped `open` と投影記法を含むプレビューを再検査した。既存の F-2 実装を読み込んで略記と定理の alias を生成し、外部の試験ファイルから両方を非推奨警告付きで使えることを確かめた。
- `81e593fb9` 時点の章表で途中プレビューを作り、3,001 項目から 14,966 行の表を再計算した。変更・要確認の記録は 809 件、うち既存行で行き先が変わったものは 32 件、新しい対応元は 5 件。正式モードは未提出の Ch 2 で停止し、正式出力は作らなかった。
- 実ファイルでもビルド鍵を通した。既存の `PinchedHom/Index` と `PinchedHom/Basic` を §4.6 の候補パスに一時出力し、改名候補 23 件を使って 2 本を順に再検査した。外部の `EInfinity/ComplexLimits/ConeTriangleIndex` から旧名の利用 3 件を抽出した。

## 停止点 1.6 — 章別レビュー後の割り当て差分

2026-11-10。作業枝に main `d0149fd4a` を取り込み、`a12e53be8` の章表と `c29b7be1b` の手順を使用した。`klw1_review_assignment.py --accept-cross-review` の正式モードで、全 10 章 3,553 項目と停止点 1 の割り当て 14,966 行を照合した。出力は [changes.csv](kerodon-layout-stop-1-6/changes.csv)（953 行、見出しを除く）。

| 集計 | 件数 |
| --- | ---: |
| 行き先が変わる既存行 | 22（∞ 圏内 21、外部候補 1） |
| 旧来の宣言根拠を撤回した行 | 172（∞ 圏内 160、外部候補 12） |
| 割り当て表にない新しい対応元 | 4 |
| 出力上の行き先の衝突 | 0 |
| 旧 partial 根拠のまま維持した行 | 437（∞ 圏内 380、外部候補 57） |

新たな配置の根拠は `own`・`both`・`mathlib` の確定行に載る SerrePositivity 側のファイルに限った。Mathlib のファイルは移動候補に含めない。`unsure` は要確認として記録した。旧 partial による割り当ては行き先も従来の根拠欄も維持し、更新表の `partial_placement_retained=yes` と差分表の理由欄で区別した。撤回は、旧宣言根拠があり、今回採用できる宣言根拠がどの節にも残らなかった行を数えた。暫定パスは維持した。

### 行き先が変わる 22 行

パスは `SerrePositivity/` を起点とする。旧・新の数字は Kerodon の節番号。`Project` は旧案の出どころ別配置。

| ソース | 旧 → 新 | 採用した項目 |
| --- | --- | --- |
| `EInfinity/FrameHom/AnodyneWeakDetection.lean` | 3.1 → 3.3 | 3.3.6.7、3.3.6.8、3.3.7.4 |
| `InfinityCategories/Core/Equivalence.lean` | 4.5 → 3.1 | 3.1.5.1、3.1.5.9 |
| `InfinityCategories/Core/EquivalencePathLifting.lean` | 4.5 → 4.4 | 4.4.5.10 |
| `InfinityCategories/Core/InitialBoundaryTransport.lean` | 7.1 → 4.2 | 4.2.4.11 |
| `InfinityCategories/Core/KanCharacterization.lean` | 4.4 → 1.3 | 1.3.5.2 |
| `InfinityCategories/Core/KanHomotopyEquivalence.lean` | 4.8 → 3.1 | 3.1.5.4 |
| `InfinityCategories/Core/OuterHornConverse.lean` | 4.4 → 1.4 | 1.4.6.10、1.4.6.12 |
| `InfinityCategories/F1/FilteredExchange/FilteredPointwiseWeakEquivalences.lean` | Project → 3.2 | 3.2.8.3 |
| `InfinityCategories/F1/Joins/CosliceTwistedHomComparison.lean` | 4.3 → 8.1 | 8.1.2.11 |
| `InfinityCategories/F1/Joins/CosliceTwistedHomEquivalence.lean` | 4.3 → 8.1 | 8.1.2.11 |
| `InfinityCategories/F1/Joins/RelativeJoinPrismCoverage.lean` | 5.2 → 3.1 | 3.1.2.12 |
| `InfinityCategories/F1/Joins/RelativeJoinPrismInitialPushout.lean` | 5.2 → 3.1 | 3.1.2.12 |
| `InfinityCategories/F1/TwistedArrow/EdgewiseEnrichedCategory.lean` | 8.1 → 8.6 | 8.6.7.1、8.6.7.2、8.6.7.5 |
| `InfinityCategories/F1B/Diagrams/OppositeInvolution.lean` | Project → 4.4 | 4.4.1.8 |
| `InfinityCategories/F1B/Diagrams/OppositeLifting.lean` | Project → 4.4 | 4.4.1.8 |
| `InfinityCategories/F1B/Fibrations/FiberwiseFunctor.lean` | 7.3 → 4.5 | 4.5.8.1 |
| `InfinityCategories/F1B/Fibrations/FiberwiseFunctorComponents.lean` | 5.1 → 4.5 | 4.5.8.1 |
| `InfinityCategories/F1B/Fibrations/FiberwiseHom.lean` | 7.3 → 4.5 | 4.5.8.1、4.5.8.5 |
| `InfinityCategories/F2/Presentable/AccessibleFunctor.lean` | 9.5 → 9.4 | 9.4.8.1 |
| `InfinityCategories/F2/Presentable/Definition.lean` | 7.4 → 7.6 | 7.6.6.1、7.6.6.4 |
| `InfinityCategories/F2/Presentable/Duality/RightUnitContractible.lean` | 9.5 → 4.7 | 4.7.3.14 |
| `InfinityCategories/F2/Presentable/EquivalenceColimits.lean` | 9.5 → 7.1 | 7.1.4.12 |

外部の `EInfinity/FrameHom/AnodyneWeakDetection.lean` は既存候補の対応節の差分で、§7 で承認された外部移動 4 群の対象外。新しい対応元 4 本は表に追加せず、`changes.csv` に記録した。外部移動の承認フラグは、この見直しでは付けていない。

Python の単体試験 11 件が通過し、差分表から 22 行すべての新しい根拠・437 行の維持・パスの一意性を検算した。段 1.6 はビルドを要さない。調整役による確認のため、ここで停止した。

## 段 2 — Kerodon の Tag

停止点 1.6 の承認 `1d39655f0` を取り込んで着手。全 10 章の `ok`・`fix` かつ `own`・`both` の行を `item-tags.csv` と突き合わせ、SerrePositivity の 610 宣言に 672 組の属性を付けた。カーネル環境で宣言名と所有モジュールが全件一致し、対象宣言の型に `ModelCategory` の仮定は 0 件。対応表で唯一該当する Archive の宣言も対象に含めた。部分対応の注記は今回の範囲外。

ビルド鍵を `--wait 1800` で取り、元の依存成果物を複製した一時領域で、変更した 367 本を再コンパイルした。全 367 本が通過した。`#kerodon_tags` を 16 の import 群で実行し、SerrePositivity の 672 組と照合した。欠落・余分はともに 0 件。Mathlib の既存 13 組は集計対象から除いた。出典と位置は [属性台帳](../../research/kerodon-coverage/kerodon-stage2-tags.csv)、照合した出力は [Lean の一覧](../../research/kerodon-coverage/kerodon-tags-lean.txt)。

## 段 3 — Alexander–Whitney・shuffle・Eilenberg–Zilber 群

承認済みの外部 4 群のうち、Alexander–Whitney・shuffle・Eilenberg–Zilber の import 閉包 56 本を `InfinityCategories/Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/` に移した。移動先と同じ名前空間に改名し、入口を含む利用側 81 本の import または参照を更新した。追跡対象の Lean ソースを調べ、旧 56 モジュールへの import は 0 件だった。旧名を ∞ 圏の外から使う参照の記録に基づき、88 名に `Project/Compatibility/KSTAlexanderWhitney.lean` で非推奨 alias を用意した。

ビルド鍵を `--wait 1800` で取得し、移動先 56 本と互換モジュールをコンパイルした。利用側の `KST.ProExcision.IntegerLinearizationAdjunction` と `HomologicalAlgebra.Cosimplicial.CupCommutativity` も検査した。保存比較 v3b は対象の移動前後 379 宣言で PASS、未説明差分 0 件。移動した宣言の Kerodon 属性 15 組を `#kerodon_tags` で再確認した。

### 並行する枝での追従

作業枝で追加した Lean ファイルのうち追従対象だけをリポジトリ相対パスの JSON 配列 `$files` にし、取り込み前の枝で `python3 scripts/refactor/klw1_namespace.py collect --root "$PWD" --files "$files" --output "$before_index"` を実行する。収集には、各ソースの依存を同じ版でビルドした Lean 成果物を使う。改名表を取り込んだ後、対象ソースの内容を収集時と揃えて、次の一行でプレビューを作る。

```sh
python3 scripts/refactor/klw1_namespace.py rewrite --root "$PWD" --files "$files" --index "$before_index" --plan scripts/refactor/targets/kl-namespace-map.json --output "$preview"
```

[`kl-module-map.json`](../../scripts/refactor/targets/kl-module-map.json) は旧 import から新 import への対応表で、[`kl-namespace-map.json`](../../scripts/refactor/targets/kl-namespace-map.json) の `modules` にも同じ対応が入る。プレビューの `review.json` で保留箇所を確認し、検査したソースを枝に反映する。移動先と旧名の両方が必要な場合、旧名を公開する互換モジュールを明示的に import する。現時点の改名表は、この報告で移動済みとした群を対象とする。段 3 全体の停止条件は未達。

### 関手圏の各点ごとの余極限

`KST/SConstruction/FunctorPointwiseColimitExistence` と同じ群に属する依存 4 本を Kerodon §7.1 の `LimitsAndColimits/LimitsAndColimits/` に移した。利用側 19 本を更新し、∞ 圏の外で参照される 11 名を `Project/Compatibility/KSTPointwiseColimits.lean` から公開した。ビルド鍵 `--wait 1800` で移動先 5 本、互換モジュール、利用側の `KST.SConstruction.FunctorInitialVertices` を検査した。保存比較 v3b は 18 宣言で PASS、未説明差分 0 件。

### 局所化の存在

`KST/LocalizingInvariants/GeneralLocalization` と同群の依存 9 本を Kerodon §6.3 の `AdjointFunctors/Localization/` に移した。利用側 7 本を更新し、∞ 圏の外で参照される 5 名を `Project/Compatibility/KSTLocalization.lean` から公開した。ビルド鍵 `--wait 1800` で移動先 10 本と互換モジュールをコンパイルし、`Derived.Localization.GroupoidCompletion` も新しい明示的な import で検査した。保存比較 v3b は 43 宣言で PASS、未説明差分 0 件。移動した Kerodon 属性も Lean で照合した。

### §9 の主題による配置

| 元の `F2/Presentable/` のファイル | 処理と根拠 |
| --- | --- |
| `Definition` | `HTT/PresentableInfinityCategories/Definition` に一体で置いた。HTT 5.5.1 の presentable 性が主題。小（余）極限とその保存は同じ API を成し、`HasSmallColimits` は移動前の 144 本のソースに現れる。Kerodon の対応に付けた 6 組の属性を維持した。 |
| `AccessibleFunctor` | Kerodon §9.4 の `LargeInfinityCategories/CompactGenerationAndAccessibility` に一体で置いた。HTT 5.4.2 にも由来し、二つの中心定義がともに Kerodon §9.4.8.1（Tag 06KY）に当たる。残りはその恒等・合成・濃度変更などの補題。 |
| `EquivalenceColimits` | `equivalence_isColimitCone_iff` を Kerodon §7.1 の `EquivalenceColimitCones` に分けた。残る二つの κ-filtered 余極限の輸送は `HTT/AccessibleInfinityCategories/EquivalenceColimits`。分割した補題は移動前の 15 本のソースに現れる。 |
| `Duality/RightUnitContractible` | `initialVertices_isContractibleKan` を Kerodon §4.7 の `InitialVerticesContractible` に分けた。随伴の右関手と実単位に関する残りの宣言は `HTT/PresentableInfinityCategories/RightUnitContractible`。分割した補題は移動前の 2 本のソースに現れる。 |

二つの分割を `split_module.py` で検査した。どちらも HTT に残す宣言から Kerodon に切り出す補題への依存だけがあり、逆向きの依存はなかった。移動先 6 本、外部から参照される 1 名の互換モジュール、および利用側の `AccessibleFunctorEquivalence`、`Duality.LeftUnitContractible`、`ContravariantContinuity` をビルド鍵 `--wait 1800` で検査した。v3b は 30 宣言で PASS、未説明差分 0 件。書き換えた利用側は 313 本で、属性も Lean の出力で再照合した。

`Core/Retracts` も §9 に当たる。頂点 retract の定義とその基本補題 9 宣言を Kerodon §8.5 の `VertexRetractions` に、HTT 5.1.4.2 の頂点条件の retract 閉包 6 宣言を `HTT/RetractsAndIdempotentCompletion/RetractClosure` に分けた。`split_module.py` で、閉包側から頂点 retract 側への依存だけであることを確認した。利用側 62 本を更新した。移動先 2 本、外部利用 5 名の互換モジュールと利用側の `Core.Idempotent.Coherent` を検査し、Kerodon 属性 2 組を再照合した。v3b は 15 宣言で PASS、未説明差分 0 件。

`Core/InitialBoundaryTransport` では、標準単体の最初の頂点についての補題を `split_module.py` で Kerodon §4.2 の `FirstVertexLeftAnodyne` に切り出し、HTT §1.2.12・§2.1.2 に沿った相対始対象の輸送を `HTT/InitialAndFinalObjects/InitialBoundaryTransport` に置いた。残る 3 宣言から切り出した補題への依存は一方向。移動先 2 本、外部利用 1 名の互換モジュールと `Core.TerminalBoundaryTransport` のビルドを通し、利用側 12 本の参照を更新した。v3b は 4 宣言で PASS、未説明差分 0 件。Kerodon 属性 1 組を再照合した。

### Ex∞

Ex∞ の構成、Kan 性、anodyne・ファイブレーション・局所化・モノイダル性と、その専用の補助を Kerodon §3.3 の `KanComplexes/TheExInfinityFunctor/` に移した。割り当て済み 60 本と、Ex∞ 群の外からは集約入口を除いて直接使われない補助 12 本。共有補助の `FiberwiseAnodyne`、`HornRightColimit`、`IntervalBoundaryFamily`、`PairContractionAnodyne`、`PairHomotopyLifting`、`SubcomplexContraction` は `KST/Comparison` に置き、移動した側の参照で境界を明示した。モデル圏を使う引き戻し比較も同じ場所に置いた。

利用側 153 本の import または参照を更新した。互換モジュール `Project/Compatibility/KSTExInfinity.lean` は ∞ 圏の外で参照される 8 名を公開する。ビルド鍵 `--wait 1800` で移動先 72 本、互換モジュール、残留 KST 側の 19 本を依存順に検査した。後者には `ArbitraryBasePullback`、`DiagramExInfinity`、`ExInfinityHomotopyPullback`、`ExInfinitySimplicialMonoid`、`SpanGluing` が含まれる。保存比較 v3b は 271 宣言で PASS、未説明差分 0 件。移動した属性 16 組も `#kerodon_tags` の出力と一致した。

### 集約入口

`public import` だけから成り、∞ 圏の宣言ファイルからは推移的にも import されない 47 本を `Project/Entrypoints/` に移した。利用側 31 本の import と README の入口リンクを更新した。宣言または実装側の利用を持つ候補 6 本は、入口に依存する定義側を調べる対象に残した。移動先 47 本がビルドを通過し、保存比較 v3b で 47 本すべての所有宣言数が前後とも 0 件であることを確かめた。

### 監査とドラフトの参照

Lean の宣言参照索引に載らない監査・ドラフトをソースから照合し、移動済みの旧名 790 箇所と、ドラフトの `IsPresentable` の選択的 `open`・相対参照を更新した。`audit_infinity_presentable.lean` の所有モジュールの検査には分割先を加えた。ドラフトの利用を根拠に `IsPresentable` の旧名も互換モジュールに加えた。書き換えた宣言の新名と公理一覧、追加した互換名は、ビルド鍵 `--wait 1800` で個別に照合した。

### 利用側のフィールドと書き換え道具

先に移動した型に対して、別ファイルに残る 42 メソッドを新しい型名で解決できるようにした。`with_weak_namespace … export …` で既存のメソッドを参照し、宣言の追加や数学的な変更は行っていない。AW を使う 9 本では、構造体を作る式のフィールドラベル 42 箇所を元の相対表記に戻した。合わせて 32 本の変更を、中間依存を含む 377 本の再コンパイルで検査した。

書き換え道具には、型とメソッドが別のモジュールにある場合、構造体のフィールドラベル、`@` 付きの識別子の処理を追加した。16 件の試験が通り、実際の改名表と並行枝向けコマンドでも、旧 AW import と旧名を持つ試験ファイルを新しいパスへ変換し、Lean で検査した。保存比較では、56,004 行の改名表で接頭辞を索引化し、従来のハッシュと同じ結果になることを確認した。

### 段 3 の到達点

作業枝に反映した範囲は、外から移す 4 群 143 本、§9 に該当した 6 本、集約入口 47 本。4 本を分割したため、旧 196 モジュールに対して移動先は 200 本。ここまでの対象ビルドを通し、移動前後の保存比較 v3b は 760 宣言、未説明差分 0 件。集約入口の所有宣言は前後とも 0 件。改名表の 196 モジュールと 775 名を確認し、追跡対象の Lean ソースから移動済みの旧モジュールへの import は 0 件だった。非推奨 alias は、∞ 圏外での利用を確認した 120 名に限った。

残る ∞ 圏内の 14,606 本は一時領域で移動先のソースを生成した。モデル圏の入力 3 本は元ソースを個別にビルドして索引を補った。`KanQuillen` にある既存の文献入力の `sorry` は移動前ソースに由来する。残りのプレビューから import 依存が閉じた先頭 64 本を選び、対象ビルドを通した。保存比較の最初の組では、参照索引の宣言欄に載らない `EnrichedDegree.Objects` が改名表から漏れ、宣言の増減と関連する型・本体で 7 件の差が出た。参照索引の別欄にある定義位置から改名規則を補い、最初の 16 本の再比較では 71 宣言で未説明差分 0 件。先頭 64 本の残りと全体の保存比較は継続課題。全体の改名表には、参照索引の各欄と Lean の保存比較の宣言一覧の照合が必要になる。

暫定配置の import グラフでは、未解決のプロジェクト内 import と循環はともに 0 件、Kerodon の節番号と逆向きの直接 import は 1,425 件。逆向きの辺と実装境界の扱いを確定し、5 層のファイル別設定に反映する作業が残る。**停止点 3 は未達。** 上の追従手順と作業枝の改名表は、反映済みの範囲に対応する。

### 段 3 の分割ビルド

残る移動対象 14,606 本と、対象が使う再コンパイル対象を import の依存順で検査している。当初の再コンパイル対象 2,919 本に、追加分割の移動先 1 本と、依存が変わるタグ所有ファイルを検査するための閉包 8 本を加えた。ビルド済みの成果物と失敗ログを塊ごとに保存し、ソースを修正したモジュールと、その成果物を使うモジュールを再検査する。各回に `--wait 1800` を指定し、取得後の実行は 1,740 秒で終了を要求し、10 秒後に強制終了する。第 13 回は、当時の調整役の指示に従い、取得要求を一つにまとめ、前の塊から 10 分以上空けた。全体を一度に通す確認の前には調整役に知らせる。

| 鍵を取得した回 | 成功 | 失敗 | 保持時間 |
| --- | ---: | ---: | ---: |
| 1 | 160 | 0 | 約 84 秒 |
| 2 | 353 | 47 | 約 205 秒 |
| 3 | 364 | 36 | 約 217 秒 |
| 4 | 726 | 74 | 約 435 秒 |
| 5 | 539 | 87 | 約 319 秒 |
| 6 | 443 | 77 | 約 267 秒 |
| 7 | 1,718 | 82 | 約 779 秒 |
| 8 | 1,766 | 34 | 約 1,062 秒 |
| 9 | 1,769 | 31 | 約 853 秒 |
| 10 | 1,756 | 44 | 約 1,161 秒 |
| 11 | 1,743 | 57 | 約 1,356 秒 |
| 12 | 1,762 | 38 | 約 1,205 秒 |
| 13 | 1,615 | 28 | 約 1,660 秒 |

表の件数には修正後の再試行を含む。第 12 回終了時点では、移動先 10,941 本と前提 2,119 本の成果物が有効だった。追加分割による再コンパイルを含む第 13 回の終了時点では、移動先 10,757 本と前提 2,042 本が有効。Lean が生成する補助名を指す既存の非推奨 alias は、左辺を維持して右辺を直した。旧名前空間の `open`、`cases` の枝名、移動で相対解決を失った名前も、ビルド診断と移動前の参照索引に沿って修正している。これらは移動のプレビュー内の進捗。

プレビューの改名表は、第一陣を含む 14,802 本のモジュール経路と、定義元付きの宣言経路 58,438 件を収録している。並行枝向けの一行コマンドをこの表で再実行し、試験ファイルの出力が第一陣で検査済みの出力と一致した。旧名 `IsFullyFaithful.preimageFunctorIso_postcomp` は、利用側によって異なる 2 モジュールの宣言を指す。書き換えでは Lean が記録した定義元を使う。同名の alias が一つの出力に混ざる場合は、利用範囲の分割を要求する。これらを覆う Python 試験を追加し、14 件が通った。Lean を使う 3 件はこの回の試験対象外。

層設定の確認用に、節番号と逆向きの 1,425 辺を移動前の参照索引と突き合わせた。1,136 辺に依存先の宣言への直接参照があり、残り 289 辺は `public import` による再公開。実装境界候補 1,173 辺でも、1,016 辺に直接参照があり、157 辺は再公開だった。これを段 1 の配置・分割案と照合し、残す辺の理由をファイル単位で記録する。

### 保存比較で使う宇宙変数と公理の照合

先頭 64 本の v3b で、401 宣言のうち 9 項目に差が出た。Lean が生成する `Direction.noConfusion` と `Direction.noConfusionType` の宇宙変数名に移動前後のモジュール名が入り、型と本文のハッシュが変わっていた。宣言名と束縛された宇宙変数名を対応させて式を照合すると、両方の型と本文は一致した。

公理一覧では `FreeQuiverCover.Vertex`、`TwoSidedDiagram.Data`、`TwoSidedElements.Hom`、`Word.Hom` とそれらの補助宣言で、Lean がエクスポートした一覧に差があった。帰納型とコンストラクタの循環に対して、キャッシュの走査順により一部の公理が記録されなかった。カーネル環境の型・本文から到達する公理を、各宣言を起点に再計算して、前後が一致することを確かめた。

`decl_snapshot.lean --stable-project` では、宇宙変数を宣言の束縛順で正規化し、プロジェクト内の公理への到達を再計算する。同じオプションを前後両方に指定して再比較し、先頭 64 本の 401 宣言すべてで未説明差分 0 件。残りの保存比較にも同じ指定を使う。



範囲を広げた比較では、第一陣の改名が抜けた依存名、`@[reassoc]` の生成名、名前解決用の `with_weak_namespace ... export ...` による生成補題の所属判定を補った。差が出た 4 組のうち 3 組を再実行し、1,386 宣言で差分 0 件。生成補題が追加扱いだった 4 件は、修正前のスナップショットでも型・属性・公理一覧が一致していた。比較器に所属判定の回帰試験を追加した。

残る 1 組の生の差 12 件は `DeprecatedAlias` の生成宣言の本文・所属に限られた。元ソースとプレビューの差が `namespace` と `end` の 2 行だけであることを確認し、この置換を元ソースに適用して移動先のモジュール名でコンパイルした。プレビューと `.olean` 本体・private・server、`.ilean`、`.ir`・sig の 6 成果物がバイト単位で一致し、生成宣言を含む 11 宣言の保存比較も差分 0 件。この 12 件は移動による生成結果の差として説明済み。


比較範囲を 1,920 本に広げ、前後の環境で定義元が一致する匿名 instance や生成補助宣言の 101 組を改名表に加えた。`LengthZero` と `WordCons` に同じ旧完全修飾名の宣言がある場合は、定義元が混ざらないよう比較群を分けた。既存の `deprecated_alias` をソース上の宣言として認識するように比較器を修正した。差が出た 7 組を再実行し、1,120 本、6,794 宣言で未説明差分 0 件。

### 追加分割と層の再検査

`F2/Presentable/AdjointFunctorTheorem` も §9 の分割候補とした。`split_module.py` で、随伴関手定理から前層の局所性判定への依存が一方向であることを確認した。プレビューでは `exists_rightAdjoint_iff_preservesSmallColimits` を Kerodon §9.5 に置き、局所性判定と連続前層の表現可能性の 2 宣言を `HTT/PresentableInfinityCategories/AdjointRepresentability` に分けた。両方の移動先のビルドと保存比較は継続中。

プレビューの現役 29,314 モジュールの import に循環・未解決のプロジェクト内 import は 0 件。追跡中の Lean ソースに移動済みの旧 import は 0 件。節番号と逆向きの直接 import は、依存先の直接参照がなく別の `public import` 経路が残る 73 辺を 61 モジュールから外した。残る 1,352 辺は、参照する宣言か再公開の理由を辺ごとに記録した。5 層の暫定設定を新しい import グラフに当て、未登録の実装境界、層順の違反、理由未登録の逆向き辺はすべて 0 件。直接 import を外した対象のビルドと保存比較を進めている。

タグ付き 367 本から、モジュール文書で HTT または HA を明記する 93 本を抽出し、主題とタグを付けた宣言を照合した。たとえば `Core/Idempotent/Coherent` の冪等図式と強い分裂、`DGNerve/Pullback` の単調写像による引き戻し、`HomotopyLimits/Presentable/LocalObjects` の局所対象の定義は、そのファイル自体の主題が Kerodon の対応に当たるので一体で置く。

`DGNerve/EdgeHomotopy` の主題は HA Example 1.3.1.8 の、左右の辺ホモトピーと閉零射の境界関係の比較。`edgeClosedEquiv`（Tag 00PZ）とその型に必要な `vertexClosed` を Kerodon §2.5 の `EdgeClosedEquivalence` に分け、比較の残り 9 宣言を `HA/DerivedCategoryModels/EdgeHomotopy` に置いた。`split_module.py` で元ソースと保存データを照合し、HA 側から Kerodon 側への依存だけであることを確認した。プレビューで利用側 72 本を書き換え、前回の成果物のうち依存が変わる 1,876 本を再検査に回した。この分割を加えた状態でも、旧 import、未解決 import、層違反は 0 件。

移動後のタグは、成果物がそろっていた 352 本で 644 組を登録環境から照合し、欠落・余分は 0 件。上の分割を含む最終配置でも残りと合わせて再照合する。並行枝の参照を調べ直したところ、外部互換名の候補集合に増減はなかった。外部利用の 5,956 名について、定義元を分けて署名の依存を集めている。

`WordForwardCore.forwardColumns` の本体差分では、`deriving DecidableEq` で生成された `instDecidableEqDirection` が改名表から漏れていた。カーネル式に現れる 6 定数の移動前後の名前を対応させると、型と本体が一致した。名前を補って 160 本、1,171 宣言を再比較し、未説明差分は 0 件。別ファイルにある同名の private 補助は、比較に限って定義元別の改名規則を保持した。

第 13 回は、取得要求の前に KL-W1 の待機要求をすべて取り下げ、10 分空けてから `--wait 1800` で取得した。保持時間は 27 分 40 秒。`EdgeClosedEquivalence` と HA 側の `EdgeHomotopy`、`FilteredPosetNerve` はビルドを通った。

保存比較ツールは、同じ入力で Lean の `--run` とバイト単位で出力が一致することを確認して、同じ Lean ソースをネイティブ実行した。追加分割後に残っていた成果物 9,254 本を比較した時点では、9,203 本で未説明差分 0 件。51 本で生成名の増減 148 行と、`DGKappaSpanPoset` の生成補助の差 1 行を検出した。前者は同じ定義元と元の宣言位置、後者は `deriving DecidableEq` の補助定数を照合し、比較用の改名表を補った。新しい規則での再比較を行う。

監査のプレビュー 54 本で、Lean の名前引用を含む旧名や旧ファイルパスを更新した。旧名が二つの定義元を指しうる 19 箇所は、前後の監査項目と追加時の履歴を照合した。旧ディレクトリ接頭辞で所有モジュールを選ぶ 14 箇所は、同じ旧ファイル群を `kl-module-map.json` から選ぶ方式に更新し、分割先も監査に含めた。監査の Lean 実行はこれから。


### ビルド時間帯の切り替え

`main` の `d8477d799` に入った指示書 §10 と `coordination.md` §2 を確認した。第 13 回の鍵は 19:56:29 JST に返し、続けて予定していた互換名検査の取得要求を取り下げた。以後、一括の検査・保存比較・対象ビルドは 23:00〜翌 08:00 JST に行う。取得には `--wait 1800` を使い、待機がタイムアウトしたときの自動再取得は行わない。夜間の取得後は 08:00 前に終了するよう制限する。昼は改名表、逆向きの import、層、監査と報告の静的な作業に充てる。小さな対象ビルドが必要な場合は 10 分以内。段 4 は調整役の暦に従い夜に行う。


## 停止点 3 の報告案

### 逆向きの import と 5 層

1,425 辺を用途で分類した。依存先の宣言を直接使う 1,136 辺は、Kerodon の主題に沿った配置と直接の依存を保つ。直接参照がない 289 辺は公開経路を照合し、代替の公開経路がある 73 辺を 61 ファイルから外した。残る 216 辺は公開の見せ直しに使うため維持する。削除後の実ソースで、73 辺すべてについて代替経路が `public import` だけでつながることを確認した。残す 1,352 辺、削除する 73 辺とその経路、実装境界の例外 1,175 辺は付表に記録した。[逆向き import と実装境界の付表](kerodon-layout-w1-stage3-reverse-imports.md)

| 層 | 割り当てファイル数 | 決まり |
| --- | ---: | --- |
| `SharedFoundation` | 198 | 共有の土台。保持した実装境界に推移的に依存しない。 |
| `Portable` | 6,240 | 可搬な構成。保持した実装境界に推移的に依存しない。 |
| `Comparison` | 8,396 | 実装への直接 import を許す箇所と根拠を辺ごとに登録する。 |
| `Entrypoints` | 59 | 入口、監査用の集約、互換名。 |
| `Consumers` | 1 | 利用側に置く ∞ 圏内の集約。層を明示していない外部の利用側もこの層に属する。 |

互換名の残りを加える前の集計。最終配置プレビューの現役 29,314 モジュールを Python だけで検査し、未解決 import、循環、層順違反、理由のない実装境界と逆向きの辺はすべて 0 件。設定は `layers.json` の `klw1` にまとめた。移動を反映した作業木での再現コマンドは `python3 scripts/refactor/layer_check.py --enforce KLW1 --root "$PWD"`。


### Tag の文章と README

既存の項目参照 6,246 件と節・小節参照 3,637 件に Tag を添えた。Kerodon 配下の 7,685 ファイルを照合し、対応節が書かれていなかった 7,672 本に追記した。番号・参照先 198 件と、見出し語 148 件を修正した。番号に対応する Tag の欠落や既存 Tag の不一致は 0 件。編集対象は 7,763 本で、うち 1 本は Archive。docstring を除いたバイト列は前後一致した。

元素 ∞ 圏の旧引用は、底変換、ファイバー、空間値の構成、小節全体の文脈に分けた。Kan fibration の塔の既存引用は付録で項目 Tag を確認した。README の番号照合表を修正し、∞ 圏の README は Kerodon の 51 節の番号・Tag・パス、HTT・HA・Project の役割、5 層の規則を説明する形に整えた。配置プレビュー上で両 README のローカルリンクを照合した。[底変換の Remark 5.6.2.18](https://kerodon.net/tag/0271)、[ファイバーの Example 5.6.2.19](https://kerodon.net/tag/0272)、[空間値の Example 5.6.2.9](https://kerodon.net/tag/026S)、[塔の Corollary 11.9.7.2](https://kerodon.net/tag/01C7)

文書の編集は同じ Lean コードの保存比較を再利用できるよう別のプレビューに保管した。型と本文の比較後に、照合したコードと docstring を合成し、全対象の確認ビルドでは文書も含む最終ソースを使う。

### レーン別の追従表

2026-11-12 11:32:40 JST に再確認した。動いている 4 レーンの追跡済み・未追跡の Lean ソースを import 行のテキスト検索で調べた。本体は `SerrePositivity/` 以下に絞り、drafts を除外した。⑤a・⑥は各レーンが確定した検証済み一覧を使い、他は各 HEAD と main の merge base からの差分に作業木の変更を加えた。「直すファイル」は枝固有のうち旧 import が直接あるもの。「収集対象」は確定した本体の Lean ファイルで、推移的な import から解決される旧名も書き換える。継承した旧 import は取り込み側の改名に含まれる。[対象ファイルと参照行](kerodon-layout-stop-3/lane-imports.json)。

HA・HTT・K の地図には現在の枝・作業木がなく、前回記録の HEAD が main の祖先であることを確認した。これらの現在の収集対象は空。実装 4 レーンの枝固有の直接旧 import は 計 10 本だった。推移的な参照を確認するため、計 117 本を収集対象とする。

`$handoff` は配布した `kerodon-layout-stop-3`、`$klw1` は KL-W1 の作業木。`$maps` は最終配置のコミットと同じ版の `kl-module-map.json`・`kl-namespace-map.json` を置いたディレクトリ（`$klw1/scripts/refactor/targets` でもよい）。取り込み前の枝で、各行の `*-files.json` を `$files` にして `python3 "$klw1/scripts/refactor/klw1_namespace.py" collect --root "$PWD" --files "$files" --output "$before_index"` を実行する。その同じソースを入力にして、以下の一行で新しい出力先 `$preview` にプレビューを作る。`review.json` とソース差分を確認し、main の取り込みと書き換えを一緒に反映する。

| レーン・枝 | 枝全体で旧 import があるファイル | 直すファイル（旧 import 行数） | 収集対象 | 書き換えの一行 |
| --- | ---: | ---: | ---: | --- |
| ⑤a `math/bs-impl` | 17,427 | 10（29 行） | [31](kerodon-layout-stop-3/bs-impl-files.json) | `python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite --root "$PWD" --files "$handoff/bs-impl-files.json" --index "$before_index" --plan "$maps/kl-namespace-map.json" --output "$preview"` |
| ⑤b `math/inf-supply-b` | 0 | 0（0 行） | [0](kerodon-layout-stop-3/bs-d68-files.json) | `python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite --root "$PWD" --files "$handoff/bs-d68-files.json" --index "$before_index" --plan "$maps/kl-namespace-map.json" --output "$preview"` |
| ⑤c `math/bs-classical` | 17,418 | 0（0 行） | [18](kerodon-layout-stop-3/bs-classical-files.json) | `python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite --root "$PWD" --files "$handoff/bs-classical-files.json" --index "$before_index" --plan "$maps/kl-namespace-map.json" --output "$preview"` |
| ⑥ `math/scheme` | 17,418 | 0（0 行） | [68](kerodon-layout-stop-3/scheme-files.json) | `python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite --root "$PWD" --files "$handoff/scheme-files.json" --index "$before_index" --plan "$maps/kl-namespace-map.json" --output "$preview"` |
| HA `research/ha-review` | — | 0（0 行） | [0](kerodon-layout-stop-3/ha-review-files.json) | `python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite --root "$PWD" --files "$handoff/ha-review-files.json" --index "$before_index" --plan "$maps/kl-namespace-map.json" --output "$preview"` |
| HTT `research/htt-review` | — | 0（0 行） | [0](kerodon-layout-stop-3/htt-review-files.json) | `python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite --root "$PWD" --files "$handoff/htt-review-files.json" --index "$before_index" --plan "$maps/kl-namespace-map.json" --output "$preview"` |
| K の地図 `research/k-maps` | — | 0（0 行） | [0](kerodon-layout-stop-3/k-maps-files.json) | `python3 "$klw1/scripts/refactor/klw1_namespace.py" rewrite --root "$PWD" --files "$handoff/k-maps-files.json" --index "$before_index" --plan "$maps/kl-namespace-map.json" --output "$preview"` |

drafts の import・名前は、調整役が改名表を使って文字列として追従させる。本体の collect には含めない。

`kl-module-map.json` は import の改名、`kl-namespace-map.json` は宣言の改名と分割先の定義元を収める。旧名の互換モジュールを使う場合も import は改名表で更新する。ファイルが追加された場合はレーン側でそのパスを収集対象の JSON 配列に加え、改名前の成果物とソースで収集し直す。

### 夜間の検証結果

11-10〜11-11 の夜間枠。集計は 11-11 08:00:20 JST。main の `f68a0abea` を `9bbc07615` に取り込み、草稿 5 本の衝突を解消した。新旧の依存をたどって 28 本を Lean で採取し、7 本の構文を採取結果と照合して補正した。追加 13 本を含む 38 本、旧 import 872 行を配置プレビューで更新した。追加ファイルで外部から使う 16 名を確認して互換名の対象に加えた。

| 確認項目 | 夜間の結果 |
| --- | --- |
| 移動先のビルド | 14,436 / 14,606 本。残り 170 本。 |
| 前提ファイルと互換名 | 2,848 / 2,980 本。互換モジュール 19 / 51 本、対象 alias 5,972 名。 |
| 保存比較 v3b | 14,233 本を比較し、14,217 本で未説明差分なし。未比較 373 本、現行比較の未説明差分 34 行。 |
| Lean の Kerodon 属性 | 367 / 367 モジュール、672 / 672 組が完全一致。 |
| 5 層の Python 検査 | 現役 29,492 モジュール。旧 import 0 件、未解決 import 0 件、層違反 0 件。 |
| root `lake build SerrePositivity` | 未着手。 |
| 全監査と verify | 未着手。予定対象は 103 本。段階 II の BS は `audit_bhatt_scholze_stage2.lean`、AlgebraicGeometry は `audit_kst_scheme_lemmas.lean`。 |
| 共有鍵 | 11-10 23:00:46 JST〜11-11 01:08:43 JST、11-11 06:07:30 JST〜11-11 07:05:37 JST、11-11 07:41:56 JST〜11-11 07:59:39 JST。 |

停止点 3 の条件を満たすまで、一括移動は作業枝に反映しない。夜間の完了通知は 1〜5 が完了したときに発行する。

保存されたビルドエラーのある起点は 7 本。未ビルドの集計には各起点に依存するファイルも含む。

- `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearHomCohomology`
- `SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactCoproduct`
- `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.CompactStage`
- `SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.PaddedBackwardInsertionComparison`
- `SerrePositivity.KST.LocalizingInvariants.SpectrumZeroClass`
- `SerrePositivity.KST.LocalizingInvariants.StrictCospanConeLegs`
- `SerrePositivity.KST.SConstruction.PerfectStableHoArrow`

現行の保存比較で差が残るモジュール。

- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CofinalPartialColimitFamilies`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceColimitIso`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePiecePresentations`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageMappedPartialConditions`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PartialFamilyValues`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeSmallPresentationPiece`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialConditions`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces`
- `SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedRefinementPresentation`
- `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeAttachmentOriginalSquares`
- `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeInverseNativeHomSquares`
- `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeNativeHomCoherence`
- `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeNativeHomSquare`
- `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TransportTriangleHomFamily`
- `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TransportTriangleHomParameters`
- `SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TransportTriangleInitialHom`

### 11-11 昼の修正と再検査の対象

朝の 302 本の内訳を、保存されたビルド結果と依存グラフから求めた。移動先 170 本のうち 164 本、前提 100 本のうち 94 本、互換 32 本の全本に未完了の前提がある。エラーログが残った起点は 7 本。互換モジュールに固有の型エラーは朝のログに残っていなかった。

| 原因 | ソースでの修正 |
| --- | --- |
| 移動後に解決できなくなった `open` | `LinearHomCohomology` と `DGModuleKappaCompactCoproduct` の `DoldKanComparison`、`KappaCovers.CompactStage` の `F2`、`PerfectStableHoArrow` の `F2.Idempotent` を外した。必要な移動済み参照は新しい名前で指定されている。 |
| 利用側で省略していた名前 | `PaddedBackwardInsertionComparison` の `FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence`、`SpectrumZeroClass` の `spectrumPoint`、`StrictCospanConeLegs` の `spectrumPullbackDiagram` を定義元の名前で明示した。旧 `.ilean` の参照と移動後の import 閉包を照合した。 |

7 本を配置プレビューで修正し、対象モジュールの再ビルドは夜に回した。前夜に修正した `GeneratorWord.erase` の非計算可能な互換名の指定も、互換モジュールを再生成するときに保持する。

保存比較の 34 行のうち 18 行は、`local instance : Fact Cardinal.aleph0.IsRegular` 9 宣言の追加・削除の対だった。前後で定義元、ソース範囲、型ハッシュ、属性、公理が対応することを確認し、定義元ごとに改名表を修正した。残る 16 行は局所記法から Lean が生成した 8 宣言の本文と親の差分だった。共有鍵の下で既存の成果物から前後の式を採取し、名前空間と hygiene の識別子、および既存の改名表で同じ定義を指す 2 種の識別子の綴りを対応させた。8 宣言の式が一致し、親の差は記法を定義した名前空間の移動と一致した。この照合結果を該当するビルドと差分行のハッシュに結び付けて保存した。

改名表を更新した時点で、現在の規則で有効な比較は 14,121 本で、未説明差分は 0 行。夜は、朝の未比較 373 本を優先し、改名表の更新で有効期限が切れた 112 本も再比較する。対象は付表に保存した。[朝の未比較 373 本](kerodon-layout-stop-3/overnight-uncompared-373.json)、[改名表更新後に再比較する 112 本](kerodon-layout-stop-3/overnight-recompare-112.json)

08:24 JST 時点の `main`（`6e6a3f9a7`）まで、⑤b・⑥の取り込みを含む差分の import を静的に確認した。前夜に書き換えた差分を保持し、23 時の `main` を取り込んでから、その時点の BS・EInfinity の追加分を再確認する。残りの対象ビルド、保存比較、root ビルド、全監査、verify の順で進める。

### 11-11 昼の再ビルドと保存比較（§11）

11:11 JST 集計。§11 の `main`（`263a6e1fc`）を `e0950c02e` に、§12 と整理券の繰り上げ方式を含む `cac43df5c` を `7415ebbed` に取り込んだ。追加された BS と基盤のファイルには、InfinityCategories の旧配置への直接・推移的な依存がなかった。前夜分の書き換え 38 ファイル・872 import 行を保持し、最新の root・BS の入口と監査の登録も配置プレビューに反映した。

| 確認項目 | 結果 |
| --- | --- |
| 移動先のビルド | 14,606 / 14,606 本 |
| 前提・互換モジュール | 2,980 / 2,980 本（互換 51 / 51 本） |
| 保存比較 v3b | 14,281 / 14,606 本。未説明 0 行 |
| 5 層の Python 検査 | 29,694 モジュール、層違反 0 件、旧 import 0 件、未解決 import 0 件 |

共有鍵の保持（JST）は09:18:20〜09:26:07、09:36:49〜10:01:38、10:37:04〜11:04:05。

§13 により昼の大きな枠を終了した。main の `7a689544b` から `with_build_lock.sh` を取り込み、昼の上限を 580 秒、待ちを `--wait 3600` に変更した。次の処理は今夜 23 時の main の取り込み後に行う。

今回、373 本と期限切れ 112 本を合わせた 485 本の比較を実行した。新たに出た 38 行は、3 モジュールの private な補助宣言 19 個の追加・削除だった。定義元とソースを照合して比較用の名前対応を 23 個追加した。これにより期限切れとなった 325 本の再比較を夜に回す。[対象の 325 本](kerodon-layout-stop-3/overnight-recompare-325.json)現在の規則で有効な 14,281 本には未説明の差分がない。

前夜は、対象ビルドが残っていても一定回数の後にスナップショットとタグの処理へ進み、処理列を終了する構成になっていた。01:08 に鍵を返した後、06:07 まで次の枠を開始できなかった。今夜は、各枠の完了後に残件を検査して次の段へ進み、停止が必要なら時刻と理由を報告へ記録する。

残りは移動先 0 本、前提・互換 0 本、未比較 325 本。

### 11-11 夕方の小枠による保存比較（§14）

19:29 JST 集計。main の 267277a0e を 0291ca816 に取り込み、coord 組と鍵の使用履歴を含む新しいスクリプトを使用した。当初は昼の上限を 280 秒、待ちを --wait 3600 に設定した。19:15 の改定後は上限を 170 秒、返却から次の要求までを 60 秒以上とした。

| 確認項目 | 結果 |
| --- | --- |
| 移動先・前提・互換のビルド | 17,586 / 17,586 本（移動先 14,606 本、前提・互換 2,980 本）。昼の再ビルド完了時の対象 |
| 保存比較 v3b | 現行の規則で 14,573 / 14,606 本が一致。未説明 0 行 |
| 再比較の残り | 33 本 |
| 鍵の履歴 | 全 14 枠。改定前を含む最長 280.09 秒。19:15 以降は 3 枠、最長 170.05 秒 |
| 5 層の静的検査 | 現役 29,868 モジュール。層違反 0 件、旧 import 0 件、未解決 import 0 件 |

夕方の処理では、残っていた 325 本のうち 292 本を小さな組に分けて再比較した。型・本文・名前の対応は、移動前後の成果物と現在の改名表で照合した。

19:15 の改定を受け、実行中だった枠は 19:16:48 に約 63 秒で終了して鍵を返した。その後は 60 秒以上空けてから、170 秒の枠で再開した。

19:25:41 JST の枠は 170 秒で打ち切った。移動前の 2 組の採取結果は正常な JSON として保存済みだが、比較の完了には届かなかった。60 秒を空けて状態を確認し、昼の再要求は終了した。[夜に回す残り 33 本](kerodon-layout-stop-3/evening-recompare-33.json)。19:15 改定後の次の要求までの間隔は実測 119.58 秒、81.32 秒で、いずれも 60 秒以上だった。

夜の継続処理は、既存の移動先が全部済んでいても main 差分の参照採取と書き換えを必ず終えてから、最終配置・root ビルドへ進むよう補正した。

追加された main の差分について、import の配置プレビューを更新した。新たに参照採取が必要な EInfinity・BS 等のファイルは夜の作業に含める。root ビルド・全監査・verify は、23 時の main の取り込みと参照の書き換えを終えてから行う。

### 11-11 昼の隙間の継続と再照合

20:37 JST 集計。調整役の継続指示を受けて 19:35 から小枠を再開した。上限 170 秒、返却後から次の要求まで 60 秒以上、`--wait 3600` を、保存比較・タグ・互換名の照合で共通に適用する。

| 確認項目 | 結果 |
| --- | --- |
| 保存比較 v3b | 14,606 / 14,606 本が一致。未説明 0 行 |
| 移動先・前提・互換のビルド | 既報の 17,586 / 17,586 本（移動先 14,606 本、前提・互換 2,980 本） |
| タグの新たな照合 | 672 / 672 組。対象 367 モジュール。前夜の 672 組の一致に加え、最終配置の成果物で再照合も全件一致 |
| 外部利用と互換名のソース | 元の 5,956 名と追加 16 名の全 5,972 名が一致。互換 51 モジュール、欠落 0、余分 0 |
| 互換名の成果物 | 5,972 / 5,972 名を照合済み。元の 5,956 名のうち 5,956 名 |
| root・全監査・verify | 未着手。23 時以降の対象 |

最後の保存比較で `ModNerve._proof_1` の型差分が 1 行出た。private 略記 `B := PUnit.{1}` の名前が比較表から漏れていたためだった。定義元を指定して前後の型を採取し、宇宙パラメータが同じで、private 定数の名前だけを対応させると式の構造が完全一致することを確認した。比較用の名前対応を 1 件追加し、影響する 6 本・46 宣言を採取し直して、20:11 に全件一致を確認した。Lean のソースの修正は不要だった。[型と成果物の根拠](kerodon-layout-stop-3/private-B-type-explanation.json)。

タグは古い照合結果に頼らず新たな照合セッションで採取し、完了した組を保存する。互換名は同じ旧名の別定義を混ぜない二つの環境に分け、所有元・型・定数そのものの本文・deprecated 属性を確認する。全監査は夜の verify で行う。

完了時の [照合記録](kerodon-layout-stop-3/daytime-preflights-receipt.json) に件数と入出力のハッシュを保存した。互換名の型は 5,690 名で検証済み alias の置換後に構造一致し、残る 282 名も Lean の還元可能な型の等しさの検査に通った。全 5,972 名の本文は対応する定数そのものだった。共有鍵の履歴による返却から次の整理券発行までの最短は 60.068 秒。

夜は 23 時にその時点の main（281f5420f 以降）を取り込んで差分の参照を書き換え、残る確認と段 4 に続ける。二つの鍵のどちらを取得しても自分の保持を確認できるようにし、verify の設定は `VERIFY_JOBS=4 VERIFY_MEMORY_GB=32` に変更した。

## 停止点 3 — 取り込み前の最終検証（2026-11-12）

main `f654cdc11`（⑤c の停止点 4、⑤a の途中、⑥ の AlgebraicGeometry 120 モジュールを含む）を `6a22ffb0a` で取り込んだ。夕方以降の EInfinity・BS 等の参照採取は 147 / 147 本、書き換えは累計 71 ファイル・898 import 行。AlgebraicGeometry には InfinityCategories への依存がなく、配置の書き換えは不要だった。一括移動は `4e656a4c6` で作業枝に反映し、その後の利用側の名前解決の修正を含む **`1304c688ff9e4b2486f547310d07bfc25a2780d7`** を検証した。§15 に従い、ここに記載した root・監査・verify では共有鍵を取得していない。

| 確認項目 | 最終結果 |
| --- | --- |
| 対象ビルド | 移動先 14,606 / 14,606 本、前提・互換 2,980 / 2,980 本。移動先の検証用ソースで完了。後続の root・verify は実際の配置で実行 |
| 保存比較 v3b | 14,606 / 14,606 本。未説明 0 行。第一陣 196 モジュール・760 宣言は既報の比較と合わせて確認 |
| Kerodon 属性 | 367 モジュール・672 組が一致。欠落・余分 0。own・both の対象だけを付与し、§6 の除外を維持 |
| 一括移動の互換名 | 所有元付き 5,995 件 / 5,995 件の型・本文・属性等が一致。元の外部利用 5,956 件と main 差分の追加 39 件を含む |
| 第一陣の互換名 | 120 件。上の 5,995 件と合わせ、今回のレーンで新設した alias 宣言は 6,115 件。以前からある非推奨名とは別集計 |
| 5 段の層 | 現役 30,226 モジュールで違反 0。旧 import・未解決 import・循環 0 |
| root ビルド | `lake build SerrePositivity`：成功（30,355 ジョブ、終了コード 0） |
| 全監査 | 103 / 103 本成功（失敗 0、既知扱い 0）。BS 段階 II・AlgebraicGeometry を含む |
| verify | PASS（終了コード 0、`gate: true`、監査の省略 0）。`VERIFY_JOBS=6 VERIFY_MEMORY_GB=44`（11-12 09:40 のユーザー判断）。指定された大きい 3 本を排他にし、修正後の実測が未採取の 2 本も同じ排他グループに入れて並列実行。キャッシュによる監査省略や対象限定のフックは使用しない |

[最終の検証記録](kerodon-layout-stop-3/stop-3-final-receipt.json) に、検証した HEAD、main、ビルド・監査の結果、保存比較と alias の件数、入力・出力のハッシュを残した。同じ綴りの旧名が異なる元モジュールにある場合は所有元を区別し、互換名の照合は衝突しない二つの環境に分けた。型と本文の数学的な変更は行っていない。最後に実際の worktree のコンパイル済み成果物からも、367 モジュール・672 組の属性を再照合し、欠落・余分 0 を確認した。互換モジュール 51 本は、5,995 件のカーネル検査に使ったソースとのコード一致を確認し、最終ソースと検査用ソース・成果物のハッシュを記録した。

### §9 の最終配置

以下は `SerrePositivity/InfinityCategories/` 以下のパス。先の経過欄でプレビュー・継続中とした AFT と EdgeHomotopy の分割も、両方の出力を対象ビルドと保存比較に含めて完了した。

| 旧ファイル | 配置 | 判断 |
| --- | --- | --- |
| `F2/Presentable/Definition` | `HTT/PresentableInfinityCategories/Definition.lean` | HTT の主題を一体で保持し、対応する宣言に Kerodon 属性を付けた。 |
| `F2/Presentable/AccessibleFunctor` | `Kerodon/LargeInfinityCategories/CompactGenerationAndAccessibility/AccessibleFunctor.lean` | 中心の定義が Kerodon §9.4 に当たるため一体で配置した。 |
| `F2/Presentable/EquivalenceColimits` | `HTT/AccessibleInfinityCategories/EquivalenceColimits.lean / Kerodon/LimitsAndColimits/LimitsAndColimits/EquivalenceColimitCones.lean` | 同値による余極限錐の輸送を Kerodon §7.1、κ-filtered 余極限の輸送を HTT に分けた。 |
| `F2/Presentable/Duality/RightUnitContractible` | `HTT/PresentableInfinityCategories/RightUnitContractible.lean / Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/InitialVerticesContractible.lean` | 頂点の可縮性を Kerodon §4.7、実単位と随伴の残りを HTT に分けた。 |
| `Core/Retracts` | `HTT/RetractsAndIdempotentCompletion/RetractClosure.lean / Kerodon/TheYonedaEmbedding/RetractsAndIdempotents/VertexRetractions.lean` | 頂点 retract を Kerodon §8.5、retract 閉包を HTT に分けた。 |
| `Core/InitialBoundaryTransport` | `HTT/InitialAndFinalObjects/InitialBoundaryTransport.lean / Kerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/FirstVertexLeftAnodyne.lean` | 標準単体の最初の頂点の補題を Kerodon §4.2、相対始対象の輸送を HTT に分けた。 |
| `DGNerve/EdgeHomotopy` | `HA/DerivedCategoryModels/EdgeHomotopy.lean / Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/EdgeClosedEquivalence.lean` | 辺と閉零射の同値および必要な頂点を Kerodon §2.5、HA の比較の残りを HA に分けた。 |
| `F2/Presentable/AdjointFunctorTheorem` | `Kerodon/LargeInfinityCategories/PresentableInfinityCategories/AdjointFunctorTheorem.lean / HTT/PresentableInfinityCategories/AdjointRepresentability.lean` | 右随伴と余極限保存の判定を Kerodon §9.5、前層の局所性・表現可能性を HTT に分けた。 |

### 利用側・文章・例外案

今回移動しない KST 側の `pointedMappingFunctor`・`spectrumPullbackDiagram` 等は元の定義名を保持し、利用側の参照をその完全修飾名で明示した。利用側では、無効になった `open`、コンストラクタの枝名、移動した型に対して外に残るメソッドの呼び出しを整理した。`cases`・`induction` の枝は `intro` や `@intro` の元の短い名前に保ち、外部の拡張メソッドは元の公開名への明示的な適用にした。移動しない宣言を相対名で使う 14 本では、必要な `open` を保持した。配布用ツールは、短い枝名を維持し、移動した型の未移動メソッドと、改名表にない生成メンバー（コンストラクタ・`reassoc` 等）を `review.json` に出して保留する。さらに、値と射影が別々の参照範囲になる場合も追跡し、解決できない相対 `open` は保留する。固定版 Lean の三つの実例を含む全 23 件の回帰検査が通った。

docstring の項目 Tag 追記は 6,246 箇所、見出しの Tag は 3,638 箇所、節の案内の新設は 7,672 箇所。種別 148 箇所・番号 198 箇所を補正し、未解決の引用・Tag 不一致は 0 件。対象は 7,764 ファイル（現役 7,763、Archive 1）。InfinityCategories の README を配置・節 Tag・5 層の規則に合わせた。旧レーンの README 2 ファイルのリンク 5 箇所も新しい Lean パスに直した。

逆向きの例外は **1,352 辺（直接参照 1,136、public import の見せ直し 216）** の案を維持する。public の元の 289 辺から、他の経路で見せ直せる 73 辺を整理した。層検査の違反 0 は、理由付きの個別例外案を設定した結果であり、例外一覧は停止点 3 での調整役の確認対象とする。

監査スクリプトに残った短い旧名と生成名は、main `f654cdc11` の元ソース 16 本から Lean の参照情報を採取し、定義元を区別して書き換えた。移動しない `DGSuspensionCoherentActionInput.ofSquareFamily` の名前は元に戻した。既存の非推奨メッセージ 5 件は本文と日付を維持し、現在の宣言名とメッセージ中の旧名を区別して、同じ内容を厳密に照合する。値に続く射影 40 箇所は、修正後の Lean の参照情報でも元の所有元と一致した。`open` の削除は個別の import 環境で存在しないと確認した単純な名前だけとし、複数の名前を持つコマンドの有効な部分を保持した。局所化監査は旧 185 モジュールの像を明記し、LocalObjects の 8 本の除外と三公理の条件を維持した。計数は 1,007 から 1,014 宣言になったが、差の 7 件は旧環境で自動名が他のモジュールと衝突していた既存の `Fact Cardinal.aleph0.IsRegular` 局所 instance が、移動後は別の完全修飾名で数えられるためである。[監査の書き換え記録](kerodon-layout-stop-3/audit-rewrite-receipt.json) に、元ソース・参照情報・出力のハッシュと回帰検査の結果を残した。

11-12 09:40 の指示で 3 回目の直列 full verify を停止し、実測を再利用して 6 ジョブ・44 GB で実行し直した。`VERIFY_EXCLUSIVE_AUDITS` に空白区切りで列挙した監査は、同時に一つだけを実行する。対象の一覧・検査内容・合否条件は維持した。今回は `scripts/audit_infinity_f1.lean`・`scripts/audit_infinity_f1b.lean`・`scripts/audit_infinity_core.lean` と、修正後の実測がなかった `scripts/audit_einfinity.lean`・`scripts/audit_infinity_presentable_localization.lean` を指定した。小さい監査はメモリ予算内で並列化し、公理監査と sorry 閉包は従来どおり最後に直列で実行する。スケジューラ 12 件・再試行 12 件の回帰検査が成功した。最終記録には、設定・実測の出所・排他の対象と最大同時数を残した。今回の verify は 37 分 7 秒、最大同時実行 6 本、排他グループの同時実行は最大 1 本だった。監査プロセス木の同時 RSS 合計の観測最大は 39.0 GB（十進）である。

公開する改名表は 14,802 モジュール・58,365 宣言の対応で、二つの表のモジュール対応は全件一致する。並行枝の対象と一行コマンドは上の「レーン別の追従表」を更新した。新しいファイルを作り足した場合はその JSON 一覧に足し、取り込み前の同じソースから参照を採取して、最終版の `$maps/kl-namespace-map.json` でプレビューを作る。未移動メソッド等が保留された場合は、明示呼び出しまたは export を確認し、各レーンで対象ビルドを行う。

ここで停止点 3 を提出し、調整役の確認を待つ。

## 改名追従の道具の修正（2026-11-12）

⑤c の `RootFamilySparseBasis.rootFamilySparseFractionCoordinates_smul` は、通常の Lake ModuleSetup では成功し、旧採取器の空の設定では失敗した。`maxSynthPendingDepth = 3` だけを補った同期採取でも成功したため、今回の再現の差をこの設定に絞れた。採取器は `lake --no-build setup-file` のファイル別 ModuleSetup から、オプション・package・import の可視性・プラグイン等を引き継ぐ。設定の取得に失敗したときは明示エラーにし、依存のビルドは事前に済ませる。同期スナップショットだけを意図的な上書きとして残す。

修正途中の共有ヘルパーを⑥の実行中に変更し、`String` と `FilePath` の型推論、および `ProcessingT IO` への IO の持ち上げの二つのコンパイルエラーを混ぜた。共有版を確定版に戻し、修正・検証は隔離ディレクトリで行ってから公開した。修正版の collect は開始時にヘルパーを一度コピーして全ファイルで固定し、各 capture に `elaboration.collector_sha256`・Lake setup のハッシュ・引き継いだ設定を記録する。公開は検証済みファイルの原子的な置換で行った。

⑤a の open は、未移動の宣言を持つ旧 `SimplicialLocalization`・`ComonadResolutionOperators` を保持し、移った宣言の参照は新しい完全名へ置く方針を採る。旧 `HomotopyLimits` も全体で保持し、参照がすべて移動済みの四つの利用モジュールだけ、不要な open を `module_opens` で削除する。移動先の名前空間を open に追加しない。`open scoped Simplicial` は Mathlib の `_root_.Simplicial` に固定する。明示的宇宙 `RelativeCategory.{u}` は Lean の `explicitUniv` 構文木の識別子部分だけを編集対象にし、`.{u}`・`.{max u 1}` 等の宇宙構文を保持する。

| 対象 | 検証結果 | 再利用できる採取・プレビュー |
| --- | --- | --- |
| ⑤c 本体18本 | collect 18/18 成功、元の `756352681` とソース一致 | `/tmp/klw1-collect-fix/c18-index` |
| ⑤a 本体31本 | collect 31/31 成功、rewrite 31/31・保留0。元の `36da456c0` とソース一致 | `/tmp/klw1-collect-fix/a31-index`・`/tmp/klw1-collect-fix/a31-preview` |
| ⑥ 検証済み68本 | 全68本を新規採取し、`69ace8712` とソース一致。rewrite も68/68・保留0 | `/tmp/klw1-collect-fix/s68-index`・`/tmp/klw1-collect-fix/s68-preview` |

全117本のソースに変更はなく、全 capture で同じヘルパー SHA と `maxSynthPendingDepth = 3` を確認した。⑥は17本ずつの採取を、全件のソース・版・範囲を再照合してから完全な68本の index にまとめた。共有鍵は `--wait 3600` で各採取の間だけ取得し、長い一回は580秒以内に区切った。実 Lean の四つの例を含む回帰検査28件がすべて成功した。[検証記録とソースのハッシュ](kerodon-layout-stop-3/collector-support-receipt.json)。

配布する `*-files.json` は本体だけに絞り、⑤a は確定した31本、⑥は検証済み68本を採用した。`formalization-plans/bhatt-scholze/drafts/`・`scheme-drafts/` 等は含めない。drafts は調整役が文字列として追従させる。⑤b は改名追従を完了して `math/inf-supply-b` へ移行済みなので、旧配置の追従対象は空とする。起動済みの旧 collect と未完成 index を流用せず、修正版を新たに起動して新しい出力先で採取する。上記 index の再利用時も、入力ソースのバイト列の一致を確認する。
