# KL-W1 段 0・段 1 報告

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
