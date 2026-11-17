# ∞ 圏基盤の地図

quasicategory 模型を使う。∞ 圏は `X : SSet` と `[Quasicategory X]`、
関手は単体的集合の射、関手 ∞ 圏は `(ihom X).obj Y` で表す。
極限は slice の終対象、写像空間は右 pinched Hom として定義する。

## 典拠に沿った配置

`Kerodon/<章>/<節>/` は Kerodon の主題順に並ぶ。章・節のディレクトリ名には英語見出しを使い、番号と Tag は下の一覧で引く。module docstring の Tag は対応する節・小節を指す。宣言の `@[kerodon TAG]` は、項目と対応することを確認した自前の宣言を指す。[Lean で照合した属性一覧](../../research/kerodon-coverage/kerodon-tags-lean.txt)

`HTT/` と `HA/` は、それぞれ HTT・HA が主題の構成を収める。presentable 性の定義は [HTT の Definition](HTT/PresentableInfinityCategories/Definition.lean)、dg nerve の辺ホモトピーと閉零射の境界関係の比較は [HA の EdgeHomotopy](HA/DerivedCategoryModels/EdgeHomotopy.lean) にある。後者が使う辺と閉零射の同値は [Kerodon の EdgeClosedEquivalence](Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/EdgeClosedEquivalence.lean) に置く。`Project/` はプロジェクト固有の比較、集約入口、互換名を収める。

### Kerodon の節

この配置にファイルがある 51 節を示す。小節と本文の見出しは Kerodon の目次で引ける。[節・小節の目次](../../research/kerodon-coverage/toc.md)

| 節と Tag | 見出し | ディレクトリ |
| --- | --- | --- |
| [1.1（Tag 0004）](https://kerodon.net/tag/0004) | Simplicial Sets | [`Kerodon/TheLanguageOfInfinityCategories/SimplicialSets/`](Kerodon/TheLanguageOfInfinityCategories/SimplicialSets/) |
| [1.2（Tag 0508）](https://kerodon.net/tag/0508) | From Topological Spaces to Simplicial Sets | [`Kerodon/TheLanguageOfInfinityCategories/FromTopologicalSpacesToSimplicialSets/`](Kerodon/TheLanguageOfInfinityCategories/FromTopologicalSpacesToSimplicialSets/) |
| [1.3（Tag 002L）](https://kerodon.net/tag/002L) | From Categories to Simplicial Sets | [`Kerodon/TheLanguageOfInfinityCategories/FromCategoriesToSimplicialSets/`](Kerodon/TheLanguageOfInfinityCategories/FromCategoriesToSimplicialSets/) |
| [1.4（Tag 0039）](https://kerodon.net/tag/0039) | ∞-Categories | [`Kerodon/TheLanguageOfInfinityCategories/InfinityCategories/`](Kerodon/TheLanguageOfInfinityCategories/InfinityCategories/) |
| [1.5（Tag 0055）](https://kerodon.net/tag/0055) | Functors of ∞-Categories | [`Kerodon/TheLanguageOfInfinityCategories/FunctorsOfInfinityCategories/`](Kerodon/TheLanguageOfInfinityCategories/FunctorsOfInfinityCategories/) |
| [2.4（Tag 00JN）](https://kerodon.net/tag/00JN) | Simplicial Categories | [`Kerodon/ExamplesOfInfinityCategories/SimplicialCategories/`](Kerodon/ExamplesOfInfinityCategories/SimplicialCategories/) |
| [2.5（Tag 00ND）](https://kerodon.net/tag/00ND) | Differential Graded Categories | [`Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/`](Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/) |
| [3.1（Tag 00SZ）](https://kerodon.net/tag/00SZ) | The Homotopy Theory of Kan Complexes | [`Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/`](Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/) |
| [3.2（Tag 00V2）](https://kerodon.net/tag/00V2) | Homotopy Groups | [`Kerodon/KanComplexes/HomotopyGroups/`](Kerodon/KanComplexes/HomotopyGroups/) |
| [3.3（Tag 00XF）](https://kerodon.net/tag/00XF) | The $\operatorname{Ex}^{\infty }$ Functor | [`Kerodon/KanComplexes/TheExInfinityFunctor/`](Kerodon/KanComplexes/TheExInfinityFunctor/) |
| [3.4（Tag 0106）](https://kerodon.net/tag/0106) | Homotopy Pullback and Homotopy Pushout Squares | [`Kerodon/KanComplexes/HomotopyPullbackAndHomotopyPushoutSquares/`](Kerodon/KanComplexes/HomotopyPullbackAndHomotopyPushoutSquares/) |
| [3.5（Tag 0513）](https://kerodon.net/tag/0513) | Truncations and Postnikov Towers | [`Kerodon/KanComplexes/TruncationsAndPostnikovTowers/`](Kerodon/KanComplexes/TruncationsAndPostnikovTowers/) |
| [3.6（Tag 012Y）](https://kerodon.net/tag/012Y) | Comparison with Topological Spaces | [`Kerodon/KanComplexes/ComparisonWithTopologicalSpaces/`](Kerodon/KanComplexes/ComparisonWithTopologicalSpaces/) |
| [4.1（Tag 01B8）](https://kerodon.net/tag/01B8) | Inner Fibrations | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/InnerFibrations/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/InnerFibrations/) |
| [4.2（Tag 014H）](https://kerodon.net/tag/014H) | Left and Right Fibrations | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/) |
| [4.3（Tag 015M）](https://kerodon.net/tag/015M) | The Slice and Join Constructions | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/) |
| [4.4（Tag 01EM）](https://kerodon.net/tag/01EM) | Isomorphisms and Isofibrations | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/IsomorphismsAndIsofibrations/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/IsomorphismsAndIsofibrations/) |
| [4.5（Tag 01DE）](https://kerodon.net/tag/01DE) | Equivalence | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/Equivalence/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/Equivalence/) |
| [4.6（Tag 01J3）](https://kerodon.net/tag/01J3) | Morphism Spaces | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/) |
| [4.7（Tag 05EA）](https://kerodon.net/tag/05EA) | Truncated Objects and Higher Homotopy Categories | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/) |
| [4.8（Tag 0578）](https://kerodon.net/tag/0578) | Full, Faithful, and Essentially Surjective Functors | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/FullFaithfulAndEssentiallySurjectiveFunctors/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/FullFaithfulAndEssentiallySurjectiveFunctors/) |
| [4.9（Tag 03PP）](https://kerodon.net/tag/03PP) | Size Conditions on ∞-Categories | [`Kerodon/TheHomotopyTheoryOfInfinityCategories/SizeConditionsOnInfinityCategories/`](Kerodon/TheHomotopyTheoryOfInfinityCategories/SizeConditionsOnInfinityCategories/) |
| [5.1（Tag 01T1）](https://kerodon.net/tag/01T1) | Cartesian Fibrations | [`Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/`](Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/) |
| [5.2（Tag 019A）](https://kerodon.net/tag/019A) | Covariant Transport | [`Kerodon/FibrationsOfInfinityCategories/CovariantTransport/`](Kerodon/FibrationsOfInfinityCategories/CovariantTransport/) |
| [5.3（Tag 035A）](https://kerodon.net/tag/035A) | Fibrations over Ordinary Categories | [`Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/`](Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/) |
| [5.5（Tag 01YV）](https://kerodon.net/tag/01YV) | The ∞-Category $\operatorname{\mathcal{QC}}$ | [`Kerodon/FibrationsOfInfinityCategories/TheInfinityCategoryQC/`](Kerodon/FibrationsOfInfinityCategories/TheInfinityCategoryQC/) |
| [5.6（Tag 027M）](https://kerodon.net/tag/027M) | Classification of Cocartesian Fibrations | [`Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/`](Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/) |
| [6.1（Tag 02CA）](https://kerodon.net/tag/02CA) | Adjunctions in $2$-Categories | [`Kerodon/AdjointFunctors/AdjunctionsInTwoCategories/`](Kerodon/AdjointFunctors/AdjunctionsInTwoCategories/) |
| [6.2（Tag 02EH）](https://kerodon.net/tag/02EH) | Adjoint Functors Between ∞-Categories | [`Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/`](Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/) |
| [6.3（Tag 01M4）](https://kerodon.net/tag/01M4) | Localization | [`Kerodon/AdjointFunctors/Localization/`](Kerodon/AdjointFunctors/Localization/) |
| [7.1（Tag 02H1）](https://kerodon.net/tag/02H1) | Limits and Colimits | [`Kerodon/LimitsAndColimits/LimitsAndColimits/`](Kerodon/LimitsAndColimits/LimitsAndColimits/) |
| [7.2（Tag 02MZ）](https://kerodon.net/tag/02MZ) | Cofinality | [`Kerodon/LimitsAndColimits/Cofinality/`](Kerodon/LimitsAndColimits/Cofinality/) |
| [7.3（Tag 02Y1）](https://kerodon.net/tag/02Y1) | Kan Extensions | [`Kerodon/LimitsAndColimits/KanExtensions/`](Kerodon/LimitsAndColimits/KanExtensions/) |
| [7.4（Tag 02SX）](https://kerodon.net/tag/02SX) | Limits and Colimits of Spaces | [`Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/`](Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/) |
| [7.5（Tag 039Y）](https://kerodon.net/tag/039Y) | Homotopy Limits and Colimits | [`Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/`](Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/) |
| [7.6（Tag 03E8）](https://kerodon.net/tag/03E8) | Examples of Limits and Colimits | [`Kerodon/LimitsAndColimits/ExamplesOfLimitsAndColimits/`](Kerodon/LimitsAndColimits/ExamplesOfLimitsAndColimits/) |
| [7.7（Tag 05SB）](https://kerodon.net/tag/05SB) | Universality of Colimits | [`Kerodon/LimitsAndColimits/UniversalityOfColimits/`](Kerodon/LimitsAndColimits/UniversalityOfColimits/) |
| [8.1（Tag 03JB）](https://kerodon.net/tag/03JB) | Twisted Arrows and Cospans | [`Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/`](Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/) |
| [8.2（Tag 043P）](https://kerodon.net/tag/043P) | Couplings of ∞-Categories | [`Kerodon/TheYonedaEmbedding/CouplingsOfInfinityCategories/`](Kerodon/TheYonedaEmbedding/CouplingsOfInfinityCategories/) |
| [8.3（Tag 03LZ）](https://kerodon.net/tag/03LZ) | The Yoneda Embedding | [`Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/`](Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/) |
| [8.4（Tag 03V7）](https://kerodon.net/tag/03V7) | Cocompletion | [`Kerodon/TheYonedaEmbedding/Cocompletion/`](Kerodon/TheYonedaEmbedding/Cocompletion/) |
| [8.5（Tag 03Y9）](https://kerodon.net/tag/03Y9) | Retracts and Idempotents | [`Kerodon/TheYonedaEmbedding/RetractsAndIdempotents/`](Kerodon/TheYonedaEmbedding/RetractsAndIdempotents/) |
| [8.6（Tag 04C0）](https://kerodon.net/tag/04C0) | Conjugate and Dual Fibrations | [`Kerodon/TheYonedaEmbedding/ConjugateAndDualFibrations/`](Kerodon/TheYonedaEmbedding/ConjugateAndDualFibrations/) |
| [9.1（Tag 05WY）](https://kerodon.net/tag/05WY) | Filtered ∞-Categories | [`Kerodon/LargeInfinityCategories/FilteredInfinityCategories/`](Kerodon/LargeInfinityCategories/FilteredInfinityCategories/) |
| [9.2（Tag 0639）](https://kerodon.net/tag/0639) | Finitary Functors and Compact Objects | [`Kerodon/LargeInfinityCategories/FinitaryFunctorsAndCompactObjects/`](Kerodon/LargeInfinityCategories/FinitaryFunctorsAndCompactObjects/) |
| [9.3（Tag 06FR）](https://kerodon.net/tag/06FR) | Ind-Completions of ∞-Categories | [`Kerodon/LargeInfinityCategories/IndCompletionsOfInfinityCategories/`](Kerodon/LargeInfinityCategories/IndCompletionsOfInfinityCategories/) |
| [9.4（Tag 06GT）](https://kerodon.net/tag/06GT) | Compact Generation and Accessibility | [`Kerodon/LargeInfinityCategories/CompactGenerationAndAccessibility/`](Kerodon/LargeInfinityCategories/CompactGenerationAndAccessibility/) |
| [9.5（Tag 06NC）](https://kerodon.net/tag/06NC) | Presentable ∞-Categories | [`Kerodon/LargeInfinityCategories/PresentableInfinityCategories/`](Kerodon/LargeInfinityCategories/PresentableInfinityCategories/) |
| [9.6（Tag 04KF）](https://kerodon.net/tag/04KF) | Factorization Systems | [`Kerodon/LargeInfinityCategories/FactorizationSystems/`](Kerodon/LargeInfinityCategories/FactorizationSystems/) |
| [9.7（Tag 06ZD）](https://kerodon.net/tag/06ZD) | Tensor Products of ∞-Categories | [`Kerodon/LargeInfinityCategories/TensorProductsOfInfinityCategories/`](Kerodon/LargeInfinityCategories/TensorProductsOfInfinityCategories/) |
| [10.1（Tag 04QJ）](https://kerodon.net/tag/04QJ) | Simplicial Objects of ∞-Categories | [`Kerodon/ExactnessAndAnimation/SimplicialObjectsOfInfinityCategories/`](Kerodon/ExactnessAndAnimation/SimplicialObjectsOfInfinityCategories/) |

KL-W1 時点の改名は [モジュール対応表](../../scripts/refactor/targets/kl-module-map.json) と
[宣言対応表](../../scripts/refactor/targets/kl-namespace-map.json) を参照。
並行する枝の追従手順は [KL-W1 の報告](../../formalization-plans/stage-ii/bulk/kerodon-layout-w1-report.md) にある。

今回の Project・BhattScholze の整理に追従する枝は、[B3 後の B4 資料](../../evidence/bulk/bulk-w1-b3/B4-README.md) にある新しいモジュール表・所有元付きの実名表と、各枝の対象ファイル一覧を使う。移動前の環境で参照を採取してから main を取り込む。

## Project の主題分けと文献の属性

`Project/DerivedCategories/` の大きな群は、`MappingAndStability/`、`Gluing/`、`KanModels/`、`Verdier/`、`LocalizationAndRoofs/`、`CompactnessAndPresentability/`、`Tensor/` に分ける。既存の `PiCriterion/`、`KappaCovers/` なども保持する。strict 図式と D(A) の比較を追加する場所は `Project/DerivedCategories/DiagramComparison/` とする。他の Project ディレクトリも、錐・slice・Kan 置換などの主題ごとに分ける。ディレクトリだけを分ける移動では、公開の数学的な名前空間を保つ。

HTT・HA の節が主題のファイルは `HTT/`・`HA/` に置く。複数の文献による引用があっても、同じ構成を複製しない。Kerodon と Stacks はそれぞれ既存の `@[kerodon TAG]`・`@[stacks TAG]` を使う。ほかの文献は `@[cite KEY "番号"]`、部分対応は理由を伴う `partial := special`・`direction`・`stronger-hyp`・`component` で記す。照会は `#cite_tags KEY`、型も見るときは `#cite_tags! KEY`。略号と版の正本は [bibliography.json](../../research/bibliography.json)、構文は [Citation.lean](../Util/Citation.lean) を参照する。

## 層・入口・監査

開発レーンごとの入口と監査を下表に示す。依存の層はファイルごとに決める。入口の import と監査の `#check` を目次として使う。
入口は層全体の一括 import を保証するものではなく、監査欄も代表例である。
数学上の作業状況は
[基盤計画](../../formalization-plans/archive/stage-i/infinity-lanes/foundations.md) と
[進捗](../../formalization-plans/archive/stage-i/infinity-lanes/foundations-progress.md) が正本。

| 開発レーン | 内容 | 入口 | 監査（scripts/） |
| --- | --- | --- | --- |
| Simplicial | 単体的集合の組合せ論、境界・prism・necklace・cube・fat realization の部品 | [BoundaryGluing](Kerodon/TheLanguageOfInfinityCategories/SimplicialSets/BoundaryGluing.lean)、[CubeJoinNormalForm](Project/SimplicialCombinatorics/Cubes/CubeJoinNormalForm.lean)（`Project.Entrypoints.Simplicial` は集約入口） | audit_homotopical_general_tools.lean、audit_kst_s_construction.lean |
| PinchedHom | 右 pinched 写像空間 | [PinchedHom/Basic.lean](Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/Basic.lean) | audit_infinity_core.lean |
| Core | join・slice、終対象、極限、同値、写像空間、fibration の基礎 | [Core.lean](Project/Entrypoints/Core.lean) | audit_infinity_core.lean |
| Kan | Core を使う空間の理論：Kan 充填、ホモトピー、置換、基本亜群と整合性の道具 | [Kan.lean](Project/Entrypoints/Kan.lean)、[LastHornContraction](Kerodon/KanComplexes/HomotopyGroups/LastHornContraction.lean) | audit_infinity_kan.lean、audit_kst_comparison.lean |
| Kan/Pointed | 基点付き空間、区間・ループ・懸垂の道具 | [PointedIntervalAnodyne](Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanPointedPointedIntervalAnodyne.lean) | audit_infinity_kan.lean、audit_kst_spectra.lean |
| Coherent | coherent nerve の quasicategory 性（γ1） | [Coherent.lean](Kerodon/ExamplesOfInfinityCategories/SimplicialCategories/Coherent.lean) | audit_coherent_nerve.lean |
| F1 | cocartesian fibration、straightening、Yoneda・前層、Ind・compact・冪等完備化、FilteredExchange | [F1.lean](Project/Entrypoints/F1.lean)、[fibration の基本](Project/Entrypoints/F1Fibrations.lean) | audit_infinity_f1.lean |
| F1/Cocartesian | 休止中の Cat∞ 値 straightening（独立入口） | [F1/Cocartesian.lean](Project/Entrypoints/Cocartesian.lean) | audit_infinity_f1.lean、audit_infinity_f1_f1b.lean |
| F1B | Kan 拡張、随伴、cofinality、局所化（straightening に依存しない基盤） | [F1B.lean](Project/Entrypoints/F1B.lean)、[役割別の地図](F1B/README.md) | audit_infinity_f1b.lean、audit_infinity_f1_f1b.lean |
| HomotopyLimits | ホモトピー極限・Quillen 随伴の ∞ 圏比較（γ3・γ4） | [HomotopyLimits.lean](Project/Entrypoints/HomotopyLimits.lean) | audit_homotopy_limits.lean |
| Stable | 安定 ∞ 圏、cofiber、三角構造、完全関手 | [Stable.lean](Project/Entrypoints/Stable.lean) | audit_infinity_stable.lean |
| F2 | Cat∞、sifted・PΣ、accessible・presentable、空間とのテンソルと集合値重み | [F2.lean](Project/Entrypoints/F2.lean) | audit_infinity_f2.lean |
| Presentable | accessible・presentable、局所化 | [F2/Presentable.lean](Project/Entrypoints/Presentable.lean) | audit_infinity_presentable.lean |
| StablePresentable | 安定性と F2 の構成を併用する、完全関手・cofiber・矢圏の構造 | [StablePresentable.lean](Project/Entrypoints/StablePresentable.lean) | audit_infinity_stable_presentable.lean |
| ModelBridge | モデル圏との比較：Quillen 随伴、置換、frame、Reedy・bisimplicial、入力境界 | [ModelBridge.lean](Project/Entrypoints/ModelBridge.lean)、[Inputs](Project/ModelCategoryComparison/Inputs/) | audit_infinity_model_bridge.lean、audit_homotopy_limits.lean |
| DGNerve | dg nerve、線形写像空間、h と H⁰ の比較 | [DGNerve.lean](Project/Entrypoints/DGNerve.lean) | audit_dg_nerve.lean |
| DoldKanComparison | coherent nerve と dg nerve の比較（γ1.5） | [DoldKanComparison.lean](Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/DoldKanComparison.lean) | audit_dold_kan_comparison.lean |
| Derived | D(S)・Perf(S)、Verdier 商、dg 加群・Morita、gluing | [Derived.lean](Project/Entrypoints/Derived.lean) | audit_derived_infinity.lean |

### 5 層の依存規則

層はファイルごとに決める。依存は原則として同じ層か下の層へ向かう。ディレクトリは典拠を、層は依存の制約を表す。

| 層（下から） | 役割と制約 |
| --- | --- |
| `SharedFoundation` | 共有の土台。実装境界への推移的な依存を持たない。 |
| `Portable` | 可搬な構成。実装境界への推移的な依存を持たない。 |
| `Comparison` | モデル圏・DG・スペクトルなどとの比較。許す実装依存と理由を辺ごとに登録する。 |
| `Entrypoints` | 集約入口、監査用の集約、外部利用がある旧名の互換モジュール。 |
| `Consumers` | KST・BS など、構成と比較を利用する側。 |

Kerodon の節番号に逆向きの import は、依存先の宣言を直接使う場合や公開 API の経路を維持する場合に個別登録する。代替の公開経路があり直接参照がない辺は外した。[層の設定](../../scripts/refactor/layers.json)、[逆向き import と実装境界の付表](../../formalization-plans/stage-ii/bulk/kerodon-layout-w1-stage3-reverse-imports.md)

静的な検査はリポジトリ直下で行う。

```sh
python3 scripts/refactor/layer_check.py --enforce KLW1 --root "$PWD"
```
Derived の利用者のない試作4本は Archive の [Diagnostics](../Archive/InfinityCategories/DGKappaDiagnostics/README.md) に区別する。

監査はリポジトリ直下で `lake env lean scripts/<監査名>`、対象のビルドは
`lake build SerrePositivity.InfinityCategories.<入口名>` で行う。
主経路は quasicategory の仮定で進める。モデル圏の仮定を使う比較は `Project/ModelCategoryComparison/` に置く。
公理監査は標準の `propext`・`Classical.choice`・`Quot.sound` のみを許す。

Core の基本入口は [Fibrations.lean](Project/Entrypoints/CoreFibrations.lean) と
[MappingSpace.lean](Project/Entrypoints/MappingSpace.lean)。辺の cocartesian 性と相対外側ホーンは
[F1/Fibrations.lean](Project/Entrypoints/F1Fibrations.lean) にまとめる。

Cat∞ 値 straightening は F1 主入口から直接は読み込まない。
`lake build SerrePositivity.InfinityCategories.Project.Entrypoints.Cocartesian` で独立に検証する。
主経路が必要とする汎用補助は引き続き推移的に読み込まれる。F1 公理監査は
主入口と独立入口の両方を import し、休止中の宣言も検査する。

## 集合値重みのテンソル比較（G8）

正本は [SetSectionsNaturality.lean](Project/SetWeightedTensors/SetSectionsNaturality.lean) の
`SetWeight.tensorSpaceFunctor_setWeightHomNatural`。その比較に使う
`elementsComparisonNatural`・`sectionsEquivalenceNatural` も同じファイルにある。
旧 `tensorSpaceFunctor_setWeightHom` と旧比較 4 宣言は deprecated として保持する。
旧名と Natural 版は同じ定義ではなく、旧版の型・本体を新しい選択へ書き換えない。
一般の重みの射に関する自然性の四角形は、この指定だけで証明済みとはしない。
BS の S4・S8 は Natural 版を使う（[BS の確認記録](../../formalization-plans/bhatt-scholze/reports/report-codex-s4-sieve.md)）。

## 読み順と規約

[日本語解説の全体地図](../../exposition/ja/infinity/00-map.html) から、Core、F1・F1B、
γ 層、F2、Stable、dg nerve・Derived の順に読む。
[dg nerve の規約と計算](DGNerve/README.md) は移動前の符号・次数・N0 の計算を保存している。
微分は cochain 次数 +1、合成は通常順。HA と Kerodon の符号を比べる際はこの規約を参照する。

[リファクタリング計画](../../formalization-plans/archive/stage-i/refactoring-infinity.md) に従い、
移動した旧モジュールを削除し、下流の import と公開名を直接置換する。必要な補題が禁止 import 閉包にある場合は、
コピーせずコーディネータ経由で上流の分割を依頼する。
重複候補は `python3 scripts/check_duplicates.py --baseline
formalization-plans/archive/refactor-duplicates-2026-10-23.md` で比較できる。

## 旧 KST 名の経緯（F-2）

KST から移した宣言は現在のディレクトリに対応する名前空間を使う。
従来の F1・F1B・F2 は開発レーン名として使う。旧 KST 名は deprecated alias として
段 G の最初の区切りまで保持し、BS・G2・KST の移行確認後、別の束で一括削除する。
対応と alias の種類は [確定改名表](../../scripts/refactor/targets/f-namespace-map.json) を参照。
instance・simp の登録は新名側のみで、旧名側の型・暗黙引数・宇宙を保つ。
