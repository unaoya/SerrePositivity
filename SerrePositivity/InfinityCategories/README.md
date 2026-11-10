# ∞ 圏基盤の地図

quasicategory 模型を使う。∞ 圏は `X : SSet` と `[Quasicategory X]`、
関手は単体的集合の射、関手 ∞ 圏は `(ihom X).obj Y` で表す。
極限は slice の終対象、写像空間は右 pinched Hom として定義する。

## Kerodon・HTT に沿った配置

移動済みの主な内容は次の節にある。宣言の属性 `@[kerodon TAG]` は
[Lean で照合した一覧](../../research/kerodon-coverage/kerodon-tags-lean.txt) から引ける。

| 節 | 内容 | 入口 |
| --- | --- | --- |
| Kerodon 2.5 | Alexander–Whitney・shuffle・Eilenberg–Zilber | [NormalizedEZHomotopy](Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/NormalizedEZHomotopy.lean) |
| Kerodon 3.3 | Ex∞ と Kan 性 | [ExInfinityKan](Kerodon/KanComplexes/TheExInfinityFunctor/ExInfinityKan.lean) |
| Kerodon 4.2・4.7 | 最初の頂点の包含と、始対象の頂点が張る可縮な部分複体 | [FirstVertexLeftAnodyne](Kerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/FirstVertexLeftAnodyne.lean)、[InitialVerticesContractible](Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/InitialVerticesContractible.lean) |
| Kerodon 6.3 | 局所化の存在 | [GeneralLocalization](Kerodon/AdjointFunctors/Localization/GeneralLocalization.lean) |
| Kerodon 7.1 | 関手圏の各点ごとの余極限と同値による余極限錐の保存・反映 | [FunctorPointwiseColimitExistence](Kerodon/LimitsAndColimits/LimitsAndColimits/FunctorPointwiseColimitExistence.lean)、[EquivalenceColimitCones](Kerodon/LimitsAndColimits/LimitsAndColimits/EquivalenceColimitCones.lean) |
| Kerodon 8.5 | 頂点の retract | [VertexRetractions](Kerodon/TheYonedaEmbedding/RetractsAndIdempotents/VertexRetractions.lean) |
| Kerodon 9.4 | accessible 関手 | [AccessibleFunctor](Kerodon/LargeInfinityCategories/CompactGenerationAndAccessibility/AccessibleFunctor.lean) |
| HTT 1.2.12・2.1.2 | 相対始対象の輸送 | [InitialBoundaryTransport](HTT/InitialAndFinalObjects/InitialBoundaryTransport.lean) |
| HTT 5.1.4・5.4.2・5.5 | retract 閉包、accessibility の輸送、presentable 性と実単位 | [RetractClosure](HTT/RetractsAndIdempotentCompletion/RetractClosure.lean)、[EquivalenceColimits](HTT/AccessibleInfinityCategories/EquivalenceColimits.lean)、[Definition](HTT/PresentableInfinityCategories/Definition.lean)、[RightUnitContractible](HTT/PresentableInfinityCategories/RightUnitContractible.lean) |

改名は [モジュール対応表](../../scripts/refactor/targets/kl-module-map.json) と
[宣言対応表](../../scripts/refactor/targets/kl-namespace-map.json) を参照。
並行する枝の追従手順は [KL-W1 の報告](../../formalization-plans/stage-ii/kerodon-layout-w1-report.md) にある。

## 層・入口・監査

従来の開発レーンごとの入口と監査を下表に示す。入口の import と監査の `#check` を目次として使う。
入口は層全体の一括 import を保証するものではなく、監査欄も代表例である。
数学上の作業状況は
[基盤計画](../../formalization-plans/infinity-lanes/foundations.md) と
[進捗](../../formalization-plans/infinity-lanes/foundations-progress.md) が正本。

| 層 | 内容 | 入口 | 監査（scripts/） |
| --- | --- | --- | --- |
| Simplicial | 単体的集合の組合せ論、境界・prism・necklace・cube・fat realization の部品 | [BoundaryGluing](Simplicial/BoundaryGluing.lean)、[CubeJoinNormalForm](Simplicial/CubeJoinNormalForm.lean)（`Simplicial.lean` は骨組み） | audit_homotopical_general_tools.lean、audit_kst_s_construction.lean |
| PinchedHom | 右 pinched 写像空間 | [PinchedHom/Basic.lean](PinchedHom/Basic.lean) | audit_infinity_core.lean |
| Core | join・slice、終対象、極限、同値、写像空間、fibration の基礎 | [Core.lean](Project/Entrypoints/Core.lean) | audit_infinity_core.lean |
| Kan | Core を使う空間の理論：Kan 充填、ホモトピー、置換、基本亜群と整合性の道具 | [Kan.lean](Project/Entrypoints/Kan.lean)、[LastHornContraction](Kan/LastHornContraction.lean) | audit_infinity_kan.lean、audit_kst_comparison.lean |
| Kan/Pointed | 基点付き空間、区間・ループ・懸垂の道具 | [PointedIntervalAnodyne](Kan/Pointed/PointedIntervalAnodyne.lean) | audit_infinity_kan.lean、audit_kst_spectra.lean |
| Coherent | coherent nerve の quasicategory 性（γ1） | [Coherent.lean](Coherent.lean) | audit_coherent_nerve.lean |
| F1 | cocartesian fibration、straightening、Yoneda・前層、Ind・compact・冪等完備化、FilteredExchange | [F1.lean](Project/Entrypoints/F1.lean)、[fibration の基本](Project/Entrypoints/F1Fibrations.lean) | audit_infinity_f1.lean |
| F1/Cocartesian | 休止中の Cat∞ 値 straightening（独立入口） | [F1/Cocartesian.lean](Project/Entrypoints/Cocartesian.lean) | audit_infinity_f1.lean、audit_infinity_f1_f1b.lean |
| F1B | Kan 拡張、随伴、cofinality、局所化（straightening に依存しない基盤） | [F1B.lean](Project/Entrypoints/F1B.lean)、[役割別の地図](F1B/README.md) | audit_infinity_f1b.lean、audit_infinity_f1_f1b.lean |
| HomotopyLimits | ホモトピー極限・Quillen 随伴の ∞ 圏比較（γ3・γ4） | [HomotopyLimits.lean](Project/Entrypoints/HomotopyLimits.lean) | audit_homotopy_limits.lean |
| Stable | 安定 ∞ 圏、cofiber、三角構造、完全関手 | [Stable.lean](Project/Entrypoints/Stable.lean) | audit_infinity_stable.lean |
| F2 | Cat∞、sifted・PΣ、accessible・presentable、空間とのテンソルと集合値重み | [F2.lean](Project/Entrypoints/F2.lean) | audit_infinity_f2.lean |
| Presentable | accessible・presentable、局所化 | [F2/Presentable.lean](Project/Entrypoints/Presentable.lean) | audit_infinity_presentable.lean |
| StablePresentable | 安定性と F2 の構成を併用する、完全関手・cofiber・矢圏の構造 | [StablePresentable.lean](Project/Entrypoints/StablePresentable.lean) | audit_infinity_stable_presentable.lean |
| ModelBridge | モデル圏との比較：Quillen 随伴、置換、frame、Reedy・bisimplicial、入力境界 | [ModelBridge.lean](Project/Entrypoints/ModelBridge.lean)、[Inputs](ModelBridge/Inputs/) | audit_infinity_model_bridge.lean、audit_homotopy_limits.lean |
| DGNerve | dg nerve、線形写像空間、h と H⁰ の比較 | [DGNerve.lean](DGNerve.lean) | audit_dg_nerve.lean |
| DoldKanComparison | coherent nerve と dg nerve の比較（γ1.5） | [DoldKanComparison.lean](DoldKanComparison.lean) | audit_dold_kan_comparison.lean |
| Derived | D(S)・Perf(S)、Verdier 商、dg 加群・Morita、gluing | [Derived.lean](Project/Entrypoints/Derived.lean) | audit_derived_infinity.lean |

中核の層順序は Simplicial → Core → Kan → Coherent →
{F1, F1B, HomotopyLimits} → Stable → F2 → StablePresentable。
モデル圏との接続はその上の ModelBridge、dg 側の応用は DGNerve・
DoldKanComparison・Derived に置く。F1B の入口は straightening に依存せず、
straightening を使う一般補題は F1 に置く。
[層の判断表](../../formalization-plans/infinity-foundation-plan.md) と
[層検査設定](../../scripts/refactor/layers.json) が配置の基準である。
Derived の利用者のない試作入口は [Diagnostics](Derived/Diagnostics/README.md) に区別する。

監査はリポジトリ直下で `lake env lean scripts/<監査名>`、対象のビルドは
`lake build SerrePositivity.InfinityCategories.<入口名>` で行う。
主経路では `ModelCategory SSet` の instance 仮定を置かない。
公理監査は標準の `propext`・`Classical.choice`・`Quot.sound` のみを許す。

Core の基本入口は [Fibrations.lean](Project/Entrypoints/CoreFibrations.lean) と
[MappingSpace.lean](Project/Entrypoints/MappingSpace.lean)。辺の cocartesian 性と相対外側ホーンは
[F1/Fibrations.lean](Project/Entrypoints/F1Fibrations.lean) にまとめる。

Cat∞ 値 straightening は F1 主入口から直接は読み込まない。
`lake build SerrePositivity.InfinityCategories.Project.Entrypoints.Cocartesian` で独立に検証する。
主経路が必要とする汎用補助は引き続き推移的に読み込まれる。F1 公理監査は
主入口と独立入口の両方を import し、休止中の宣言も検査する。

## 集合値重みのテンソル比較（G8）

正本は [SetSectionsNaturality.lean](F2/Tensor/SetSectionsNaturality.lean) の
`SetWeight.tensorSpaceFunctor_setWeightHomNatural`。その比較に使う
`elementsComparisonNatural`・`sectionsEquivalenceNatural` も同じファイルにある。
旧 `tensorSpaceFunctor_setWeightHom` と旧比較 4 宣言は deprecated として保持する。
旧名と Natural 版は同じ定義ではなく、旧版の型・本体を新しい選択へ書き換えない。
一般の重みの射に関する自然性の四角形は、この指定だけで証明済みとはしない。
BS の S4・S8 は Natural 版を使う（[BS の確認記録](../../formalization-plans/bhatt-scholze/report-codex-s4-sieve.md)）。

## 読み順と規約

[日本語解説の全体地図](../../exposition/ja/infinity/00-map.html) から、Core、F1・F1B、
γ 層、F2、Stable、dg nerve・Derived の順に読む。
[dg nerve の規約と計算](DGNerve/README.md) は移動前の符号・次数・N0 の計算を保存している。
微分は cochain 次数 +1、合成は通常順。HA と Kerodon の符号を比べる際はこの規約を参照する。

[リファクタリング計画](../../formalization-plans/refactoring-infinity.md) に従い、
移動した旧モジュールを削除し、下流の import と公開名を直接置換する。必要な補題が禁止 import 閉包にある場合は、
コピーせずコーディネータ経由で上流の分割を依頼する。
重複候補は `python3 scripts/check_duplicates.py --baseline
formalization-plans/archive/refactor-duplicates-2026-10-23.md` で比較できる。

## 移動した宣言の名前空間（F-2）

KST から移した宣言は現在のディレクトリに対応する名前空間を使う。
F1・F1B・F2 のディレクトリ名は維持する。旧 KST 名は deprecated alias として
段 G の最初の区切りまで保持し、BS・G2・KST の移行確認後、別の束で一括削除する。
対応と alias の種類は [確定改名表](../../scripts/refactor/targets/f-namespace-map.json) を参照。
instance・simp の登録は新名側のみで、旧名側の型・暗黙引数・宇宙を保つ。
