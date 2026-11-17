# R レーン：∞ 圏基盤のリファクタリング（2026-10-23 新設）

解説 [exposition/ja/infinity/](../../../exposition/ja/infinity/index.html)（第 0〜8 章、R8 重複調査）が挙げた候補 R1〜R25 を、
全レーン停止窓で実施した。R-C・R-B の再適用後、R-A 最終ラウンドも main で検証を完了した。正本はこのファイル。実施記録はコミットメッセージ。候補の番号は解説の番号をそのまま使う。

## 0. リファクタ文書の索引（R1〜R79、2026-10-28 整理、10-30 更新）

> **11-12 追記**：状態の正本は [refactor-ledger.md](../../refactor-ledger.md)。この §0 の状態欄とパスは 10-30 のまま（KL-W1 の前の構成）。


∞ 圏まわりのリファクタは、このファイルを入口とする。番号は全文書で通し番号。BS 側は [bhatt-scholze-refactoring.md](../../bhatt-scholze/notes/bhatt-scholze-refactoring.md)（別セッション）。

| 範囲 | 文書 | 状態 |
| --- | --- | --- |
| R1〜R25 | 本ファイル §4（段の表）・§5（旧所在→新所在の対応表）・§8（分担） | 第 1 窓で実施済み（10-23〜24）。下表の「先送り」を除く |
| R-C の再適用 | [refactoring-infinity-r-c.md](../refactoring-infinity-r-c.md) | 完了（10-24） |
| R26〜R47 | [refactoring-infinity-r2.md](refactoring-infinity-r2.md)（候補 §3）、R2-B の処置案 [refactoring-infinity-r2-b.md](refactoring-infinity-r2-b.md) | 調査済み。実施の窓は整備計画 §5〜§6（R26・R37〜R40 は W1〜W2b、R28〜R30・R44・R46・R47 は範囲外） |
| R48〜R57 | [refactoring-verdier.md](refactoring-verdier.md)（Verdier 商の一般構成に向けた配置換え） | R48・R49a・R50・R53 は W1 の対象一覧（承認 10-30）。R56a・R52・R51・R68 は W2a〜W2c |
| R59〜R67 | [refactoring-infinity-r2.md](refactoring-infinity-r2.md) §3 末尾（入口の修正、台帳、重複、Kan・pointed 層、DK 局所化層、∞ 中核の dg 非依存化、分類し直し。10-28 の調査から） | 候補 |
| R68〜R79 と全体の順序 | [infinity-foundation-plan.md](infinity-foundation-plan.md)（∞ 基盤の整備計画の正本。段 A〜G、窓 W0〜W2c、決定事項、目標構成） | W0 進行中（IF-W0-1・2 完了、IF-W0-3 で W1 の対象一覧を承認 10-30、w2a 以降は作成中） |
| （別計画） | [refactor-plan.md](../../refactor-plan.md)（論文の層の整理・一般論の切り出し・Mathlib への提出。旧 paper-layer-extraction.md を統合） | 計画（10-30） |
| R58 | 解説 [route-yoneda.html](../../../research/infinity-refactor-audit/route-yoneda.html) §6（旧番号 R26。R2 の R26 と衝突したため 10-28 に改番） | R27・R37 に統合して扱う |
| 調査記録 | archive の `refactor-*-2026-10-23/24.*`（第 1 窓の検証・名前対応）、`r2-*-2026-10-27.*`（R2 の各調査）、[infinity-outside-survey-2026-10-28.md](../infinity-outside-survey-2026-10-28.md)（∞ 層の外にある一般論）、[repository-survey-2026-10-28.md](../repository-survey-2026-10-28.md)（SerrePositivity/ 全体の地図と問題点） | — |
| 候補の出所 | 解説の赤い囲み（11-12 に台帳へ移した、原文は `research/infinity-refactor-audit/box-texts.md`）、[r8-duplication.html](../../../research/infinity-refactor-audit/r8-duplication.html) | — |

### 0.1 ∞ 基盤の整備（2026-10-28 以降の正本）

段 A〜G の順序、決定事項（局所化と Verdier の所有の移管、Kan 層、改名の先送り）、目標とする構成、完了条件は
[infinity-foundation-plan.md](infinity-foundation-plan.md) に一本化した。この節は索引だけを持つ。

R1〜R25 の内訳：

| 状態 | 番号 |
| --- | --- |
| 実施済み | R1・R2・R3・R5 前半・R6・R7・R8・R9・R11・R12・R13・R14・R15・R16・R17・R18（F1/F1B と HomotopyLimits）・R19・R22・R23・R24・R25 |
| 継続中の保守 | R20（仮定入力の一覧、§6） |
| 先送り（第 I 段終了時） | R4（ファイル粒度）・R5 後半（双対化）・R10（計算規則の統合）・R21（docstring、各レーンが工程完了時に行う） |

## 引き継ぎ

### 現在地

- R-A 最終ラウンド完了（2026-10-24 17:55 JST）、実装コミット `3503018076d1036f5388065107b828a9cfe039b5`。R11 600本、R12 1714本に続き、R13 の F1B 766本を役割別に移動。
- PinchedInterval 26宣言・scaffold 19宣言を原本へ直接置換し、重複7モジュールを削除。共通部14宣言は元の名前・型・証明のまま4新設／2既存モジュールへ移した。
- F1B の kan/Kan 接頭辞を持つ宣言だけを改名。完全名対応842件には上記45重複の原本参照を含む。互換シムはない。
- `scripts/refactor/verify.sh`：全体ビルド・全監査対象ビルド・24監査・sorry閉包を通過（独立sorry再検証を含め 1669.26 秒、事前の全監査対象ビルド3097.49秒後のルート再確認 16.36 秒）。
- 補完36監査は35合格、BS 1本は範囲外の既存不具合（918.72 秒）。ユーザー指示によりverify.shの24監査全緑を合格条件とする。直接sorryと新規重複対は0。
- 詳細・対応・実測値は [最終検証記録](../refactor-ra-final-validation-2026-10-24.json) と §5。R-C・R-B の main 再適用も完了済み。

### 残り

- R の今回の担当は完了し停止する。取り込み確認・タグ・各レーン再開はコーディネータとユーザーが行う。
- 型の異なる準重複、docstring・粒度・双対化・計算規則の再設計は第 I 段終了時。Derived の型依存データ19組は既存の承認どおり D 再開後判断。

### 主要宣言・依存と提供

- 正本：`Core/SubcomplexInverseImageComparison`、`F1/Diagrams/ScaffoldFiberMaps`、`F1/Scaffold/FinitePrism`・`FiniteFiberGeometry`。
- F1B の入口は `F1B.lean`。新分類は Adjunction・Cofinality・Diagrams・FunctorCategories・Homotopy・Fibrations・MappingSpaces・KanExtension・NerveComparison・CocartesianScaffold・Cones・KanComplex・Joins・Equivalences・Localization。
- 旧所在・旧名からの全対応は §5 の保存 JSON が正本。不要な straightening 閉包を追加せず、F1B 禁止閉包監査を保持した。

### 未コミット・既知の問題

- 既存未追跡 `HomotopyLimits/PresheafElementsLeftKan.lean` の機械的参照更新は [差分](../refactor-ra-final-untracked-references-2026-10-24.patch) に保存し、元の数学本文は R のコミットから除外。
- 他レーンの既存未コミット文書・PDF・未追跡本文は保持した。範囲外のBS監査838行の型不一致は[BS計画](bhatt-scholze/bhatt-scholze-refactoring.md)の既知問題。第II段再開時にBSが修正し、Rは当該監査を変更しない。

### 次の一手

- R は停止。再開する各レーンは新しい分類と §5 の対応表を読み、仮定入力は §6 の供給元へ依頼する。

## 1. 目的と範囲

- 目的：(a) 複製されたコードの除去、(b) 一般論を正しい層（Core・F1B）へ移す、(c) 逆向き依存（基盤 → KST、DGNerve ↔ Derived）の解消、
  (d) 入口と README を読める形にする。数学的内容・宣言の型・証明は変えない。
- 範囲外：証明の書き直し（R5 の双対化、R10 の計算規則の統合）、docstring の書き直し（R21、各レーンが工程完了時に行う）、
  ファイル粒度の変更（R4）。これらは第 I 段の終了時に改めて計画する。

## 2. 不変条件と実施方針（2026-10-23、全レーン停止方式へ変更）

1. 数学的内容・宣言の型・残す原本の証明を変えない。重複側は削除し、参照を原本へ直接向ける。
   宣言・モジュールの改名は許す。最終ラウンドの宣言改名は F1B の kan/Kan 接頭辞に限定する。互換シムは残さず、下流の import と `KanSection.foo` 等も同じ段階で置換する。
2. 一般論の import 閉包に straightening 等の不要な依存を追加しない。F1B の禁止閉包監査を保つ。
   型・instance の解決に必要な import は明示し、以前の暗黙の依存をビルド・監査で確認する。
3. `sorry`・新規公理・引用・`ModelCategory SSet` 等の instance 仮定を導入しない。
   公理監査は標準三公理だけ。既存監査の検査対象や検査条件を弱めない。
4. 各段階の終わりに対象ビルド、該当監査、`scripts/check_duplicates.py` を実行し、結果と所要時間を記録・報告する。
   R13の合格条件はユーザー指示によりverify.shの24監査全緑（追加36本は35合格・BS既存不具合1本を範囲外として記録）。R12・R13 はユーザー指示により R-A が `scripts/refactor/verify.sh` で全体ビルド・全監査・sorry 閉包も通す。タグはコーディネータ。
5. 全レーン停止と基準タグは受領済み。初回バッチは main に取り込み済み。以後 R-A だけが main で直接作業する。
   R-B・R-C の再適用は完了済み。R-A 最終ラウンドの検証・コミット後は書き込みを停止し、タグと各レーン再開はコーディネータが行う。
6. 所有範囲と他レーンへの書き込み条件は §8 を正本とする。今後の他レーン変更は (a)(b) に限定する。

## 3. 停止・main への移行・再開（2026-10-23 R-A 分担へ更新）

- 基準：`stage1-checkpoint-2026-10-23`（`f8df7f77b`）。分担の正本：`c6692be81` の §8。
- R-A は main の自分の変更だけを `set -o pipefail` のうえ `git commit --only` で保存する。
  R-B・R-C の worktree は取り込み前に `git rebase main` し、ff-merge はコーディネータが行う。
  他レーンの未コミット作業を巻き込んでコミット・破棄しない。
- R-A は main で直接作業し、互換シムは残さない。`scripts/move_module.py` を配置・コミット済みで、以後の機械的置換に使う。
- R-A の順序：第 0〜1 段＋第 5 段の F1/F1B 重複除去 → R5 前半・R6・R7・R9 の入口 → 第 4 段の R11・R12・R13。
  他レーンの範囲は §8 の (a) 新規ファイル追加、(b) ツールによる import・参照・集約の機械的更新だけ。
- R-C・R-B の再適用・全監査完了後、R-A が R13 最終ラウンドを main に適用し、全体検証まで完了した。
- 移動前に移動本数・更新ファイル数・他レーン範囲の更新一覧（レーン名・ファイル名・種類）を報告する。各段の検証結果と所要時間も報告する。
- 期限は **2026-10-25 夜**。終わらない項目は「第 I 段終了時」に戻す。R12・R13 の全体ビルドはユーザー指示により R-A が実施。タグはコーディネータ。

## 4. 段階

分担・実施条件は §8 を優先する。初回バッチの「R-A」は所管の対象検証を指す。R12・R13の最終検証はルート全体ビルド・全監査対象ビルド・verify.shの24監査・sorry閉包まで含む。

| 段 | 内容 | 候補 | 触るレーン | 条件 | 完了 |
|---|---|---|---|---|---|
| 0-1 | 正規化ハッシュによる重複検査 `scripts/check_duplicates.py`。現状の一覧を `archive/` に保存 | R8 再発防止 | なし | 即時 | 2026-10-23 09:35 JST |
| 0-2 | `InfinityCategories/README.md`（dg nerve の規約）を `DGNerve/README.md` へ移し、最上位 README を全体地図（層・入口・監査スクリプト）に | R25 | なし | 即時 | 2026-10-23 09:37 JST |
| 0-3 | `F2/JoinRightRelativeRetraction` を削除し、import と F2 公開名を F1 原本へ直接置換 | R8 段階 0 | F1b（10-20 以降未変更） | §3 | 2026-10-23 17:45 JST（直接置換・初回バッチ） |
| 0-4 | 仮定入力の一覧（§6）を grep で作り本計画に固定 | R17・R20 | なし | 即時 | 2026-10-23 09:40 JST |
| 1-1 | `F1/PullbackFiber`・`F1/LeftFiberKan` を汎用部（新 `Core/VertexFiberPullback`・`Core/LeftFiberKan`）と straightening 部（`LeftUnstraighteningFiberIso`・`LeftUnstraighteningFiberKan`、Core を import）に分割 | R8 段階 1 | F1（10-18 以降未変更） | §3 | 2026-10-23 17:45 JST（R-A） |
| 1-2 | 汎用部だけで足りる直接 importer（6 本）を Core 側へ向け直す。下流の import と名前を原本へ直接更新する（旧依存を保つための import は加えない） | R8 段階 2 | F1・F1B・HomotopyLimits・F2 | 1-1 の後、§3 | 2026-10-23 17:45 JST（R-A） |
| 1-3 | F1B の `KanSection*` 重複を削除し原本へ直接置換。現状の宣言数と差分を再検証し、独自内容だけを残す | R8 段階 3 | F1b（10-19 以降未変更） | 1-2 の後（F1B 監査が原本の閉包を通すため） | 2026-10-23 17:45 JST（R-A） |
| 1-4 | `Core/Fibrations.lean`・`Core/MappingSpace.lean` の入口（定義は動かさず import と docstring で目次化）、R6 は `F1/Fibrations.lean` | R6・R7・R9 | なし | 即時 | 2026-10-23 22:05 JST |
| 1-5 | `Stable/SliceOpposite` の `sliceOverOpIso` を `Core/SliceOpposite` へ移し、旧ファイルを削除・参照を直接更新 | R5 の前半 | D（10-18 以降未変更） | §3 | 2026-10-23 17:45 JST（Core・R-A 対象。Stable 集約は R-B） |
| 2-1 | `Stable/Cocone`・`UniverseLimits`・`ColimitDiagramIso`・`Definition` の `HasFiniteLimits` を `Core/Colimit*` へ（旧ファイルを削除して直接置換） | R2・R22 | D | D-7 d 完了直後 | R-B：main 適用済み、指定9集約・verify.sh 全24監査・sorry閉包通過（検証ソース `eec26ad27`） |
| 2-2 | `Stable/AdjunctionHomotopyCategory` を `F1B/AdjunctionHomotopyCategory` へ | R14 | D・F1b | 2-1 と同時 | R-B：main 適用済み、指定9集約・verify.sh 全24監査・sorry閉包通過（検証ソース `eec26ad27`） |
| 2-3 | `Derived/LimitDiagramIso` を Core、`CofinalLimitExistence` を F1B へ、`Localization*Criterion`・`DeformationLocalization` を F1B へ | R23 | D・F1b | D の区切り | R-B：main 適用済み、指定9集約・verify.sh 全24監査・sorry閉包通過（検証ソース `eec26ad27`） |
| 2-4 | `KST/SConstruction/VertexPrescribedExtension`・`KST/LocalizingInvariants/LimitProjectionExistence` の内容を Core へ移し KST の旧ファイルを削除して直接置換。Stable → KST の import を解消 | R3 | K-S•・Sp・D | 三レーンの区切り | R-B：main 適用済み、指定9集約・verify.sh 全24監査・sorry閉包通過（検証ソース `eec26ad27`） |
| 2-5 | `DGNerve/SemifreeLimits` を Derived（または DifferentialGraded）へ、DGNerve の旧ファイルを削除して直接置換 | R24 | D | D の区切り | R-B：main 適用済み、指定9集約・verify.sh 全24監査・sorry閉包通過（検証ソース `eec26ad27`） |
| 2-6 | `F2/Ind/ElementsDiagram` の密度定理を F1 の前層の層へ | R15 | F1 | F1-7 完了後 | R-C：d5cd974e2、密度59本・補助81本適用、verify.sh・関係監査通過 |
| 2-7 | `F2/SpaceLimitShapes` の条件付き版を無条件定理の系に（3 ファイル） | R17 | F1b | a7 完了・差し替えと同時 | R-C：bdf8d1c6a 適用、verify.sh・関係監査通過 |
| 2-8 | `HomotopyLimits/Local*`・`Sigma*`・`Sifted*` を `F2/Presentable/` へ | R16 | N・P | P-1 f・g 完了後 | R-C：ba39c0897、90本適用、verify.sh・関係監査通過 |
| 3-1 | その他の完全一致・準重複：`F2/JoinRight*`↔`F1/JoinDiagramRight*`、Stable↔KST 4 組、`Derived/DGCommaAug*`↔`DGModuleAugmentation*` 17 組、EInfinity 19 組、HomotopicalAlgebra 8 組 | R8 §3 | F1b・K-S•・D・E2 | 各レーンの区切り | R-B：4組・14宣言・Prop4本、R-C：完全一致3宣言・転送267本完了。型依存19組はD再開後、型の異なる他の準重複は第I段終了時。所管監査通過 |
| 3-2 | `PinchedInterval` 6 本・`KanScaffold`／`KanCocartesian` 15 本の精査 | R8 段階 4 | F1b | F1b-5 a7 完了後 | 2026-10-24 17:55 JST（PinchedInterval26・scaffold19、verify.sh合格） |
| 4-1 | 休止中の Cat∞ 値 straightening `F1/Cocartesian*`（3.7 万行）を `F1/Cocartesian/` へ移し集約から外す | R11 | F1 | R-A、直接置換・入口の検証後 | 2026-10-23 22:41 JST |
| 4-2 | F2 最上位を `F2/CatInfinity/`（完成）と `F2/FilteredExchange/`（作業中）へ | R19 | F1b | a7 完了後 | R-C：65c0881c8、2,210本適用、verify.sh・関係監査通過 |
| 4-3 | F1 のサブディレクトリ化、F1B の `Kan*` 接頭辞の整理、ディレクトリ名の層への対応 | R12・R13・R1・R6 | F1・F1b | R-A、R11 の後 | R12：2026-10-24 06:49 JST。R13：2026-10-24 17:55 JST（verify.sh合格） |
| 5 | 旧重複モジュールの削除と `KanSection.foo` → `foo` の直接置換（約 60 箇所）、`HomotopyLimits.lean` の docstring と `quillenCfBottomEndpoint_wrong` 等の改名 | R18 ほか | 全レーン | 第 0〜1 段と同時（全停止後） | 2026-10-23 17:45 JST（F1/F1B 部分。HomotopyLimits は R-C） |

## 5. 移動した宣言の所在

| 旧所在（削除・改名） | 新所在 | 段 | コミット |
|---|---|---|---|
| F1/PullbackFiber・LeftFiberKan の汎用部 | Core/VertexFiberPullback・LeftFiberKan | 1-1 | 6e3cbbcba（初回、2026-10-23 17:45 JST） |
| F1/ScaffoldFiniteVerticalEdges の prism・LeftStrictTransport の under map | Core/PrismVerticalSimplex・NerveUnderMap | 1-3 | 同上 |
| F1/PullbackNerveFiber・ScaffoldUnderChain | Core/VertexFiberNervePullback・F1B/ScaffoldUnderChain | 1-3 | 同上 |
| F1B/KanSection 重複群・F2/JoinRightRelativeRetraction | F1 原本または新 Core（[全対応一覧](../refactor-direct-batch-2026-10-23.json)） | 0-3・1-3・5 | 同上 |
| Stable/SliceOpposite と join/reverse 汎用補助 16 本 | Core の同名モジュール | 1-5 | 同上 |

R-C の main 再適用（2026-10-24、verify.sh・関係監査通過）：

| 旧所在 | 新所在 | 項目 | コミット |
|---|---|---|---|
| F2 最上位の2,210本 | F2/CatInfinity・FilteredExchange（[計画](../r-c-main-2026-10-24/r19.json)） | R19 | 65c0881c8 |
| HomotopyLimits の Local*・Sigma*・Sifted* 90本 | F2/Presentable（[計画](../r-c-main-2026-10-24/r16.json)） | R16 | ba39c0897 |
| F2/Ind の前層密度59本・F2 の一般補助81本 | F1/Yoneda/PresheafDensity と Support（[計画](../r-c-main-2026-10-24/r15.json)） | R15 | d5cd974e2 |
| EInfinity の完全一致3宣言・bar の output | HomotopyWeight/DoubleOpposite・BarOutput（型と本文を保存） | R8 完全一致部 | a6a10c52b |
| HomotopicalAlgebra/HomotopyFunctionComplex の267転送入口 | Rectification へ直接 import（[計画](../r-c-main-2026-10-24/redirect-267.json)、[閉包証拠](../r-c-main-2026-10-24/redirect-267-closure.json)） | 追加項目 | d2385ea7e |

型の異なる準重複の実施は所有レーン再開後の判断。HomotopicalAlgebra は現存6組の全調査として確定。[一覧](../refactor-near-duplicates-einfinity-2026-10-23.md)を参照。UniverseSSetMaps と Stable 補助6本の移動は R-B に残した。

### R-B main 再適用（2026-10-24）

宣言の型・本文を保持し、互換シムは残さない。部分抽出29宣言は元の固有内容を残す。F1 の2宣言は namespace を保持し、元ファイルの public import から instance も公開する。

| 旧モジュール | 新モジュール | 項目 |
|---|---|---|
| `SerrePositivity.InfinityCategories.DGNerve.SemifreeLimits` | `SerrePositivity.InfinityCategories.Derived.SemifreeLimits` | R-B |
| `SerrePositivity.InfinityCategories.Stable.Cocone` | `SerrePositivity.InfinityCategories.Core.Cocone` | R-B |
| `SerrePositivity.InfinityCategories.Stable.BoundaryOpposite` | `SerrePositivity.InfinityCategories.Core.BoundaryOpposite` | R-B |
| `SerrePositivity.InfinityCategories.Stable.ConeOpposite` | `SerrePositivity.InfinityCategories.Core.ConeOpposite` | R-B |
| `SerrePositivity.InfinityCategories.Stable.CosliceRestrictionEquivalence` | `SerrePositivity.InfinityCategories.Core.CosliceRestrictionEquivalence` | R-B |
| `SerrePositivity.InfinityCategories.Stable.ColimitDiagramIso` | `SerrePositivity.InfinityCategories.Core.ColimitDiagramIso` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseJoinAugmentation` | `SerrePositivity.InfinityCategories.Core.UniverseJoinAugmentation` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseJoin` | `SerrePositivity.InfinityCategories.Core.UniverseJoin` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseJoinNaturality` | `SerrePositivity.InfinityCategories.Core.UniverseJoinNaturality` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseJoinSimplexShapes` | `SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseBoundary` | `SerrePositivity.InfinityCategories.Core.UniverseBoundary` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseBoundaryHom` | `SerrePositivity.InfinityCategories.Core.UniverseBoundaryHom` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseBoundaryFilling` | `SerrePositivity.InfinityCategories.Core.UniverseBoundaryFilling` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseJoinSimplexNaturality` | `SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexNaturality` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseConeHom` | `SerrePositivity.InfinityCategories.Core.UniverseConeHom` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseSlices` | `SerrePositivity.InfinityCategories.Core.UniverseSlices` | R-B |
| `SerrePositivity.InfinityCategories.Stable.UniverseLimits` | `SerrePositivity.InfinityCategories.Core.UniverseLimits` | R-B |
| `SerrePositivity.InfinityCategories.HomotopyLimits.UniverseSSetMaps` | `SerrePositivity.InfinityCategories.Core.UniverseSSetMaps` | R-B |
| `SerrePositivity.InfinityCategories.Stable.PointConstantHomEquivalence` | `SerrePositivity.InfinityCategories.F1B.PointConstantHomEquivalence` | R-B |
| `SerrePositivity.InfinityCategories.Stable.AdjunctionHomotopyCategory` | `SerrePositivity.InfinityCategories.F1B.AdjunctionHomotopyCategory` | R-B |
| `SerrePositivity.InfinityCategories.F2.CatInfinity.LimitConeExtension` | `SerrePositivity.InfinityCategories.Core.LimitConeExtension` | R-B |
| `SerrePositivity.InfinityCategories.F2.CatInfinity.SliceRestrictionEquivalence` | `SerrePositivity.InfinityCategories.Core.SliceRestrictionEquivalence` | R-B |
| `SerrePositivity.InfinityCategories.F2.CatInfinity.SliceRestrictionEquivalenceLifting` | `SerrePositivity.InfinityCategories.Core.SliceRestrictionEquivalenceLifting` | R-B |
| `SerrePositivity.InfinityCategories.Derived.LimitDiagramIso` | `SerrePositivity.InfinityCategories.Core.LimitDiagramIso` | R-B |
| `SerrePositivity.InfinityCategories.Derived.CofinalLimitExistence` | `SerrePositivity.InfinityCategories.F1B.CofinalLimitExistence` | R-B |
| `SerrePositivity.InfinityCategories.Derived.RightKanPrecompositionFaithful` | `SerrePositivity.InfinityCategories.F1B.RightKanPrecompositionFaithful` | R-B |
| `SerrePositivity.InfinityCategories.Derived.LocalizationFunctorExtension` | `SerrePositivity.InfinityCategories.F1B.LocalizationFunctorExtension` | R-B |
| `SerrePositivity.InfinityCategories.Derived.LocalizationRightKanCriterion` | `SerrePositivity.InfinityCategories.F1B.LocalizationRightKanCriterion` | R-B |
| `SerrePositivity.InfinityCategories.Derived.LocalizationPrecompositionCriterion` | `SerrePositivity.InfinityCategories.F1B.LocalizationPrecompositionCriterion` | R-B |
| `SerrePositivity.InfinityCategories.Derived.DeformationLocalization` | `SerrePositivity.InfinityCategories.F1B.DeformationLocalization` | R-B |
| `SerrePositivity.KST.SConstruction.ZeroBoundaryExtension` | `SerrePositivity.InfinityCategories.Core.ZeroBoundaryExtension` | R-B |
| `SerrePositivity.InfinityCategories.Stable.InitialExtension` | `SerrePositivity.InfinityCategories.Core.InitialExtension` | R-B |
| `SerrePositivity.InfinityCategories.Stable.LimitConeFamilies` | `SerrePositivity.InfinityCategories.Core.LimitConeFamilies` | R-B |
| `SerrePositivity.KST.SConstruction.VertexPrescribedExtension` | `SerrePositivity.InfinityCategories.Core.VertexPrescribedExtension` | R-B |
| `SerrePositivity.KST.LocalizingInvariants.LimitProjectionExistence` | `SerrePositivity.InfinityCategories.Core.LimitProjectionExistence` | R-B |
| `SerrePositivity.KST.SConstruction.RelativeInitialCosliceComparison`（重複削除） | `SerrePositivity.InfinityCategories.Stable.RelativeInitialCosliceComparison`（正本保持） | 3-1 |
| `SerrePositivity.KST.SConstruction.RelativeInitialEndpoint`（重複削除） | `SerrePositivity.InfinityCategories.Stable.RelativeInitialEndpoint`（正本保持） | 3-1 |
| `SerrePositivity.KST.SConstruction.InitialBoundaryTransport`（重複削除） | `SerrePositivity.InfinityCategories.Stable.InitialBoundaryTransport`（正本保持） | 3-1 |
| `SerrePositivity.KST.SConstruction.TerminalBoundaryTransport`（重複削除） | `SerrePositivity.InfinityCategories.Stable.TerminalBoundaryTransport`（正本保持） | 3-1 |

部分抽出の所在（名前空間は `SerrePositivity.InfinityCategories` を保持）：

| 宣言 | 旧ファイル | 新ファイル |
|---|---|---|
| `HasFiniteLimits` | `SerrePositivity/InfinityCategories/Stable/Definition.lean` | `SerrePositivity/InfinityCategories/Core/FiniteLimitsColimits.lean` |
| `HasFiniteColimits` | `SerrePositivity/InfinityCategories/Stable/Definition.lean` | `SerrePositivity/InfinityCategories/Core/FiniteLimitsColimits.lean` |
| `isTerminalVertex_iff_ulift` | `SerrePositivity/InfinityCategories/Stable/UniverseZeroObjects.lean` | `SerrePositivity/InfinityCategories/Core/UniverseInitialTerminal.lean` |
| `isInitialVertex_iff_ulift` | `SerrePositivity/InfinityCategories/Stable/UniverseZeroObjects.lean` | `SerrePositivity/InfinityCategories/Core/UniverseInitialTerminal.lean` |
| `reverseSimplex_vertex` | `SerrePositivity/InfinityCategories/Stable/InitialOpposite.lean` | `SerrePositivity/InfinityCategories/Core/InitialOpposite.lean` |
| `isInitialVertex_of_isTerminalVertex_op` | `SerrePositivity/InfinityCategories/Stable/InitialOpposite.lean` | `SerrePositivity/InfinityCategories/Core/InitialOpposite.lean` |
| `IsInitialVertex.op_isTerminalVertex` | `SerrePositivity/InfinityCategories/Stable/InitialOpposite.lean` | `SerrePositivity/InfinityCategories/Core/InitialOpposite.lean` |
| `isInitialVertex_iff_isTerminalVertex_op` | `SerrePositivity/InfinityCategories/Stable/InitialOpposite.lean` | `SerrePositivity/InfinityCategories/Core/InitialOpposite.lean` |
| `IsTerminalVertex.op_isInitialVertex` | `SerrePositivity/InfinityCategories/Stable/InitialOpposite.lean` | `SerrePositivity/InfinityCategories/Core/InitialOpposite.lean` |
| `edgeCosliceVertex` | `SerrePositivity/InfinityCategories/Stable/ZeroHomotopy.lean` | `SerrePositivity/InfinityCategories/Core/InitialHomotopy.lean` |
| `edgeCosliceVertex_projection` | `SerrePositivity/InfinityCategories/Stable/ZeroHomotopy.lean` | `SerrePositivity/InfinityCategories/Core/InitialHomotopy.lean` |
| `IsInitialVertex.homMk_eq` | `SerrePositivity/InfinityCategories/Stable/ZeroHomotopy.lean` | `SerrePositivity/InfinityCategories/Core/InitialHomotopy.lean` |
| `IsInitialVertex.isInitialHo₂` | `SerrePositivity/InfinityCategories/Stable/ZeroHomotopy.lean` | `SerrePositivity/InfinityCategories/Core/InitialHomotopy.lean` |
| `IsInitialVertex.isInitialHo` | `SerrePositivity/InfinityCategories/Stable/ZeroHomotopy.lean` | `SerrePositivity/InfinityCategories/Core/InitialHomotopy.lean` |
| `IsInitialVertex.exists_stableCosliceLift` | `SerrePositivity/InfinityCategories/Stable/InitialTransport.lean` | `SerrePositivity/InfinityCategories/Core/InitialTransport.lean` |
| `isInitialVertex_of_isInitialHo` | `SerrePositivity/InfinityCategories/Stable/InitialTransport.lean` | `SerrePositivity/InfinityCategories/Core/InitialTransport.lean` |
| `IsInitialVertex.of_vertexIso` | `SerrePositivity/InfinityCategories/Stable/InitialTransport.lean` | `SerrePositivity/InfinityCategories/Core/InitialTransport.lean` |
| `isInitialVertex_iff_of_vertexIso` | `SerrePositivity/InfinityCategories/Stable/InitialTransport.lean` | `SerrePositivity/InfinityCategories/Core/InitialTransport.lean` |
| `IsColimitCone.of_vertexIso` | `SerrePositivity/InfinityCategories/Stable/InitialTransport.lean` | `SerrePositivity/InfinityCategories/Core/InitialTransport.lean` |
| `isColimitCone_iff_of_vertexIso` | `SerrePositivity/InfinityCategories/Stable/InitialTransport.lean` | `SerrePositivity/InfinityCategories/Core/InitialTransport.lean` |
| `QCatEquivalence.map_isInitialVertex` | `SerrePositivity/InfinityCategories/Stable/ColimitCoconeFamily.lean` | `SerrePositivity/InfinityCategories/Core/InitialEquivalence.lean` |
| `QCatEquivalence.isInitialVertex_iff` | `SerrePositivity/InfinityCategories/Stable/ColimitCoconeFamily.lean` | `SerrePositivity/InfinityCategories/Core/InitialEquivalence.lean` |
| `JoinCocone.restrict` | `SerrePositivity/InfinityCategories/Stable/ColimitRestriction.lean` | `SerrePositivity/InfinityCategories/Core/ColimitCoconeRestriction.lean` |
| `JoinCocone.vertex_restrict` | `SerrePositivity/InfinityCategories/Stable/ColimitExistenceTransfer.lean` | `SerrePositivity/InfinityCategories/Core/ColimitExistenceTransfer.lean` |
| `exists_cocone_extension_of_trivialRestriction` | `SerrePositivity/InfinityCategories/Stable/ColimitExistenceTransfer.lean` | `SerrePositivity/InfinityCategories/Core/ColimitExistenceTransfer.lean` |
| `exists_colimitCocone_extension_of_trivialRestriction` | `SerrePositivity/InfinityCategories/Stable/ColimitExistenceTransfer.lean` | `SerrePositivity/InfinityCategories/Core/ColimitExistenceTransfer.lean` |
| `hasColimit_iff_of_trivialRestriction` | `SerrePositivity/InfinityCategories/Stable/ColimitExistenceTransfer.lean` | `SerrePositivity/InfinityCategories/Core/ColimitExistenceTransfer.lean` |
| `sliceUnderRestrict_comp` | `SerrePositivity/InfinityCategories/F1/Joins/CosliceRestriction.lean` | `SerrePositivity/InfinityCategories/Core/SliceUnderRestriction.lean` |
| `sliceUnderRestrict_isIso` | `SerrePositivity/InfinityCategories/F1/Joins/CosliceRestrictionIso.lean` | `SerrePositivity/InfinityCategories/Core/SliceUnderRestriction.lean` |

F2/KST からの機械的宣言名変更：

| 旧名 | 新名 |
|---|---|
| `SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting` | `SerrePositivity.InfinityCategories.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting` |
| `SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext` | `SerrePositivity.InfinityCategories.sliceUnder_empty_hom_ext` |
| `SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting` | `SerrePositivity.InfinityCategories.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting` |
| `SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift` | `SerrePositivity.InfinityCategories.exists_relativeInitialCosliceLift` |
| `SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne` | `SerrePositivity.InfinityCategories.stdSimplex_firstVertex_leftAnodyne` |
| `SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection` | `SerrePositivity.InfinityCategories.pointCosliceVertexOfEdge_projection` |
| `SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge` | `SerrePositivity.InfinityCategories.InitialBoundaryLifting.of_invertibleEdge` |
| `SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso` | `SerrePositivity.InfinityCategories.InitialBoundaryLifting.of_vertexIso` |
| `SerrePositivity.KST.SConstruction.terminalBoundaryLifting_of_initialBoundaryLifting_op` | `SerrePositivity.InfinityCategories.terminalBoundaryLifting_of_initialBoundaryLifting_op` |
| `SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.op_initial` | `SerrePositivity.InfinityCategories.TerminalBoundaryLifting.op_initial` |
| `SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.of_vertexIso` | `SerrePositivity.InfinityCategories.TerminalBoundaryLifting.of_vertexIso` |
| `SerrePositivity.InfinityCategories.F2.restrictJoinCone` | `SerrePositivity.InfinityCategories.restrictJoinCone` |
| `SerrePositivity.InfinityCategories.F2.restrictJoinCone_vertex` | `SerrePositivity.InfinityCategories.restrictJoinCone_vertex` |
| `SerrePositivity.InfinityCategories.F2.exists_cone_extension_of_trivialRestriction` | `SerrePositivity.InfinityCategories.exists_cone_extension_of_trivialRestriction` |
| `SerrePositivity.InfinityCategories.F2.exists_limitCone_extension_of_trivialRestriction` | `SerrePositivity.InfinityCategories.exists_limitCone_extension_of_trivialRestriction` |
| `SerrePositivity.InfinityCategories.F2.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence_subcomplex` | `SerrePositivity.InfinityCategories.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence_subcomplex` |
| `SerrePositivity.InfinityCategories.F2.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence` | `SerrePositivity.InfinityCategories.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence` |
| `SerrePositivity.InfinityCategories.F2.isPrecompositionEquivalence_joinUnion_right` | `SerrePositivity.InfinityCategories.isPrecompositionEquivalence_joinUnion_right` |
| `SerrePositivity.InfinityCategories.F2.sliceOverRestrict_lift_of_precompositionEquivalence` | `SerrePositivity.InfinityCategories.sliceOverRestrict_lift_of_precompositionEquivalence` |
| `SerrePositivity.KST.SConstruction.ZeroBoundaryExtension` | `SerrePositivity.InfinityCategories.Core.ZeroBoundaryExtension` |
| `SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints` | `SerrePositivity.InfinityCategories.exists_extension_of_initial_or_terminal_endpoints` |
| `SerrePositivity.KST.SConstruction.VertexPrescribedExtension` | `SerrePositivity.InfinityCategories.Core.VertexPrescribedExtension` |
| `SerrePositivity.KST.LocalizingInvariants.LimitProjectionExistence` | `SerrePositivity.InfinityCategories.Core.LimitProjectionExistence` |
| `SerrePositivity.KST.SConstruction.exists_extension_with_vertices` | `SerrePositivity.InfinityCategories.exists_extension_with_vertices` |
| `SerrePositivity.KST.LocalizingInvariants.limitConeProjection_surjective` | `SerrePositivity.InfinityCategories.limitConeProjection_surjective` |
| `SerrePositivity.KST.LocalizingInvariants.limitConeProjection_trivialKanFibration` | `SerrePositivity.InfinityCategories.limitConeProjection_trivialKanFibration` |

Derived の一般宣言14組の旧名→正本名は [対応表](../refactor-r-b-derived-name-map.json)。所在は `DGNerve/AugmentationCombinatorics`（13宣言）と `DGNerve/VertexIdentity`（1宣言）。8重複モジュールを削除。

新規共通 Prop 補題 `augmentation_proof_of_endpoint_phases`・`augmentation_proof_of_reindex_cases` は `Derived/AugmentationProofCases`。既存4定理の型を保持し、証明だけを source commit `1a412f887a63d14b73fed3fd0f2af52207a6f25e` の cherry-pick で共有した。データ86宣言の本体は名前置換以外を保持。型依存データ19組は [差分表](../refactor-near-duplicates-derived-2026-10-23.md) に保存し、Dレーン再開後の判断へ保留する。

全 JSON と適用ログは [再適用計画](../refactor-r-b-reapply-2026-10-23/manifest.json)。R23 の CofinalLimitExistence は型の閉包に従い F1B に配置。ZeroBoundaryExtension は InitialExtension・一般 InitialOpposite と同時に Core へ移し、Core→Stable と Stable→KST を残さない。

R-B main 適用検証（2026-10-24）：35モジュール移動、29宣言の本文保持抽出、重複12モジュール削除。検証ソース `eec26ad273f2d26b6eedc339a21f365bac323371`。Core・F1・F1B・F2・HomotopyLimits・Stable・Derived・DGNerve・KST/SConstruction の集約、元のF1 import経由のinstance可視性、`scripts/refactor/verify.sh` の全24監査と空のsorry閉包を確認した。実行記録は [検証結果](../refactor-r-b-reapply-2026-10-23/main-validation-state.json) と [本文・依存監査](../refactor-r-b-reapply-2026-10-23/main-completion-audit.json)。R-B は rebase せず R-C の後の main に JSON 計画を再適用した。

### R-A 最終対応（R13・重複原本共用）

| 旧所在・旧名 | 新所在・正本 | 対応記録 |
|---|---|---|
| F1/Cocartesian* 600本（R11） | F1/Cocartesian、独立入口 | `9942ec9b4`、[全対応](../refactor-ra-r11-module-plan-2026-10-23.json) |
| F1 残り1714本（R12） | 役割別サブディレクトリ | `312b86690`、[全対応](../refactor-ra-r12-module-plan-2026-10-23.json) |
| F1B 最上位766本 | 役割別15ディレクトリ | [モジュール・参照計画](../refactor-ra-final-plan-2026-10-24.json) |
| PinchedInterval 6モジュール・26宣言、KanScaffoldFiniteCylinderEndpoints の5宣言 | F1 の IntervalFat／RightInterval と ScaffoldFiniteCylinderEndpoints | 同計画の redirects と [宣言名対応](../refactor-ra-final-name-map-2026-10-24.json) |
| scaffold の部分重複14宣言 | Core・F1 の原本へ直接参照 | [削除・原本対応](../refactor-ra-final-scaffold-copies-2026-10-24.json) |
| 汎用 scaffold 14宣言の元所在 | Core 1本・F1 3本を新設、既存 Diagrams 2本へ配置 | [本文ハッシュ付き抽出対応](../refactor-ra-final-extractions-2026-10-24.json) |

型・証明は変更しない。旧名842件のうち重複参照45件を除く[明示的な改名規則797件](archive/refactor-ra-final-declaration-renames-2026-10-24.md)は F1B の kan/Kan 接頭辞だけ。他レーン更新は [適用前全一覧](../refactor-ra-final-external-updates-2026-10-24.json) に保存。

## 6. 仮定入力の一覧（完成後に外す）

2026-10-24、`rg -n '\b(IndFiniteLimitExchangeInput|CoherentFilteredLimitExchangeShape|HasSpaceLimitsOfShape|DGKappaConeInput|DGKappaPerfectInput)\b' SerrePositivity --glob '*.lean'` で採取。
使用は定義行・import 行を除く一致行数（同じ行の複数出現は 1、証拠を供給する定理も含む）。
作業ツリーの未追跡ファイルも走査した。定義と使用の行一覧は
[更新一覧](../refactor-assumptions-r-c-main-2026-10-24.md)（[初期一覧](../refactor-assumptions-2026-10-23.md)） を参照。

| 名前 | 所在（SerrePositivity/ 以下） | 供給元 | 使用（一致行／ファイル） |
|---|---|---|---|
| `IndFiniteLimitExchangeInput` | InfinityCategories/F2/Ind/FiniteLimitExchangeInput.lean:18 | F1b a7（全有限形の交換） | 11／9 |
| `CoherentFilteredLimitExchangeShape` | InfinityCategories/F2/FilteredExchange/CoherentFilteredLimitExchange.lean:24 | F1b a7（空・単体の形は証明済み） | 9／7 |
| `HasSpaceLimitsOfShape` | InfinityCategories/F2/FilteredExchange/SpaceLimitShapes.lean:25 | `F2.hasSpaceLimitsOfShape`（`hasLimit_coherentSpaceDiagram` の系、追加仮定なし） | 7／3 |
| `DGKappaConeInput` | KST/NonConnective/DGKappaConeInput.lean:47 | D（K-7 へ非可算 κ-compact dg 小模型を供給） | 16／16 |
| `DGKappaPerfectInput` | KST/NonConnective/DGKappaPerfectInput.lean:36 | D（K-7 へ実 Perf との ∞ 圏比較を供給） | 3／2 |

## 7. 再発防止（foundations.md §8 に追加済み、ユーザー承認 10-23 09:33）

- 必要な補題が禁止された import 閉包にある場合はコピーせず、上流ファイルを分割する。
- モジュールの移動・改名と下流の参照更新は同じ段階で行い、互換シムは残さない。
- `scripts/check_duplicates.py` を全体ビルドの監査に加え、完全一致の組が増えたら報告する。

## 8. 停止窓での R 分担（実施記録）

以下は停止窓の分担記録。現在の所有・再開運用は foundations.md §6・§8 を正本とする。

全作業レーンは停止済み（基準タグ `stage1-checkpoint-2026-10-23`）。R を三つのチャットに分け、各自の worktree（`../SerrePositivity-<名前>`、
ブランチ `refactor/<名前>`、`.lake` は main から `cp -Rc` でクローン）で作業する。互換シムは使わず、移動・改名・参照の置換を直接行う。
**初回取り込み後の運用（ユーザー指示）**：R-A だけは main で直接作業し、旧 worktree は使用しない。R-B・R-C は worktree 運用のまま。

| レーン | 所有（変更してよい範囲） | 項目 | 取り込み順 |
|---|---|---|---|
| R-A | Core、F1、F1B、PinchedHom、Coherent、`scripts/move_module.py`、`scripts/check_duplicates.py` | 第 0〜1 段・第 5 段（F1/F1B 重複の直接除去、Core への分割）、R5 前半、R6・R7・R9 の入口、第 4 段の R11・R12・R13 | 1（最上流） |
| R-B | Stable、Derived、DGNerve、DoldKanComparison、KST 側の逆向き依存（R3 の 2 モジュール） | 2-1〜2-5（R2・R3・R14・R22・R23・R24）、3-1 の Stable↔KST・Derived の準重複、R8 の未追跡重複の削除 | 3 |
| R-C | F2、HomotopyLimits、F2/Presentable、EInfinity・HomotopicalAlgebra の重複 | 2-6〜2-8（R15・R16・R17）、R19、R20 の一覧の保守、3-1 の EInfinity 19 組・HomotopicalAlgebra 8 組 | 2 |

- 他レーンの範囲への書き込みは、(a) 新規ファイルの追加（Core への移動先など）、(b) `move_module.py` による import 行・参照の機械的な書き換え、だけ許す。
  集約ファイルの import 行の追加・削除は (b) に含める。衝突はコーディネータが取り込み時に解決する。
- 取り込みはコーディネータが上流から順に行う（R-A → R-C → R-B）。取り込み後、他の worktree は `git rebase main` と `.lake` の再クローンを行う。
- 各レーンは自分の対象ビルドと該当監査を worktree で通してから報告する。取り込み後にコーディネータが全体ビルド・全監査・`main_statement` の sorry 閉包監査を通し、層ごとにタグを打つ。
- docstring（R21）と入口・README（R18・R25 の残り）は各レーンが自分の範囲で行う。期限は 10-25 夜。終わらない項目は第 I 段終了時へ。
