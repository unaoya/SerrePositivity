# R レーン：∞ 圏基盤のリファクタリング（2026-10-23 新設）

解説 [exposition/ja/infinity/](../exposition/ja/infinity/index.html)（第 0〜8 章、R8 重複調査）が挙げた候補 R1〜R25 を、
稼働中の 11 レーンの作業を壊さずに実施する。正本はこのファイル。実施記録はコミットメッセージ。候補の番号は解説の番号をそのまま使う。

## 引き継ぎ

### 現在地

- 10-23 09:45：シム方式の試作をコーディネータが確認。`F1/RelativeFunctorEvaluation` を `public import` し
  `namespace …KanSection` 内で `export …InfinityCategories (relativeFunctorEvaluate relativeFunctorEvaluate_ι)` とした
  モジュールを別モジュールから `public import` すると、`KanSection.relativeFunctorEvaluate` が解決される（試作ファイルは削除済み）。
- 0-1 完了：追跡済み 11,632 ファイルを走査し、実体の重複 18 群（KanSection 17 組と JoinRightRelativeRetraction 1 組）を保存。
  正規化のコメント・文字列・トークン境界と基準比較を検証。基準からの増加は 0 組。
- 0-3 検証中：F2/JoinRightRelativeRetraction を原本の export シムに変更。単体・直接下流・R 監査は通過。
  正本モジュールへの参照以外に依存追加はない。集約の検証は下記の再実行待ち。
- 10-23 09:46：1-1 を共有ツリーに直接適用したところ、F1/PullbackFiber の変更が下流全体の再ビルド連鎖を起こし、N が
  olean 欠落で停止。共有ツリーの変更は取り消し、以後は worktree 方式（§3）に切り替える。1-1 の内容自体は worktree で再適用する。
- 1-1 実装・対象検証済み（共有ツリーでは取り消し、worktree で再適用）：汎用 4 宣言を Core/VertexFiberPullback・Core/LeftFiberKan へ本文そのまま移動。
  旧 F1 二本は元の import と専用宣言を保持し Core を public import。4 モジュールのビルドと R の 8 宣言監査が通過。
  Core 二本は straightening を含まず、旧 F1 二本の閉包に加わるのは新 Core モジュールへの参照だけ。
- 0-4 完了：§6 に 5 入力の所在・供給元・使用数を固定し、grep の全一致行を archive に保存。
- 0-2 完了：dg nerve の規約を DGNerve/README.md に保存し、全体 README を層・入口・監査の地図に変更。
  文面の保存（リンク以外）と全ローカルリンクを検証。

### 残り（依存順）

§4 の段階表。各段の末尾に「完了日時」を書き換える。

### 主要宣言

- なし（本レーンは新しい定理を作らない。移動した宣言の新しい所在は §5 の表に記録する）。

### 依存と提供

- 所有：本計画、`scripts/check_duplicates.py`、`scripts/audit_refactor_shims.lean`、新設する `Core/` のモジュール、
  各レーンから移管された互換シム。
- 他レーンのファイルは §3 の条件を満たすものだけを、§3 の手順で変更する。

### 未コミット

- 0-3：`F2/JoinRightRelativeRetraction.lean`・`scripts/audit_refactor_shims.lean`。
- 1-1：`F1/PullbackFiber.lean`・`F1/LeftFiberKan.lean`・新設 `Core/VertexFiberPullback.lean`・`Core/LeftFiberKan.lean`。
  宣言ブロック・専用部が元と文字列一致することを確認。集約検証完了後にコミットする。
- 実行中：F2 ビルド session `40443`（`/tmp/r-lane-0-3-build.log`）、
  F1 ビルド session `9607`（`/tmp/r-lane-1-1-f1-build.log`）。両方が終端になってから単一の F1・F2 ビルドを再実行する。
- R 監査成功ログ：`/tmp/r-lane-1-1-shim-audit.log`。対象ビルド成功ログ：`/tmp/r-lane-1-1-build.log`。

### 既知の問題

- R が集約ビルドを並行起動したため、再生成中の `.olean` を読む競合が発生した。数学・型のエラーとは判定していない。
  追加の並行集約ビルドは起動せず、実行中の二本が終わってから F1・F2 を単一コマンドで再検証する。
- 1-2 の直接 importer は調査後に増加。48 時間未満・未追跡のファイルは変更不可。対象と保守的 import の追加先を §3 で再選別する。

### 次の一手

- 二つの集約ビルドの終端を確認してから単一コマンドで F1・F2 をビルドし、関係監査後に 0-3・1-1 をコミット。
  1-2 は `/tmp/r-lane-simulate-1-2.py` の閉包シミュレーション（session `10090`）と §3 の再選別から。

## 1. 目的と範囲

- 目的：(a) 複製されたコードの除去、(b) 一般論を正しい層（Core・F1B）へ移す、(c) 逆向き依存（基盤 → KST、DGNerve ↔ Derived）の解消、
  (d) 入口と README を読める形にする。数学的内容・宣言の型・証明は変えない（第 3 段までは宣言名も変えない）。
- 範囲外：証明の書き直し（R5 の双対化、R10 の計算規則の統合）、docstring の書き直し（R21、各レーンが工程完了時に行う）、
  ファイル粒度の変更（R4）。これらは第 I 段の終了時に改めて計画する。

## 2. 不変条件（破ったら即コミットを戻す）

1. 旧モジュール名は消さない。移動・統合した旧モジュールは、新しい所在を `public import` し `export` で旧名前空間の別名を与える
   **互換シム**として残す。下流の `import` 行と宣言名はどこも変更しない（削除・改名の一括整理は §4 第 5 段）。
2. 旧モジュールの import 閉包を縮めるだけで、広げない。分割の場合、旧モジュールは分割後の全モジュールを `public import` する。
3. 各レーンの監査スクリプトの `#check` が全て通る。F1B の「straightening を閉包に含まない」監査（`audit_infinity_f1b.lean`）も通る。
4. `sorry`・`axiom`・`ModelCategory SSet` 等の instance 仮定を増やさない。公理監査は標準三公理のみ。
5. 稼働中レーンのファイルを、共有の作業ツリー（main のチェックアウト）で直接変更しない。R は専用の git worktree
   `../SerrePositivity-R`（ブランチ `refactor/r-lane`、`.lake` は APFS クローン）で作業し、main への取り込みは §3 の手順で
   コーディネータが行う。理由：上流モジュールを共有ツリーで変えると、全レーンで下流の再ビルド連鎖と olean の競合が起きる
   （10-23 09:46、1-1 の適用で N が停止した）。
6. 稼働中レーンの集約ファイル（`F1.lean`・`F1B.lean`・`F2.lean`・`Stable.lean`・`Derived.lean`・`HomotopyLimits.lean`・`KST/*.lean`）と
   監査スクリプトは R が編集しない。必要な一行は、コーディネータ経由でそのレーンに依頼する。

## 3. 作業場所と取り込みの手順（10-23 09:55 改訂）

- 作業場所：`git worktree add -b refactor/r-lane ../SerrePositivity-R main` で作った worktree。`cp -Rc .lake ../SerrePositivity-R/.lake`
  （APFS のクローン、数十秒）でビルド済み olean を持ち込む。以後 R のビルド・監査・コミットはすべて worktree 内で行う。
  共有ツリー（main のチェックアウト）には R のファイルを置かない。
- 取り込み（1 バッチ = 0-3・1-1・1-2・1-3・1-5 のように上流変更をまとめたもの）：R がバッチ完了を報告 → コーディネータが
  取り込み時刻を提案しユーザーが決める（レーンが止まっている時間帯）→ R は worktree で `git rebase main`、`.lake` を main から
  再クローン、全体ビルド（`lake build SerrePositivity`）と全監査を通す → コーディネータが main で `git merge --ff-only refactor/r-lane`
  → worktree の `.lake/build` を main の `.lake/build` へクローンで上書きし、レーンの再ビルド連鎖を起こさない → レーン再開。
- 下記の「他レーンのファイルに触る条件」は、取り込むファイルの選定条件としてそのまま残す。

## 3′. 他レーンのファイルに触る条件（選定条件）

- 条件：(i) そのファイルの最終コミットが 48 時間以上前、(ii) `git status` に出ていない、(iii) 変更が純粋な移動・分割・シム化で宣言の型が同一。
  三つとも満たすときだけ R が変更する。満たさないものは §4 の「レーンの区切り待ち」に入れる。
- 手順：変更前にコーディネータへ「レーン・ファイル名・種類（分割／シム化）」を報告し、コーディネータが次の進捗確認でそのレーンに
  一行通知する。レーンのビルドが壊れた場合、そのレーンは既存規約どおり停止して報告し、R は当該コミットを `git revert` する。
- Core・PinchedHom・Coherent・DGNerve・DoldKanComparison は所有レーンがなく 10-18 以降変更がない。R が直接変更してよい。
- 検証：対象の集約（`lake build SerrePositivity.InfinityCategories.<Dir>`）と関係する監査スクリプト。
  他レーンの作業中ファイルに起因する失敗は R の責任外として報告だけする。コミットは `set -o pipefail` のうえ `git commit --only`。

## 4. 段階

| 段 | 内容 | 候補 | 触るレーン | 条件 | 完了 |
|---|---|---|---|---|---|
| 0-1 | 正規化ハッシュによる重複検査 `scripts/check_duplicates.py`。現状の一覧を `archive/` に保存 | R8 再発防止 | なし | 即時 | 2026-10-23 09:35 JST |
| 0-2 | `InfinityCategories/README.md`（dg nerve の規約）を `DGNerve/README.md` へ移し、最上位 README を全体地図（層・入口・監査スクリプト）に | R25 | なし | 即時 | 2026-10-23 09:37 JST |
| 0-3 | `F2/JoinRightRelativeRetraction` を F1 原本へのシムに | R8 段階 0 | F1b（10-20 以降未変更） | §3 | |
| 0-4 | 仮定入力の一覧（§6）を grep で作り本計画に固定 | R17・R20 | なし | 即時 | 2026-10-23 09:40 JST |
| 1-1 | `F1/PullbackFiber`・`F1/LeftFiberKan` を汎用部（新 `Core/VertexFiberPullback`・`Core/LeftFiberKan`）と straightening 部（旧名、Core を import）に分割 | R8 段階 1 | F1（10-18 以降未変更） | §3 | |
| 1-2 | 汎用部だけで足りる直接 importer（6 本）を Core 側へ向け直す。閉包が縮む外部ファイルには旧 import を保守的に残す | R8 段階 2 | F1・F1B・HomotopyLimits・F2 | 1-1 の後、§3 | |
| 1-3 | F1B の `KanSection*` 31 本のうち本体同一の分（126 宣言、1,660 行）をシム化。`KanSectionPrism` と中継 1 本は残す | R8 段階 3 | F1b（10-19 以降未変更） | 1-2 の後（F1B 監査が原本の閉包を通すため） | |
| 1-4 | `Core/Fibrations.lean`・`Core/MappingSpace.lean` の入口（定義は動かさず import と docstring で目次化） | R7・R9 | なし | 即時 | |
| 1-5 | `Stable/SliceOpposite` の `sliceOverOpIso` を `Core/SliceOpposite` へ（Stable 側シム） | R5 の前半 | D（10-18 以降未変更） | §3 | |
| 2-1 | `Stable/Cocone`・`UniverseLimits`・`ColimitDiagramIso`・`Definition` の `HasFiniteLimits` を `Core/Colimit*` へ（Stable 側シム） | R2・R22 | D | D-7 d 完了直後 | |
| 2-2 | `Stable/AdjunctionHomotopyCategory` を `F1B/AdjunctionHomotopyCategory` へ | R14 | D・F1b | 2-1 と同時 | |
| 2-3 | `Derived/LimitDiagramIso` を Core、`CofinalLimitExistence` を F1B へ、`Localization*Criterion`・`DeformationLocalization` を F1B へ | R23 | D・F1b | D の区切り | |
| 2-4 | `KST/SConstruction/VertexPrescribedExtension`・`KST/LocalizingInvariants/LimitProjectionExistence` の内容を Core へ移し KST 側シム。Stable → KST の import を解消 | R3 | K-S•・Sp・D | 三レーンの区切り | |
| 2-5 | `DGNerve/SemifreeLimits` を Derived へ直接移動（互換シムなし） | R24 | D | D の区切り | 2026-10-23（R-B、aa2236b66） |
| 2-6 | `F2/Ind/ElementsDiagram` の密度定理を F1 の前層の層へ | R15 | F1 | F1-7 完了後 | |
| 2-7 | `F2/SpaceLimitShapes` の条件付き版を無条件定理の系に（3 ファイル） | R17 | F1b | a7 完了・差し替えと同時 | |
| 2-8 | `HomotopyLimits/Local*`・`Sigma*`・`Sifted*` を `F2/Presentable/` へ | R16 | N・P | P-1 f・g 完了後 | |
| 3-1 | その他の完全一致・準重複：`F2/JoinRight*`↔`F1/JoinDiagramRight*`、Stable↔KST 4 組、`Derived/DGCommaAug*`↔`DGModuleAugmentation*` 17 組、EInfinity 19 組、HomotopicalAlgebra 8 組 | R8 §3 | F1b・K-S•・D・E2 | 各レーンの区切り | |
| 3-2 | `PinchedInterval` 6 本・`KanScaffold`／`KanCocartesian` 15 本の精査 | R8 段階 4 | F1b | F1b-5 a7 完了後 | |
| 4-1 | 休止中の Cat∞ 値 straightening `F1/Cocartesian*`（3.7 万行）を `F1/Cocartesian/` へ移し集約から外す | R11 | F1 | F1 の区切り（集約の一行は F1 に依頼） | |
| 4-2 | F2 最上位を `F2/CatInfinity/`（完成）と `F2/FilteredExchange/`（作業中）へ | R19 | F1b | a7 完了後 | |
| 4-3 | F1 のサブディレクトリ化、F1B の `Kan*` 接頭辞の整理、ディレクトリ名の層への対応 | R12・R13・R1・R6 | F1・F1b | 第 I 段終了時 | |
| 5 | シムの一括削除と `KanSection.foo` → `foo` の置換（約 60 箇所）、`HomotopyLimits.lean` の docstring と `quillenCfBottomEndpoint_wrong` 等の改名 | R18 ほか | 全レーン | 第 I 段終了時 | |

## 5. 移動した宣言の所在

| 旧所在 | 新所在 | 段 | コミット |
|---|---|---|---|
| `SerrePositivity.KST.SConstruction.RelativeInitialCosliceComparison` | `SerrePositivity.InfinityCategories.Stable.RelativeInitialCosliceComparison` | 3-1 R-B | `20f3cc257` |
| `SerrePositivity.KST.SConstruction.RelativeInitialEndpoint` | `SerrePositivity.InfinityCategories.Stable.RelativeInitialEndpoint` | 3-1 R-B | `20f3cc257` |
| `SerrePositivity.KST.SConstruction.InitialBoundaryTransport` | `SerrePositivity.InfinityCategories.Stable.InitialBoundaryTransport` | 3-1 R-B | `20f3cc257` |
| `SerrePositivity.KST.SConstruction.TerminalBoundaryTransport` | `SerrePositivity.InfinityCategories.Stable.TerminalBoundaryTransport` | 3-1 R-B | `20f3cc257` |
| `DGNerve/SemifreeLimits` | `Derived/SemifreeLimits` | 2-5 R-B | aa2236b66 |


### R-B 3-1：KST 宣言名の直接置換（互換シムなし）

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


### R-B：共通の augmentation 証明補題

| 宣言 | 所在 | 利用 |
|---|---|---|
| `augmentation_proof_of_endpoint_phases` | `Derived/AugmentationProofCases` | comma・加群の Prop 定理、型は保持 |
| `augmentation_proof_of_reindex_cases` | `Derived/AugmentationProofCases` | comma・加群の Prop 定理、型は保持 |


### R-B：augmentation の一般宣言の直接共有化

| 旧 comma 名 | 正本名（InfinityCategories 名前空間） | 旧正本ファイル（Derived/） | 新所在 |
|---|---|---|---|
| `dgCommaAugmentationCutPoints` | `dgModuleAugmentationCutPoints` | `DGModuleAugmentationCorrection` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationCutPoints_erase` | `dgModuleAugmentationCutPoints_erase` | `DGModuleAugmentationCorrection` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationPhase_double_cut_cancel` | `dgModuleAugmentationPhase_double_cut_cancel` | `DGModuleAugmentationPhaseDoubleCut` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationImage_double_cut_cancel` | `dgModuleAugmentationImage_double_cut_cancel` | `DGModuleAugmentationImageCutSigns` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationImage_phase_double_cut_cancel` | `dgModuleAugmentationImage_phase_double_cut_cancel` | `DGModuleAugmentationImageCutSigns` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationCutPoints_eq_filter_interior` | `dgModuleAugmentationCutPoints_eq_filter_interior` | `DGModuleAugmentationLinearCancellation` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationCutPoints_image` | `dgModuleAugmentationCutPoints_image` | `DGModuleAugmentationReindexIndex` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationLeftCut_image_card` | `dgModuleAugmentationLeftCut_image_card` | `DGModuleAugmentationReindexIndex` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationRightCut_image_card` | `dgModuleAugmentationRightCut_image_card` | `DGModuleAugmentationReindexIndex` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentationCut_injective_glue` | `dgModuleAugmentationCut_injective_glue` | `DGModuleAugmentationReindexIndex` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaSimplexHomOrZero_pullback_of_inj` | `dgSimplexHomOrZero_pullback_of_inj` | `DGModuleAugmentationReindexCoefficient` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaAugmentation_sum_mixed_cancel_filter` | `dgModuleAugmentation_sum_mixed_cancel_filter` | `DGModuleAugmentationCutErasure` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaDifferential_compose_of_indices` | `dgDifferential_compose_of_indices` | `DGModuleAugmentationCutBoundary` | `DGNerve/AugmentationCombinatorics` |
| `dgCommaNerve_vertex_identity_simplex` | `dgNerve_vertex_identity_simplex` | `DGModuleAugmentationActualComponent` | `DGNerve/VertexIdentity` |

## 6. 仮定入力の一覧（完成後に外す）

2026-10-23、`rg -n '\b(IndFiniteLimitExchangeInput|CoherentFilteredLimitExchangeShape|HasSpaceLimitsOfShape|DGKappaConeInput|DGKappaPerfectInput)\b' SerrePositivity --glob '*.lean'` で採取。
使用は定義行・import 行を除く一致行数（同じ行の複数出現は 1、証拠を供給する定理も含む）。
作業ツリーの未追跡ファイルも走査した。定義と使用の行一覧は
[保存一覧](archive/refactor-assumptions-2026-10-23.md) を参照。

| 名前 | 所在（SerrePositivity/ 以下） | 供給元 | 使用（一致行／ファイル） |
|---|---|---|---|
| `IndFiniteLimitExchangeInput` | InfinityCategories/F2/Ind/FiniteLimitExchangeInput.lean:18 | F1b a7（全有限形の交換） | 11／9 |
| `CoherentFilteredLimitExchangeShape` | InfinityCategories/F2/CoherentFilteredLimitExchange.lean:24 | F1b a7（空・単体の形は証明済み） | 9／7 |
| `HasSpaceLimitsOfShape` | InfinityCategories/F2/SpaceLimitShapes.lean:24 | γ3 の無条件版へ R17 で差し替え予定 | 6／3 |
| `DGKappaConeInput` | KST/NonConnective/DGKappaConeInput.lean:47 | D（K-7 へ非可算 κ-compact dg 小模型を供給） | 7／7 |
| `DGKappaPerfectInput` | KST/NonConnective/DGKappaPerfectInput.lean:36 | D（K-7 へ実 Perf との ∞ 圏比較を供給） | 3／2 |

## 7. 再発防止（foundations.md §8 に追加済み、ユーザー承認 10-23 09:33）

- 必要な補題が禁止された import 閉包にある場合は、コピーせず、上流ファイルの分割をコーディネータ経由で所有レーンに依頼する。
- モジュールの移動・改名は旧モジュール名を互換シムとして残し、下流の import と宣言名を壊さない。削除は第 I 段終了時にまとめて行う。
- `scripts/check_duplicates.py` を全体ビルドの監査に加え、完全一致の組が増えたら報告する。

## 8. 並列化（2026-10-23 11:15、ユーザー決定：全レーン停止中にリファクタリングを先に完了する）

全作業レーンは停止済み（基準タグ `stage1-checkpoint-2026-10-23`）。R を三つのチャットに分け、各自の worktree（`../SerrePositivity-<名前>`、
ブランチ `refactor/<名前>`、`.lake` は main から `cp -Rc` でクローン）で作業する。互換シムは使わず、移動・改名・参照の置換を直接行う。

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
