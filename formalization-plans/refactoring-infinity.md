# R レーン：∞ 圏基盤のリファクタリング（2026-10-23 新設）

解説 [exposition/ja/infinity/](../exposition/ja/infinity/index.html)（第 0〜8 章、R8 重複調査）が挙げた候補 R1〜R25 を、
全レーン停止後に実施する。停止の合図までは専用 worktree に隔離する。正本はこのファイル。実施記録はコミットメッセージ。候補の番号は解説の番号をそのまま使う。

## 引き継ぎ

### 現在地

- 全レーン停止を 2026-10-23 11:03 に受領。コーディネータの main 基準タグ `stage1-checkpoint-2026-10-23`（`f8df7f77b`）を受領。§8（`c6692be81`）を分担の正本とする。
- `../SerrePositivity-R`、`refactor/r-lane` のバッチをコミット後、main に rebase。ff-merge はコーディネータが行う。取り込み前は main を変更・ビルドしない。
- 0-1・0-2・0-4 はコミット済み。共有ツリーの指定 3 モジュールも復旧・再ビルド済み（1933 jobs、終了コード 0）。
- 0-3、第 1 段、第 5 段の直接置換を実装。互換シムを残さず、重複側を削除して下流 import・名前を更新。
- Core への汎用宣言抽出、F1B 重複除去、Stable の汎用補助 17 モジュールの Core 移動を同じバッチにした。
- 静的検査：参照先不在 import 0、旧 KanSection 名前空間参照 0、Core/F1B の禁止閉包 0、差分空白検査合格。
- 最終ソースの Lean ビルド・全監査は未実施。§4 の未検証項目は完了扱いにしない。

### 残り（依存順）

§4 の段階表。第 0〜1 段・第 5 段の検証後、第 2〜3 段、第 4 段へ進む。

### 主要宣言・依存と提供

- 新しい定理を追加しない。宣言の移動先は §5 と保存した対応一覧を参照。
- 所有：本計画、重複検査、R 専用監査、新設 Core モジュール、直接置換の変更。
- 他レーンの変更対象は事前にレーン名・ファイル名・変更種類を報告済み。

### 既知の問題

- `.lake` クローン時に生成中だった 12 ファイルのコピーが失敗。最終ビルドで生成・検証する。
- 重複側と原本の証明項が一致しない例は、原本を無変更で残し重複側を削除。証明の同一性を主張しない。

### 次の一手

- バッチのコミット・rebase 結果をコーディネータに報告し、コーディネータによる ff-merge を待つ。
- 取り込み後は main を正とし、最初に `scripts/move_module.py` を作る。以後の担当は §8 の R-A に限定する。
- 各段階の対象ビルド・該当監査・重複検査の結果と実測時間を報告する。全体ビルドとタグはコーディネータ。

## 1. 目的と範囲

- 目的：(a) 複製されたコードの除去、(b) 一般論を正しい層（Core・F1B）へ移す、(c) 逆向き依存（基盤 → KST、DGNerve ↔ Derived）の解消、
  (d) 入口と README を読める形にする。数学的内容・宣言の型・証明は変えない。
- 範囲外：証明の書き直し（R5 の双対化、R10 の計算規則の統合）、docstring の書き直し（R21、各レーンが工程完了時に行う）、
  ファイル粒度の変更（R4）。これらは第 I 段の終了時に改めて計画する。

## 2. 不変条件と実施方針（2026-10-23、全レーン停止方式へ変更）

1. 数学的内容・宣言の型・残す原本の証明を変えない。重複側は削除し、参照を原本へ直接向ける。
   宣言・モジュールの改名は許す。互換シムは残さず、下流の import と `KanSection.foo` 等も同じ段階で置換する。
2. 一般論の import 閉包に straightening 等の不要な依存を追加しない。F1B の禁止閉包監査を保つ。
   型・instance の解決に必要な import は明示し、以前の暗黙の依存をビルド・監査で確認する。
3. `sorry`・新規公理・引用・`ModelCategory SSet` 等の instance 仮定を導入しない。
   公理監査は標準三公理だけ。既存監査の検査対象や検査条件を弱めない。
4. 各段階の終わりに対象ビルド、該当監査、`scripts/check_duplicates.py` を実行し、結果と所要時間を記録・報告する。
   全体ビルド・全監査・タグはコーディネータが行う（§8 と最新の R-A 指示）。
5. 全レーン停止と基準タグは受領済み。バッチを専用 worktree でコミットして main に rebase し、結果を報告する。
   ff-merge はコーディネータが行う。取り込み後は main を正として直接作業する。
6. 所有範囲と他レーンへの書き込み条件は §8 を正本とする。今後の他レーン変更は (a)(b) に限定する。

## 3. 停止・main への移行・再開（2026-10-23 R-A 分担へ更新）

- 基準：`stage1-checkpoint-2026-10-23`（`f8df7f77b`）。分担の正本：`c6692be81` の §8。
- worktree の R 所有の変更だけを `set -o pipefail` のうえ `git commit --only` で保存し、`git rebase main` 後に報告する。
  コーディネータが ff-merge するまで main を変更しない。他レーンの未コミット作業を巻き込んでコミット・破棄しない。
- 取り込み後は main で直接作業し、互換シムは残さない。最初に `scripts/move_module.py` を作り、以後の機械的置換に使う。
- R-A の順序：第 0〜1 段＋第 5 段の F1/F1B 重複除去 → R5 前半・R6・R7・R9 の入口 → 第 4 段の R11・R12・R13。
  他レーンの範囲は §8 の (a) 新規ファイル追加、(b) ツールによる import・参照・集約の機械的更新だけ。
- 変更前のレーン名・ファイル名・種類の報告は継続する。各段の対象ビルド・該当監査・重複検査と所要時間を報告する。
- 期限は **2026-10-25 夜**。終わらない項目は「第 I 段終了時」に戻す。全体ビルドとタグはコーディネータ。

## 4. 段階

| 段 | 内容 | 候補 | 触るレーン | 条件 | 完了 |
|---|---|---|---|---|---|
| 0-1 | 正規化ハッシュによる重複検査 `scripts/check_duplicates.py`。現状の一覧を `archive/` に保存 | R8 再発防止 | なし | 即時 | 2026-10-23 09:35 JST |
| 0-2 | `InfinityCategories/README.md`（dg nerve の規約）を `DGNerve/README.md` へ移し、最上位 README を全体地図（層・入口・監査スクリプト）に | R25 | なし | 即時 | 2026-10-23 09:37 JST |
| 0-3 | `F2/JoinRightRelativeRetraction` を削除し、import と F2 公開名を F1 原本へ直接置換 | R8 段階 0 | F1b（10-20 以降未変更） | §3 | |
| 0-4 | 仮定入力の一覧（§6）を grep で作り本計画に固定 | R17・R20 | なし | 即時 | 2026-10-23 09:40 JST |
| 1-1 | `F1/PullbackFiber`・`F1/LeftFiberKan` を汎用部（新 `Core/VertexFiberPullback`・`Core/LeftFiberKan`）と straightening 部（`LeftUnstraighteningFiberIso`・`LeftUnstraighteningFiberKan`、Core を import）に分割 | R8 段階 1 | F1（10-18 以降未変更） | §3 | |
| 1-2 | 汎用部だけで足りる直接 importer（6 本）を Core 側へ向け直す。下流の import と名前を原本へ直接更新する（旧依存を保つための import は加えない） | R8 段階 2 | F1・F1B・HomotopyLimits・F2 | 1-1 の後、§3 | |
| 1-3 | F1B の `KanSection*` 重複を削除し原本へ直接置換。現状の宣言数と差分を再検証し、独自内容だけを残す | R8 段階 3 | F1b（10-19 以降未変更） | 1-2 の後（F1B 監査が原本の閉包を通すため） | |
| 1-4 | `Core/Fibrations.lean`・`Core/MappingSpace.lean` の入口（定義は動かさず import と docstring で目次化） | R7・R9 | なし | 即時 | |
| 1-5 | `Stable/SliceOpposite` の `sliceOverOpIso` を `Core/SliceOpposite` へ移し、旧ファイルを削除・参照を直接更新 | R5 の前半 | D（10-18 以降未変更） | §3 | |
| 2-1 | `Stable/Cocone`・`UniverseLimits`・`ColimitDiagramIso`・`Definition` の `HasFiniteLimits` を `Core/Colimit*` へ（旧ファイルを削除して直接置換） | R2・R22 | D | D-7 d 完了直後 | |
| 2-2 | `Stable/AdjunctionHomotopyCategory` を `F1B/AdjunctionHomotopyCategory` へ | R14 | D・F1b | 2-1 と同時 | |
| 2-3 | `Derived/LimitDiagramIso`・`CofinalLimitExistence` を Core へ、`Localization*Criterion`・`DeformationLocalization` を F1B へ | R23 | D・F1b | D の区切り | |
| 2-4 | `KST/SConstruction/VertexPrescribedExtension`・`KST/LocalizingInvariants/LimitProjectionExistence` の内容を Core へ移し KST の旧ファイルを削除して直接置換。Stable → KST の import を解消 | R3 | K-S•・Sp・D | 三レーンの区切り | |
| 2-5 | `DGNerve/SemifreeLimits` を Derived（または DifferentialGraded）へ、DGNerve の旧ファイルを削除して直接置換 | R24 | D | D の区切り | |
| 2-6 | `F2/Ind/ElementsDiagram` の密度定理を F1 の前層の層へ | R15 | F1 | F1-7 完了後 | |
| 2-7 | `F2/SpaceLimitShapes` の条件付き版を無条件定理の系に（3 ファイル） | R17 | F1b | a7 完了・差し替えと同時 | |
| 2-8 | `HomotopyLimits/Local*`・`Sigma*`・`Sifted*` を `F2/Presentable/` へ | R16 | N・P | P-1 f・g 完了後 | |
| 3-1 | その他の完全一致・準重複：`F2/JoinRight*`↔`F1/JoinDiagramRight*`、Stable↔KST 4 組、`Derived/DGCommaAug*`↔`DGModuleAugmentation*` 17 組、EInfinity 19 組、HomotopicalAlgebra 8 組 | R8 §3 | F1b・K-S•・D・E2 | 各レーンの区切り | |
| 3-2 | `PinchedInterval` 6 本・`KanScaffold`／`KanCocartesian` 15 本の精査 | R8 段階 4 | F1b | F1b-5 a7 完了後 | |
| 4-1 | 休止中の Cat∞ 値 straightening `F1/Cocartesian*`（3.7 万行）を `F1/Cocartesian/` へ移し集約から外す | R11 | F1 | F1 の区切り（集約の一行は F1 に依頼） | |
| 4-2 | F2 最上位を `F2/CatInfinity/`（完成）と `F2/FilteredExchange/`（作業中）へ | R19 | F1b | a7 完了後 | |
| 4-3 | F1 のサブディレクトリ化、F1B の `Kan*` 接頭辞の整理、ディレクトリ名の層への対応 | R12・R13・R1・R6 | F1・F1b | 第 I 段終了時 | |
| 5 | 旧重複モジュールの削除と `KanSection.foo` → `foo` の直接置換（約 60 箇所）、`HomotopyLimits.lean` の docstring と `quillenCfBottomEndpoint_wrong` 等の改名 | R18 ほか | 全レーン | 第 0〜1 段と同時（全停止後） | |

## 5. 移動した宣言の所在

| 旧所在（削除・改名） | 新所在 | 段 | コミット |
|---|---|---|---|
| F1/PullbackFiber・LeftFiberKan の汎用部 | Core/VertexFiberPullback・LeftFiberKan | 1-1 | 本バッチ、段階検証待ち |
| F1/ScaffoldFiniteVerticalEdges の prism・LeftStrictTransport の under map | Core/PrismVerticalSimplex・NerveUnderMap | 1-3 | 同上 |
| F1/PullbackNerveFiber・ScaffoldUnderChain | Core/VertexFiberNervePullback・F1B/ScaffoldUnderChain | 1-3 | 同上 |
| F1B/KanSection 重複群・F2/JoinRightRelativeRetraction | F1 原本または新 Core（[全対応一覧](archive/refactor-direct-batch-2026-10-23.json)） | 0-3・1-3・5 | 同上 |
| Stable/SliceOpposite と join/reverse 汎用補助 16 本 | Core の同名モジュール | 1-5 | 同上 |

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

- 必要な補題が禁止された import 閉包にある場合はコピーせず、上流ファイルを分割する。
- モジュールの移動・改名と下流の参照更新は同じ段階で行い、互換シムは残さない。
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
