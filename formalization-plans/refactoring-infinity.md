# R レーン：∞ 圏基盤のリファクタリング（2026-10-23 新設）

解説 [exposition/ja/infinity/](../exposition/ja/infinity/index.html)（第 0〜8 章、R8 重複調査）が挙げた候補 R1〜R25 を、
全レーン停止後に実施する。停止の合図までは専用 worktree に隔離する。正本はこのファイル。実施記録はコミットメッセージ。候補の番号は解説の番号をそのまま使う。

## 引き継ぎ

### 現在地

- 全レーン停止を 2026-10-23 11:03 に受領。コーディネータの main 基準タグ `stage1-checkpoint-2026-10-23`（`f8df7f77b`）を受領。§8（`c6692be81`）を分担の正本とする。
- `../SerrePositivity-R`、`refactor/r-lane` のバッチはコミット・rebase 後、コーディネータが `6e3cbbcba` を main へ ff-merge 済み。旧 worktree は以後使用しない。
- 0-1・0-2・0-4 はコミット済み。共有ツリーの指定 3 モジュールも復旧・再ビルド済み（1933 jobs、終了コード 0）。
- 0-3、第 1 段、第 5 段の直接置換を実装。互換シムを残さず、重複側を削除して下流 import・名前を更新。
- Core への汎用宣言抽出、F1B 重複除去、Stable の汎用補助 17 モジュールの Core 移動を同じバッチにした。
- 静的検査：参照先不在 import 0、旧 KanSection 名前空間参照 0、Core/F1B の禁止閉包 0、差分空白検査合格。
- Core の対象ビルドは成功（6.62 秒）。抽出 9 宣言の型・証明を含む本文文字列が原本と一致。
- F1/F1B の対象ビルドが成功（3587.87 秒、8187 jobs）。最初の失敗 1128.01 秒と再実行 13.01 秒で判明した import 不足は修正済み。
- Core・F1・F1B・F1/F1B 同時 import・R の 5 監査が全て成功（合計 86.89 秒）。
  F1 16,299 宣言、F1B 4,974 宣言、R の直接参照 139 宣言と移動先 22 モジュールの 196 宣言で標準三公理だけを確認。
  F1B は 1,438 リポジトリ内モジュールを読み、straightening 依存なし。
- 重複検査は 11,702 ファイル、実体の重複 0 群、新規重複対 0（11.11 秒）。
  [検証記録](archive/refactor-ra-validation-2026-10-23.json)・[重複一覧](archive/refactor-duplicates-ra-2026-10-23.md)。完了：2026-10-23 17:45 JST。
- 初回バッチの対象検証には F2・Stable・HomotopyLimits の各集約と全体ビルドを含めなかった。R12 は下記の統合検証を実施。
- main は `6e3cbbcba` を ff-merge 済み。コーディネータの全体ビルドは 18 秒で成功し、ビルド済み olean も反映済み。以後 R-A は main で直接作業し、旧 worktree は使用しない。
- 移動ツールを main に配置・コミット済み。R6・R7・R9 の入口を整え、対象ビルド 6.82 秒、5 監査 82.68 秒、重複検査 10.48 秒で成功。

- R12：F1 の残り 1714 本を役割別サブディレクトリへ移動。追跡済み更新 3153 ファイルは import 置換だけで、型・証明を含む本文を維持。
- `2b8bac842` の `scripts/refactor/verify.sh` で全体ビルド・実行時導出の 2797 対象・24 監査・sorry 閉包を検証。完了 2026-10-24 06:49 JST、最終検証 1499.24 秒。
  直接 sorry 0、新規重複対 0（11704 ファイル、10.53 秒）。[R12 検証記録](archive/refactor-ra-r12-validation-2026-10-24.json)。
- R13・PinchedInterval・scaffold の未完編集は取り消し、準備物を `/tmp/r-a-stopped-scaffold/` 等へ退避。R-C・R-B の再適用完了まで main に書き込まない。

### 残り（依存順）

§4・§8 を参照。R-A は main 取り込み後、移動ツール → R5 前半・R6・R7・R9 の入口 → 第 4 段の R11・R12・R13。第 2〜3 段は R-B/R-C の分担。

### 主要宣言・依存と提供

- 新しい定理を追加しない。宣言の移動先は §5 と保存した対応一覧を参照。
- 所有：本計画、重複検査、R 専用監査、新設 Core モジュール、直接置換の変更。
- 他レーンの変更対象は事前にレーン名・ファイル名・変更種類を報告済み。

### 既知の問題

- `.lake` クローン時に生成中だった 12 ファイルのコピーが失敗したが、Core・F1・F1B の対象ビルドは成功。未使用キャッシュを含む全体検証はコーディネータが行う。
- 重複側と原本の証明項が一致しない例は、原本を無変更で残し重複側を削除。証明の同一性を主張しない。

### 次の一手

- R12 を 1 コミットで報告後、R-C → R-B の main 再適用完了を待つ。その間 R-A は main に書き込まない。R13・PinchedInterval・scaffold は両者の完了後に再開する。
- `scripts/move_module.py` は main に配置済み。一時リポジトリで移動・参照・集約更新を検証済み。以後の担当は §8 の R-A に限定する。
- R11 の 600 本を `F1/Cocartesian/` へ移動し、独立入口を作成。主入口から 490 本が外れ、110 本は主経路から推移的に必要。
  型・証明を含む本文は import 置換を除き全 600 本で一致。不在 import と F1B の禁止閉包は 0。
  対象ビルド 1859.90 秒、4 監査 85.63 秒、重複検査 13.24 秒で全て成功。
  [検証記録](archive/refactor-ra-r11-validation-2026-10-23.json)。完了：2026-10-23 22:41 JST。
- R12（1714 本）は移動・検証済み。R13 の分類案と PinchedInterval 26 宣言・scaffold 19 宣言の一致検証は `/tmp/r-a-*` に保存し、適用は保留する。
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
   R12 は最新のユーザー指示により R-A が `scripts/refactor/verify.sh` で全体ビルド・全監査・sorry 閉包も通す。タグはコーディネータ。
5. 全レーン停止と基準タグは受領済み。初回バッチは main に取り込み済み。以後 R-A だけが main で直接作業する。
   R-B・R-C は専用 worktree を維持し、main への取り込みはコーディネータが行う。
6. 所有範囲と他レーンへの書き込み条件は §8 を正本とする。今後の他レーン変更は (a)(b) に限定する。

## 3. 停止・main への移行・再開（2026-10-23 R-A 分担へ更新）

- 基準：`stage1-checkpoint-2026-10-23`（`f8df7f77b`）。分担の正本：`c6692be81` の §8。
- R-A は main の自分の変更だけを `set -o pipefail` のうえ `git commit --only` で保存する。
  R-B・R-C の worktree は取り込み前に `git rebase main` し、ff-merge はコーディネータが行う。
  他レーンの未コミット作業を巻き込んでコミット・破棄しない。
- R-A は main で直接作業し、互換シムは残さない。`scripts/move_module.py` を配置・コミット済みで、以後の機械的置換に使う。
- R-A の順序：第 0〜1 段＋第 5 段の F1/F1B 重複除去 → R5 前半・R6・R7・R9 の入口 → 第 4 段の R11・R12・R13。
  他レーンの範囲は §8 の (a) 新規ファイル追加、(b) ツールによる import・参照・集約の機械的更新だけ。
- R12 の検証・コミット後は R-C・R-B の再適用完了まで main に書き込まない。R13 は両者の完了後。
- 移動前に移動本数・更新ファイル数・他レーン範囲の更新一覧（レーン名・ファイル名・種類）を報告する。各段の検証結果と所要時間も報告する。
- 期限は **2026-10-25 夜**。終わらない項目は「第 I 段終了時」に戻す。全体ビルドとタグはコーディネータ。

## 4. 段階

分担・実施条件は §8 を優先する。完了欄の「R-A」は Core・F1・F1B・R 監査の対象検証を指し、他レーンの集約や全体ビルドの完了を意味しない。

| 段 | 内容 | 候補 | 触るレーン | 条件 | 完了 |
|---|---|---|---|---|---|
| 0-1 | 正規化ハッシュによる重複検査 `scripts/check_duplicates.py`。現状の一覧を `archive/` に保存 | R8 再発防止 | なし | 即時 | 2026-10-23 09:35 JST |
| 0-2 | `InfinityCategories/README.md`（dg nerve の規約）を `DGNerve/README.md` へ移し、最上位 README を全体地図（層・入口・監査スクリプト）に | R25 | なし | 即時 | 2026-10-23 09:37 JST |
| 0-3 | `F2/JoinRightRelativeRetraction` を削除し、import と F2 公開名を F1 原本へ直接置換 | R8 段階 0 | F1b（10-20 以降未変更） | §3 | |
| 0-4 | 仮定入力の一覧（§6）を grep で作り本計画に固定 | R17・R20 | なし | 即時 | 2026-10-23 09:40 JST |
| 1-1 | `F1/PullbackFiber`・`F1/LeftFiberKan` を汎用部（新 `Core/VertexFiberPullback`・`Core/LeftFiberKan`）と straightening 部（`LeftUnstraighteningFiberIso`・`LeftUnstraighteningFiberKan`、Core を import）に分割 | R8 段階 1 | F1（10-18 以降未変更） | §3 | 2026-10-23 17:45 JST（R-A） |
| 1-2 | 汎用部だけで足りる直接 importer（6 本）を Core 側へ向け直す。下流の import と名前を原本へ直接更新する（旧依存を保つための import は加えない） | R8 段階 2 | F1・F1B・HomotopyLimits・F2 | 1-1 の後、§3 | 2026-10-23 17:45 JST（R-A） |
| 1-3 | F1B の `KanSection*` 重複を削除し原本へ直接置換。現状の宣言数と差分を再検証し、独自内容だけを残す | R8 段階 3 | F1b（10-19 以降未変更） | 1-2 の後（F1B 監査が原本の閉包を通すため） | 2026-10-23 17:45 JST（R-A） |
| 1-4 | `Core/Fibrations.lean`・`Core/MappingSpace.lean` の入口（定義は動かさず import と docstring で目次化）、R6 は `F1/Fibrations.lean` | R6・R7・R9 | なし | 即時 | 2026-10-23 22:05 JST |
| 1-5 | `Stable/SliceOpposite` の `sliceOverOpIso` を `Core/SliceOpposite` へ移し、旧ファイルを削除・参照を直接更新 | R5 の前半 | D（10-18 以降未変更） | §3 | 2026-10-23 17:45 JST（Core・R-A 対象。Stable 集約は R-B） |
| 2-1 | `Stable/Cocone`・`UniverseLimits`・`ColimitDiagramIso`・`Definition` の `HasFiniteLimits` を `Core/Colimit*` へ（旧ファイルを削除して直接置換） | R2・R22 | D | D-7 d 完了直後 | |
| 2-2 | `Stable/AdjunctionHomotopyCategory` を `F1B/AdjunctionHomotopyCategory` へ | R14 | D・F1b | 2-1 と同時 | |
| 2-3 | `Derived/LimitDiagramIso`・`CofinalLimitExistence` を Core へ、`Localization*Criterion`・`DeformationLocalization` を F1B へ | R23 | D・F1b | D の区切り | |
| 2-4 | `KST/SConstruction/VertexPrescribedExtension`・`KST/LocalizingInvariants/LimitProjectionExistence` の内容を Core へ移し KST の旧ファイルを削除して直接置換。Stable → KST の import を解消 | R3 | K-S•・Sp・D | 三レーンの区切り | |
| 2-5 | `DGNerve/SemifreeLimits` を Derived（または DifferentialGraded）へ、DGNerve の旧ファイルを削除して直接置換 | R24 | D | D の区切り | |
| 2-6 | `F2/Ind/ElementsDiagram` の密度定理を F1 の前層の層へ | R15 | F1 | F1-7 完了後 | R-C：d5cd974e2、密度59本・補助81本適用、verify.sh・関係監査通過 |
| 2-7 | `F2/SpaceLimitShapes` の条件付き版を無条件定理の系に（3 ファイル） | R17 | F1b | a7 完了・差し替えと同時 | R-C：bdf8d1c6a 適用、verify.sh・関係監査通過 |
| 2-8 | `HomotopyLimits/Local*`・`Sigma*`・`Sifted*` を `F2/Presentable/` へ | R16 | N・P | P-1 f・g 完了後 | R-C：ba39c0897、90本適用、verify.sh・関係監査通過 |
| 3-1 | その他の完全一致・準重複：`F2/JoinRight*`↔`F1/JoinDiagramRight*`、Stable↔KST 4 組、`Derived/DGCommaAug*`↔`DGModuleAugmentation*` 17 組、EInfinity 19 組、HomotopicalAlgebra 8 組 | R8 §3 | F1b・K-S•・D・E2 | 各レーンの区切り | |
| 3-2 | `PinchedInterval` 6 本・`KanScaffold`／`KanCocartesian` 15 本の精査 | R8 段階 4 | F1b | F1b-5 a7 完了後 | |
| 4-1 | 休止中の Cat∞ 値 straightening `F1/Cocartesian*`（3.7 万行）を `F1/Cocartesian/` へ移し集約から外す | R11 | F1 | R-A、直接置換・入口の検証後 | 2026-10-23 22:41 JST |
| 4-2 | F2 最上位を `F2/CatInfinity/`（完成）と `F2/FilteredExchange/`（作業中）へ | R19 | F1b | a7 完了後 | R-C：65c0881c8、2,210本適用、verify.sh・関係監査通過 |
| 4-3 | F1 のサブディレクトリ化、F1B の `Kan*` 接頭辞の整理、ディレクトリ名の層への対応 | R12・R13・R1・R6 | F1・F1b | R-A、R11 の後 | R12：2026-10-24 06:49 JST。R13 は R-C・R-B 完了後 |
| 5 | 旧重複モジュールの削除と `KanSection.foo` → `foo` の直接置換（約 60 箇所）、`HomotopyLimits.lean` の docstring と `quillenCfBottomEndpoint_wrong` 等の改名 | R18 ほか | 全レーン | 第 0〜1 段と同時（全停止後） | 2026-10-23 17:45 JST（F1/F1B 部分。HomotopyLimits は R-C） |

## 5. 移動した宣言の所在

| 旧所在（削除・改名） | 新所在 | 段 | コミット |
|---|---|---|---|
| F1/PullbackFiber・LeftFiberKan の汎用部 | Core/VertexFiberPullback・LeftFiberKan | 1-1 | 本バッチ（R-A 対象検証済み、2026-10-23 17:45 JST） |
| F1/ScaffoldFiniteVerticalEdges の prism・LeftStrictTransport の under map | Core/PrismVerticalSimplex・NerveUnderMap | 1-3 | 同上 |
| F1/PullbackNerveFiber・ScaffoldUnderChain | Core/VertexFiberNervePullback・F1B/ScaffoldUnderChain | 1-3 | 同上 |
| F1B/KanSection 重複群・F2/JoinRightRelativeRetraction | F1 原本または新 Core（[全対応一覧](archive/refactor-direct-batch-2026-10-23.json)） | 0-3・1-3・5 | 同上 |
| Stable/SliceOpposite と join/reverse 汎用補助 16 本 | Core の同名モジュール | 1-5 | 同上 |


R-C の main 再適用（2026-10-24、verify.sh・関係監査通過）：

| 旧所在 | 新所在 | 項目 | コミット |
|---|---|---|---|
| F2 最上位の2,210本 | F2/CatInfinity・FilteredExchange（[計画](archive/r-c-main-2026-10-24/r19.json)） | R19 | 65c0881c8 |
| HomotopyLimits の Local*・Sigma*・Sifted* 90本 | F2/Presentable（[計画](archive/r-c-main-2026-10-24/r16.json)） | R16 | ba39c0897 |
| F2/Ind の前層密度59本・F2 の一般補助81本 | F1/Yoneda/PresheafDensity と Support（[計画](archive/r-c-main-2026-10-24/r15.json)） | R15 | d5cd974e2 |
| EInfinity の完全一致3宣言・bar の output | HomotopyWeight/DoubleOpposite・BarOutput（型と本文を保存） | R8 完全一致部 | a6a10c52b |
| HomotopicalAlgebra/HomotopyFunctionComplex の267転送入口 | Rectification へ直接 import（[計画](archive/r-c-main-2026-10-24/redirect-267.json)、[閉包証拠](archive/r-c-main-2026-10-24/redirect-267-closure.json)） | 追加項目 | d2385ea7e |

型の異なる準重複の実施は所有レーン再開後の判断。HomotopicalAlgebra は現存6組の全調査として確定。[一覧](archive/refactor-near-duplicates-einfinity-2026-10-23.md)を参照。UniverseSSetMaps と Stable 補助6本の移動は R-B に残した。


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

Derived の一般宣言14組の旧名→正本名は [対応表](archive/refactor-r-b-derived-name-map.json)。所在は `DGNerve/AugmentationCombinatorics`（13宣言）と `DGNerve/VertexIdentity`（1宣言）。8重複モジュールを削除。

新規共通 Prop 補題 `augmentation_proof_of_endpoint_phases`・`augmentation_proof_of_reindex_cases` は `Derived/AugmentationProofCases`。既存4定理の型を保持し、証明だけを source commit `1a412f887a63d14b73fed3fd0f2af52207a6f25e` の cherry-pick で共有した。データ86宣言の本体は名前置換以外を保持。型依存データ19組は [差分表](archive/refactor-near-duplicates-derived-2026-10-23.md) に保存し、Dレーン再開後の判断へ保留する。

全 JSON と適用ログは [再適用計画](archive/refactor-r-b-reapply-2026-10-23/manifest.json)。R23 の CofinalLimitExistence は型の閉包に従い F1B に配置。ZeroBoundaryExtension は InitialExtension・一般 InitialOpposite と同時に Core へ移し、Core→Stable と Stable→KST を残さない。

## 6. 仮定入力の一覧（完成後に外す）

2026-10-24、`rg -n '\b(IndFiniteLimitExchangeInput|CoherentFilteredLimitExchangeShape|HasSpaceLimitsOfShape|DGKappaConeInput|DGKappaPerfectInput)\b' SerrePositivity --glob '*.lean'` で採取。
使用は定義行・import 行を除く一致行数（同じ行の複数出現は 1、証拠を供給する定理も含む）。
作業ツリーの未追跡ファイルも走査した。定義と使用の行一覧は
[更新一覧](archive/refactor-assumptions-r-c-main-2026-10-24.md)（[初期一覧](archive/refactor-assumptions-2026-10-23.md)） を参照。

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

## 8. 並列化（2026-10-23 11:15、ユーザー決定：全レーン停止中にリファクタリングを先に完了する）

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
