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

- なし。

### 既知の問題

- なし。

### 次の一手

- 0-3：F2/JoinRightRelativeRetraction の §3 条件を確認し、F1 原本へのシムにする。

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
5. 稼働中レーンの集約ファイル（`F1.lean`・`F1B.lean`・`F2.lean`・`Stable.lean`・`Derived.lean`・`HomotopyLimits.lean`・`KST/*.lean`）と
   監査スクリプトは R が編集しない。必要な一行は、コーディネータ経由でそのレーンに依頼する。

## 3. 他レーンのファイルに触る条件と手順

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
| 0-4 | 仮定入力の一覧（§6）を grep で作り本計画に固定 | R17・R20 | なし | 即時 | |
| 1-1 | `F1/PullbackFiber`・`F1/LeftFiberKan` を汎用部（新 `Core/VertexFiberPullback`・`Core/LeftFiberKan`）と straightening 部（旧名、Core を import）に分割 | R8 段階 1 | F1（10-18 以降未変更） | §3 | |
| 1-2 | 汎用部だけで足りる直接 importer（6 本）を Core 側へ向け直す。閉包が縮む外部ファイルには旧 import を保守的に残す | R8 段階 2 | F1・F1B・HomotopyLimits・F2 | 1-1 の後、§3 | |
| 1-3 | F1B の `KanSection*` 31 本のうち本体同一の分（126 宣言、1,660 行）をシム化。`KanSectionPrism` と中継 1 本は残す | R8 段階 3 | F1b（10-19 以降未変更） | 1-2 の後（F1B 監査が原本の閉包を通すため） | |
| 1-4 | `Core/Fibrations.lean`・`Core/MappingSpace.lean` の入口（定義は動かさず import と docstring で目次化） | R7・R9 | なし | 即時 | |
| 1-5 | `Stable/SliceOpposite` の `sliceOverOpIso` を `Core/SliceOpposite` へ（Stable 側シム） | R5 の前半 | D（10-18 以降未変更） | §3 | |
| 2-1 | `Stable/Cocone`・`UniverseLimits`・`ColimitDiagramIso`・`Definition` の `HasFiniteLimits` を `Core/Colimit*` へ（Stable 側シム） | R2・R22 | D | D-7 d 完了直後 | |
| 2-2 | `Stable/AdjunctionHomotopyCategory` を `F1B/AdjunctionHomotopyCategory` へ | R14 | D・F1b | 2-1 と同時 | |
| 2-3 | `Derived/LimitDiagramIso`・`CofinalLimitExistence` を Core へ、`Localization*Criterion`・`DeformationLocalization` を F1B へ | R23 | D・F1b | D の区切り | |
| 2-4 | `KST/SConstruction/VertexPrescribedExtension`・`KST/LocalizingInvariants/LimitProjectionExistence` の内容を Core へ移し KST 側シム。Stable → KST の import を解消 | R3 | K-S•・Sp・D | 三レーンの区切り | |
| 2-5 | `DGNerve/SemifreeLimits` を Derived（または DifferentialGraded）へ、DGNerve 側シム | R24 | D | D の区切り | |
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

| 旧所在（シム） | 新所在 | 段 | コミット |
|---|---|---|---|
| | | | |

## 6. 仮定入力の一覧（完成後に外す）

0-4 で作る。列：構造体／述語名、所在、供給元（レーン・小項目）、使用箇所の数。

| 名前 | 所在 | 供給元 | 使用 |
|---|---|---|---|
| `IndFiniteLimitExchangeInput` | F2/Ind | F1b a7 | |
| `CoherentFilteredLimitExchangeShape` | F2 | F1b a7 | |
| `HasSpaceLimitsOfShape` | F2/SpaceLimitShapes | 無条件化済み（R17） | 3 |
| `DGKappaConeInput`・`DGKappaPerfectInput` | KST/NonConnective | D（K-7 供給） | |

## 7. 再発防止（foundations.md §8 に追加済み、ユーザー承認 10-23 09:33）

- 必要な補題が禁止された import 閉包にある場合は、コピーせず、上流ファイルの分割をコーディネータ経由で所有レーンに依頼する。
- モジュールの移動・改名は旧モジュール名を互換シムとして残し、下流の import と宣言名を壊さない。削除は第 I 段終了時にまとめて行う。
- `scripts/check_duplicates.py` を全体ビルドの監査に加え、完全一致の組が増えたら報告する。
