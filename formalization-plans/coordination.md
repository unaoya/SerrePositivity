# 三つのレーンの調整（2026-10-31 新設）

概要：∞ 基盤（Codex）・DG の整理（Codex）・論文の層の整理（Claude Code）の三つの作業を、一人の調整役（Claude、長い会話）が管理するための正本。原則、レーン、ビルドの暦（順番待ち）、いまの待ち条件、引き継ぎの手順を置く。
方針：**ビルドは減らし、機械で同時に走らせない。** 下流の再ビルドを起こす変更はレーンごと・窓ごとに一束にし、全ビルドと verify は束の最後に一回。全ビルドは暦の順番で一つずつ。取り込みのたびに main の `.lake/build` を温め、他の worktree はそこから複製する。
規約：各レーンの計画と指示書が細部の正本。本書は順序・待ち条件・連絡の正本で、状態の表は調整役が更新する。日付は絶対表記。
使われ方：調整役が毎回ここを見て次の合図を出す。調整役を交代するときは §6 の手順で引き継ぐ。

## 1. レーン

| レーン | 実施 | 計画 | 指示書 | worktree／ブランチ |
| --- | --- | --- | --- | --- |
| ∞ 基盤 | Codex（∞） | [infinity-foundation-plan.md](infinity-foundation-plan.md) | [IF-W0-3 §10.12〜10.16](infinity-codex-w0-3.md)、`targets/batch-w1w2a.md` | `../SerrePositivity-ifw0-3`、`infra/if-w0-3` |
| DG の整理 | Codex（DG） | [dg-cleanup-plan.md](dg-cleanup-plan.md) | [DG-W2](dg-codex-w2.md) | `../SerrePositivity-dgw1`、`infra/dg-w2` |
| 論文の層 | Claude Code（別セッション、自分で実装） | [refactor-plan.md](refactor-plan.md) | 先方が自分で管理。伝達文 [handover-ct-to-infinity](handover-ct-to-infinity-2026-10-30.md) §8〜§10 | main で作業（凍結中は worktree） |
| BS | 人が主導の別セッション。**当面動かさない**（11-02 ユーザー決定：三つの整理が終わってから必要なら再開）。統合は BS-W1〜W9 で完了済み（10-26） | [bhatt-scholze/](bhatt-scholze/) | — | 休止中。論文の層の 2a・2b は BS の区切りを待たずに暦に入れてよい（`BhattScholze/`・`CLMST/` を動かすが、編集者がいないので衝突しない） |

連絡はすべてユーザーが貼り付けで中継する。Codex への指示は指示書の追記（§番号）で出し、短い引き渡し文を添える。

## 2. ビルドの規則

1. 全ビルド（ルート・監査対象・verify・束の下流ビルド）は**機械で一つずつ**。始める前に `ps -axo command= | grep '[l]ake build'` で他の全ビルドがないことを確かめる。道具 `scripts/refactor/with_build_lock.sh`（DG-W2(a) で作成、infra/dg-w2）が main に入ったら必ず経由する。
2. 束の途中は触ったモジュールだけ `lake build <module>`。下流の全ビルドは束の最後に一回。
3. **Lake の成果物キャッシュを全セッションで共有する（11-01 採用、Mathlib の cache と同じ仕組みのローカル版）。** `~/.zshenv` で `LAKE_ARTIFACT_CACHE=true`・`LAKE_RESTORE_ARTIFACTS=true`・`LAKE_CACHE_DIR=~/.cache/lake` を設定済み。入力（ソースと依存）のハッシュが同じ成果物は、どの worktree で作っても他の worktree の `lake build` が再コンパイルなしで使う（`RESTORE` で `.lake/build` にも復元されるので `lake env lean` の監査もそのまま動く）。
   - 既存の `.lake/build` の中身はキャッシュに入らない。効き始めるのは、この設定の後に `lake build` で作った分から。各 Codex は新しい shell を開くか `source ~/.zshenv` してから `lake` を使う（`lake env | grep LAKE_ARTIFACT_CACHE` で確認）。
   - 古い版が溜まるので、窓の区切りで `lake cache clean`（全消去）か、ディスクを見て判断する。
   - rsync の温め（`warm_build_dir.sh`）は、キャッシュに入っていない成果物が要るときの予備に格下げ。
4. verify は `VERIFY_JOBS=3`（最長の監査が RSS 19 GB）。中間の確認には `VERIFY_CACHE=1`（gate:false）を使ってよい。
5. 土台（HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・DG の Complexes/Category/Module/Functor）に触る変更は、下流ほぼ全部（約 9,000〜20,000 本、単独で 3〜8 時間）を再ビルドする。これを起こす変更は窓ごとに一束。
6. 実測（[verify-build-costs の記録](dg-cleanup-plan.md#5a-再ビルドの費用と規則2026-10-30dg-w1-の実測から)）：DG-W1 の土台 6 本の import 書き換えで 11,250 本・6 時間 57 分（3 セッション同時）、verify 1 時間 49 分。

## 3. 暦（順番待ち）

| # | 作業 | 機械 | 前提 | 状態 |
| --- | --- | --- | --- | --- |
| 1 | main の全ビルド（区切り 1-3 ＋ DG-W1 の後の温め） | 2 時間 09 分（27,854 ジョブ、新規 10,114、エラー 0） | — | **完了**（10-31 19:17〜21:26） |
| 2 | ∞ の束：main を取り込み → `.lake/build` を複製 → before snapshot（対象 1,276 本の閉包）→ R75・R79・W1・W2a を適用（停止点 1）→ 下流ビルド 約 20,000 本（6〜8 時間）→ 保存検査（停止点 2）→ verify（停止点 3） | 約 10 時間 | #1。凍結：HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・InfinityCategories・KST・EInfinity・ルート・それらの監査への他の取り込みを止める | **完了**（11-01：下流ビルド 11 round、補充 83 import、禁止閉包 177 → 166、保存比較 16,412 件一致、verify 100／100） |
| 3 | ∞ の束を main へ取り込み、main を温める | 数分（Lake キャッシュから復元） | #2 PASS | **完了**（11-01 夜、merge。温めはキャッシュからの `lake build`） |
| 4 | DG-W2(b)：main を取り込み → 複製 → D3 の move ＋ 土台でない 9 ディレクトリの統合 ＋ D5 → 内部検証（統合先だけビルド＋保存検査）→ 下流ビルド 約 7,200 本（2〜3 時間）→ verify | 約 4 時間 | #3。統合先の名前は承認済み | **完了**（11-02 昼：D3 move 33・D4 979 → 78・D5、下流 5,750 本 85 分、保存比較 PASS（個別照合 393・未説明 0）、verify 100／100） |
| 5 | DG-W2(b) を main へ取り込み、main を温める | 数分（キャッシュ） | #4 PASS | **完了**（11-02 昼、merge） |
| 6 | 論文の層の区切り 1-4（KTheory・Asymptotic・Paper の再構成、Perfect の 3 宣言を HA へ、`Asymptotic/DGVerdier/` を含める） | 先方の全体ビルド＋verify | #5 の後に**編集と直接 importer までの小さなビルド**は始めてよい（worktree で）。**全体ビルドと verify は #8a（∞ の束）が main に入った後**（11-02 改訂：順序を #8a → #6 に。∞ の束は今日 3〜5 時間、1-4 の全体ビルドは明朝） | 先方が準備完了・時刻待ち |
| 7 | DG-W3：土台 5 ディレクトリの統合（48 統合先・608 元）＋残りの D5＋層の仕上げ（PerfectComplex の例外を外す、126 本の一覧） | 下流約 16,300 本、単独 4.5〜7 時間＋verify | #6（1-4 の後） | 指示書 作成済み（11-02）：[DG-W3](dg-codex-w3.md)。**事前の静的検査は完了**（11-02 夕、`ef951fa5d`：名前解決の候補 4 箇所・universe 608/608・最大 1,621 行。回答は §7）。開始は 1-4 の後に合図 |
| 8 | IF-W0-4（完了）→ **IF-W2a-2（R76・R77・R67、下流 11,888 本 1 回）：#5 の直後、1-4 の全体ビルドより先** | IF-W0-4 はほぼビルドなし、IF-W2a-2 は全ビルド 1 回＋verify | #3（IF-W0-4）、IF-W0-4 と DG-W2(b) の後（IF-W2a-2） | **IF-W0-4 完了・取り込み済み**（11-01 夜、bddb9b570：Foundation 103 本・違反 0、runner のメモリ予算。初回は全件未計測で 2 並列・監査 44 分、次回から実測値で並列化）。IF-W2a-2 は草案（停止点 1）を先に、束のビルドは DG-W2(b) の後 |
| 9 | 論文の層の区切り 2a・2b（CA の perfectoid 部分を BS へ、CLMST の分離、DerivedCompletion 第二層） | 先方の全ビルド 1 回ずつ | BS は休止中なので時期は自由。他の全ビルドと重ねない | 先方。準備は 1-4 の後 |

## 4. いまの待ち条件（10-31 夜）

- ∞ Codex：IF-W2a-2 の草案 28767dee9。11-02 昼に「束を始めてよい」を合図（main を取り込むと DG の `universe` 修正 7e1fb1dea と proof-irrelevant の道具が入る）。
- DG Codex：DG-W2(b) 完了・取り込み済み。DG-W3 の指示書と事前の静的検査（`ef951fa5d`、回答 [DG-W3 §7](dg-codex-w3.md)）まで済み。**1-4 が main に入ったら Claude が開始を合図**。それまでビルドなし。
- 論文の層：凍結解除済み。案内 2 本の削除と README の表の更新は完了（99b57430b、Lean に変更なし）。1-4 の準備をビルドなしで進行中（群の定義・循環の確認・docstring の下書き。DGVerdier の群は DG-W2(b) の後に決める）。1-4 の取り込みとビルドは DG-W2(b)（#4・#5）の後に Claude が時刻を伝える。
- （10-31 決定・実施済み 4eb1f4d6b）main の未追跡 WIP 6 本は `SerrePositivity/Archive/WIP/` に追跡して元の場所から消した（README に由来）。∞ の束の R75 の段で `audit_kst_spectra_s3`・`d3tail` の名前一覧から旧名 4 本を外す。
- （11-01 実施）`~/.zshenv` に Lake キャッシュの 3 変数を設定（ユーザー）。使い終わった worktree `ifw0-1`・`ifw0-2` を削除（ブランチ `infra/if-w0-1`・`if-w0-2` は残してある。パッチは main に取り込み済み）。空き 344 → 447 GB。
- （10-31 決定）調整役の交代は今はしない。#5（DG-W2(b) の取り込み）の後に §6 の目安で再判断。

## 5. 逸脱の記録

- 11-01：∞ の束の停止点 3 で、監査 2 本（`audit_homotopy_limits`・`audit_infinity_f2`）の import が束で動かした定義に届かず FAIL（他の 98 本は成功）。import を直した後の再検証は `VERIFY_CACHE=1`（gate:false）で、成功済みの 98 本はキャッシュの鍵（本文と閉包の olean ハッシュ）が同一なので当たり、2 本だけ実行する。この束ではこれを合否とする（IF-W0-3 §10.36）。

- 10-31：main の温め（#1）の後、`scripts/audit/dg.lean` は走らせていない（Checks/ の 300 本がルートの閉包外で未ビルドのため。verify の監査対象ビルドで作られる）。∞ の束の verify で確認する。

- 10-31：DG-W1 の取り込み（194a65110）は、区切り 1-3 の後の merge で、merge 後の状態に全 verify を行っていない（領域が重ならず、重なりはルートの import 行だけ）。main の全ビルド（#1）と ∞ の束の verify（#2）で確認する。

## 6. 調整役の引き継ぎ

調整の状態は本書と各計画・指示書・メモリ（`~/.claude/projects/.../memory/`）に全部ある。交代するときは：
1. 本書 §3・§4 を最新にする（調整役）。
2. 新しい調整役は本書 → 各計画の「状態」節 → 指示書の末尾の追記（§10.x など）→ メモリの順に読む。
3. 進行中の合図（誰が何を待っているか）は §4 だけを信じる。会話の記憶は使わない。
