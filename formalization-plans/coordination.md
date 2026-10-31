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
| BS | 人が主導の別セッション | [bhatt-scholze/](bhatt-scholze/) | — | 論文の層の区切り 2a・2b で時間を合わせる |

連絡はすべてユーザーが貼り付けで中継する。Codex への指示は指示書の追記（§番号）で出し、短い引き渡し文を添える。

## 2. ビルドの規則

1. 全ビルド（ルート・監査対象・verify・束の下流ビルド）は**機械で一つずつ**。始める前に `ps -axo command= | grep '[l]ake build'` で他の全ビルドがないことを確かめる。道具 `scripts/refactor/with_build_lock.sh`（DG-W2(a) で作成、infra/dg-w2）が main に入ったら必ず経由する。
2. 束の途中は触ったモジュールだけ `lake build <module>`。下流の全ビルドは束の最後に一回。
3. 取り込みの直後に main の `.lake/build` を温める（取り込んだ worktree から rsync。`scripts/refactor/warm_build_dir.sh`）。他の worktree は main から複製する。終了コード 23・24 は、消えたのが書き換え中の出力だけなら受け入れる。
4. verify は `VERIFY_JOBS=3`（最長の監査が RSS 19 GB）。中間の確認には `VERIFY_CACHE=1`（gate:false）を使ってよい。
5. 土台（HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・DG の Complexes/Category/Module/Functor）に触る変更は、下流ほぼ全部（約 9,000〜20,000 本、単独で 3〜8 時間）を再ビルドする。これを起こす変更は窓ごとに一束。
6. 実測（[verify-build-costs の記録](dg-cleanup-plan.md#5a-再ビルドの費用と規則2026-10-30dg-w1-の実測から)）：DG-W1 の土台 6 本の import 書き換えで 11,250 本・6 時間 57 分（3 セッション同時）、verify 1 時間 49 分。

## 3. 暦（順番待ち）

| # | 作業 | 機械 | 前提 | 状態 |
| --- | --- | --- | --- | --- |
| 1 | main の全ビルド（区切り 1-3 ＋ DG-W1 の後の温め） | 2 時間 09 分（27,854 ジョブ、新規 10,114、エラー 0） | — | **完了**（10-31 19:17〜21:26） |
| 2 | ∞ の束：main を取り込み → `.lake/build` を複製 → before snapshot（対象 1,276 本の閉包）→ R75・R79・W1・W2a を適用（停止点 1）→ 下流ビルド 約 20,000 本（6〜8 時間）→ 保存検査（停止点 2）→ verify（停止点 3） | 約 10 時間 | #1。凍結：HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・InfinityCategories・KST・EInfinity・ルート・それらの監査への他の取り込みを止める | **合図済み（10-31 21:30）** |
| 3 | ∞ の束を main へ取り込み、main を温める（ifw0-3 から rsync） | 数分 | #2 PASS | — |
| 4 | DG-W2(b)：main を取り込み → 複製 → D3 の move ＋ 土台でない 9 ディレクトリの統合 ＋ D5 → 内部検証（統合先だけビルド＋保存検査）→ 下流ビルド 約 7,200 本（2〜3 時間）→ verify | 約 4 時間 | #3。統合先の名前は承認済み | 待ち（#3 の後に合図） |
| 5 | DG-W2(b) を main へ取り込み、main を温める | 数分 | #4 PASS | — |
| 6 | 論文の層の区切り 1-4（KTheory・Asymptotic・Paper の再構成、Perfect の 3 宣言を HA へ、`Asymptotic/DGVerdier/` を含める） | 先方のビルド＋verify | #5（DGVerdier が Asymptotic に入ってから） | 先方が準備中（凍結中は main にコミットしない） |
| 7 | DG-W3：土台 5 ディレクトリの統合＋残りの D5（Paper の経路 326 本まで再ビルド） | 約 5 時間 | #6（Paper の再構成の後） | 未作成 |
| 8 | IF-W2a-2（R76・R77・R67）、IF-W0-4（layers.json 登録、runner のメモリ予算） | 束の後 | #3 | 未作成 |
| 9 | 論文の層の区切り 2a・2b（BS の区切りに合わせる） | 先方 | BS の区切り | 先方 |

## 4. いまの待ち条件（10-31 夜）

- ∞ Codex：10-31 21:30 に「main が温まった」を合図。#2 を実施中（複製 → snapshot → 適用＝停止点 1 → 下流ビルド → 停止点 2 → verify → 停止点 3）。
- DG Codex：e14680ad0 で待機。合図「(b) を始めてよい」で #4 を開始。
- 論文の層：区切り 1-4 の準備中。凍結は 10-31 21:30 から（∞ Codex が main を取り込んで束を適用する時点）、終了は #3 のとき伝える。main でのビルドも #3 まで控える。R79 の案内 2 本の削除と README の表の更新は #3 の後。
- （10-31 決定・実施済み 4eb1f4d6b）main の未追跡 WIP 6 本は `SerrePositivity/Archive/WIP/` に追跡して元の場所から消した（README に由来）。∞ の束の R75 の段で `audit_kst_spectra_s3`・`d3tail` の名前一覧から旧名 4 本を外す。
- （10-31 決定）調整役の交代は今はしない。#5（DG-W2(b) の取り込み）の後に §6 の目安で再判断。

## 5. 逸脱の記録

- 10-31：main の温め（#1）の後、`scripts/audit/dg.lean` は走らせていない（Checks/ の 300 本がルートの閉包外で未ビルドのため。verify の監査対象ビルドで作られる）。∞ の束の verify で確認する。

- 10-31：DG-W1 の取り込み（194a65110）は、区切り 1-3 の後の merge で、merge 後の状態に全 verify を行っていない（領域が重ならず、重なりはルートの import 行だけ）。main の全ビルド（#1）と ∞ の束の verify（#2）で確認する。

## 6. 調整役の引き継ぎ

調整の状態は本書と各計画・指示書・メモリ（`~/.claude/projects/.../memory/`）に全部ある。交代するときは：
1. 本書 §3・§4 を最新にする（調整役）。
2. 新しい調整役は本書 → 各計画の「状態」節 → 指示書の末尾の追記（§10.x など）→ メモリの順に読む。
3. 進行中の合図（誰が何を待っているか）は §4 だけを信じる。会話の記憶は使わない。
