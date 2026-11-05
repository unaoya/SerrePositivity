# 調整（段階 II）

作成：2026-11-05（整理の期間の調整役が書き直した）。整理の期間（段階 I、10-31〜11-05）の暦・待ち条件・経過は [archive/coordination-stage-i.md](archive/coordination-stage-i.md)。
**段階 II の正本は [段階 II の計画](stage-ii-plan-draft.md)**（11-05 夜に確定）。本書はその運用の規則と、各レーンの現状だけを持つ。

## 1. レーン

段階 II のレーンは計画の §5.1 で確定した（11-05 夜）。開始文は調整役が書き、どれにも「F-2 の改名表 `scripts/refactor/targets/f-namespace-map.json`」「main を取り込んでから始める」「本書 §2 の規則」を入れる。

| レーン | 道具 | 担当 | worktree・枝 | 入口 | 検収 |
| --- | --- | --- | --- | --- | --- |
| 調整役 | Claude Code | 暦・合図・取り込み、∞・K・BS の検収、BS の設計（drafts・指示書・design-status。BS 設計のチャットは置かない、11-05 夜） | main | 計画・本書・`bhatt-scholze/design-status.md` §0 | — |
| ① ∞ 中核 | Codex | M1・M2・M7・M8、L4 | `SerrePositivity-inf-core`・`math/inf-core` | [stage-ii/inf-core-w1.md](stage-ii/inf-core-w1.md) | 調整役 |
| ③ ∞ 供給 | Codex | G8 の四角形 → G14・G9・G10・G8 の一般形 | `SerrePositivity-inf-supply`・`math/inf-supply` | [stage-ii/inf-supply-w1.md](stage-ii/inf-supply-w1.md) | 調整役 |
| ⑤ BS 実装 | Codex | BS-W11 → drafts の移植 | `SerrePositivity-bs-impl`・`math/bs-impl`（一度に一つ） | `bhatt-scholze/bhatt-scholze-codex-w11.md` | 調整役 |
| ⑥ スキーム論 | Codex | 公理 (3) の再確認 → スキーム論の土台（A・B 共通、計画 §1.5）、BS17 Thm 4.1 (i) まで | `SerrePositivity-scheme`・`math/scheme` | [stage-ii/scheme-w1.md](stage-ii/scheme-w1.md) | 調整役 |

後から足すもの（②④⑦、K 理論）と開く条件は計画の §5.1。

## 2. ビルドの規則

1. 全ビルド（ルート・監査対象・verify・束の下流ビルド）は**機械で一つずつ**。始める前に `ps -axo command= | grep '[l]ake build'` で他の全ビルドがないことを確かめる。道具 `scripts/refactor/with_build_lock.sh`（DG-W2(a) で作成、infra/dg-w2）が main に入ったら必ず経由する。
2. 束の途中は触ったモジュールだけ `lake build <module>`。下流の全ビルドは束の最後に一回。
3. **Lake の成果物キャッシュを全セッションで共有する（11-01 採用、Mathlib の cache と同じ仕組みのローカル版）。** `~/.zshenv` で `LAKE_ARTIFACT_CACHE=true`・`LAKE_RESTORE_ARTIFACTS=true`・`LAKE_CACHE_DIR=~/.cache/lake` を設定済み。入力（ソースと依存）のハッシュが同じ成果物は、どの worktree で作っても他の worktree の `lake build` が再コンパイルなしで使う（`RESTORE` で `.lake/build` にも復元されるので `lake env lean` の監査もそのまま動く）。
   - 既存の `.lake/build` の中身はキャッシュに入らない。効き始めるのは、この設定の後に `lake build` で作った分から。各 Codex は新しい shell を開くか `source ~/.zshenv` してから `lake` を使う（`lake env | grep LAKE_ARTIFACT_CACHE` で確認）。
   - 古い版が溜まるので、窓の区切りで `lake cache clean`（全消去）か、ディスクを見て判断する。
   - rsync の温め（`warm_build_dir.sh`）は、キャッシュに入っていない成果物が要るときの予備に格下げ。
   - **掃除（11-02 決定）**：`lake cache clean` は空きが 150 GB を切ったときだけ、全ビルドのない時刻に、全 worktree が温まった状態で行い、直後に main で `lake build` を走らせて現行の成果物を登録し直す。定期的な掃除はしない（11-02：22 GB・331,250 本、空き 455 GB）。
4b. **main の作業木の規則（11-04 決定、事故の後）**：main の作業木では Lean の編集もビルドもしない（取り込みと温めは Claude だけ）。main に直接コミットするセッション（BS の記録など）は、必ず `git commit --only <自分のファイル>` で、`git add -A`・`git commit -a` を使わない。11-04 に B4 の未コミットの削除（`Pair/Tower.lean`）が BS の記録コミット 38e6d889a に巻き込まれ、babef8b23 で復元した。
4a. **小さなビルドの規則（11-02 19:40 決定）**：変更したファイルと直接の importer までの小さなビルド（数百本以下）は、**下流ビルド・verify が走っていなければ合図なしで行ってよい**。確認は `ps -axo command= | grep "[l]ake build"` が空であることと、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること（取れなければ待つ）。下流・verify の時間帯（暦 §3）には行わない。全ビルド（下流・verify）は従来どおり暦と合図。
4. verify は `VERIFY_JOBS=3`（最長の監査が RSS 19 GB）。中間の確認には `VERIFY_CACHE=1`（gate:false）を使ってよい。
5. 土台（HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・DG の Complexes/Category/Module/Functor）に触る変更は、下流ほぼ全部（約 9,000〜20,000 本、単独で 3〜8 時間）を再ビルドする。これを起こす変更は窓ごとに一束。
6. 実測（[verify-build-costs の記録](dg-cleanup-plan.md#5a-再ビルドの費用と規則2026-10-30dg-w1-の実測から)）：DG-W1 の土台 6 本の import 書き換えで 11,250 本・6 時間 57 分（3 セッション同時）、verify 1 時間 49 分。

## 3. 暦

全ビルド（下流・verify）の予定はまだない。各レーンの最初の束が見えたところで書く。

| 時期 | 内容 |
| --- | --- |
| 11-06〜 | ①③⑤⑥の開始。小さなビルドは §2-4a |
| ③の G8 の四角形の取り込み | BS に知らせる（S4 の生成辺）。④を開く |
| 段 G の最初の区切り（目安 12 月上旬） | 保守の束：L1（F-2 の deprecated alias の一括削除）・L2（旧 G8 の削除）。BS・③・KST が新しい名前へ移ったのを確かめてから。担当は①か② |
| ①の M1・M2・M7 の取り込み | L4（分数の一般版）を①の中で。K 理論レーン（B-3〜）を開く |
| ②を開くとき | L3（M16） |
| 余裕のあるとき・該当部分を触るとき | L5（台帳 R60 の大きな処置、R78）、L6（DG の D6〜D8、Asymptotic の商） |

## 4. 各レーンの現状

段階 I のレーン（すべて閉じた）と段階 II のレーン：

| レーン | 状態 |
| --- | --- |
| ∞ 整理（Codex） | 閉じた（C1〜C3 は 05c33bfc0） |
| ∞ 数学 G2 | 閉じた。IF-G2-finish の段 1 と段 2 の途中まで main に入った（408d87457、6f35a986f）。枝 `math/g2` と worktree は削除。残りは `infinity-g2-progress.md` の末尾の節から段階 II の ∞ 供給レーンが再開する |
| BS 設計・BS 実装（段階 I） | 閉じた。段階 II では BS 実装は新しい Codex チャット、設計は調整役が持つ（入口 `bhatt-scholze/design-status.md` §0、drafts の扱いは計画 §1.0） |
| DG・論文の層 | 閉じた |
| 段階 II の新しいレーン（①③⑤⑥） | 11-05 夜：計画の確定。開始文は [stage-ii/lane-starts.md](stage-ii/lane-starts.md)、指示書は `stage-ii/`（①IC-W1、③IS-W1、⑥SC-W1）。⑤は W11（§6 の追記）|

## 5. 段階 I から引き継ぐ要点

- 整理の結果：DG 1,592 → 126 本、論文の層の区切りはすべて完了、∞ は中核層間の順序違反 0・直接の禁止辺 0・中核の閉包の KST とモデル圏 150 → 74（残りは M16）、F-2 で KST から移した 730 モジュールの名前空間をディレクトリに合わせた（改名表 `../scripts/refactor/targets/f-namespace-map.json`、旧名は deprecated alias で段 G の最初の区切りまで残す）。
- 主定理の閉包の sorry は 3 つ（E3、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`）。
- 調整役の引き継ぎは [coordinator-handover-2026-11.md](coordinator-handover-2026-11.md)。
