# Codex 作業指示書 BS-M15：M15（descendability）と G12（CAlg の presentability）

作成：2026-11-14（調整役）。決定：ユーザー（11-14「新しいレーンを立てる」）。レーン ⑤d。

## 0. なぜ新しいレーンか

⑤a（BS-W16）は M14（P⁰、May 案、完成見込み 14,990〜23,240 行）で数日かかる。5∞-5（A4）が M14 を待ち、5∞-6（A5）が M15 を、5∞-5 が G12 を待つ。⑤a に M14 → M15 → G12 を順に持たせると M14 の後ろに積み上がるので、M15 と G12 をこのレーンに移す（`stage-ii-second-half.md` の 5a-9・5a-7）。

## 1. 作業場所と規則

- worktree `SerrePositivity-bs-m15`、枝 `math/bs-m15`（main 602fe450f から。数学の基準は c5c4436c0）。
- **main は凍結中**（B3、`stage-ii/bulk-b3-goal.md`）。自分の枝へのコミットは続けてよい。B3 の取り込みの後に B4 の改名で追従する。今夜は一括レーンが重いビルドを回すので、大きい監査は控え、対象ビルドと自分の小さい監査だけにする。
- ビルドは共有の鍵 `scripts/refactor/with_build_lock.sh --class impl --wait 3600` で。昼は一回の塊を短く。
- **⑤a のファイルは変えない**（`EInfinity/` の既存のファイル、`BarrattEccles/` の既存のファイル、界面 `EInfinity/Interface/`）。読んで import するのはよい。界面 `EInfinityTheory` に欄を足さない（M15 は欄にしない、BS-W16 報告 §61.4）。
- 新しいファイルの置き場所：M15 の一般の部分は `EInfinity/Modules/`、BE への適用は `EInfinity/BarrattEccles/Modules/`。G12 の一般のモナド性・presentability は `InfinityCategories/` の HTT・HA・Kerodon の該当する節（Tag・番号を docstring と報告に）、BE への適用は `EInfinity/BarrattEccles/Presentable/`。
- docstring は README の Conventions（概要・方針・規約・使われ方、原典の番号を引く、ノートを引かない）。
- 原典どおり（`bhatt-scholze/design-status.md` の方針）。`[ModelCategory SSet]` のような外せない仮定を足さない。

## 2. 引き継ぐ紙の作業（⑤a の報告 `bhatt-scholze/report-codex-w16.md`、⑤a の枝にある）

- G12：§60〜§61（§61.2、見込み 3,000〜5,000 行）。
- M15：§61.4、§66、§95、§97、§107、§111（見込み 4,800〜8,500 行。一般の R 加群 2,500〜4,500、指数 900〜1,500、降下・評価・完備版 1,400〜2,500）。§107.3 の五点（同じ台の厳密な忘却、拡大・制限の全関手と随伴、弱同値と native な辺・合成への降下、相対テンソルと底変換、指定の単位・fiber・指数射）を最初の受け渡しにする。
- 読むには `git -C ../SerrePositivity-bs-impl show HEAD:formalization-plans/bhatt-scholze/report-codex-w16.md` か、⑤a の worktree のファイルを読むだけ（書き込まない）。

## 3. 順序と止め方

1. **M15 の段 0（紙、短く）**：上の引き継ぎを確かめ、残りの補題をすべて Lean の主張の型で書き出した一覧と見込みを出す。利用側（drafts/A5 の Lemma 8.6、`Shared/Descendable`）が要る RHom・完備版の入力の型も書く。thick ⊗-ideal の定義は K の R53（`IsThick`）と一本にできるか確認する（`refactor-ledger.md` §8 の §8 の行）。
   **条件付きの事前承認**：見込みの上端が 8,500 行以下なら、報告して止まらずに Lean へ。超えるときは止まって報告。
2. **M15 の実装**：一覧の補題を順に証明する。数え方は IS-W2 §14 と同じ（証明の分割は数に入れない／前提計算の法則は一覧の補題ごとに 3 本まで／照合は全体で 3 本まで／それ以外の新しい数学の補題が要ったら止まって報告）。外枠は段 0 の上端の 2 倍。半分で止まらずに途中報告。
3. **G12**：M15 の後（または M15 が他のレーンを待つ間）。段 0 と止め方は M15 と同じ（事前承認の上限 5,000 行、外枠は上端の 2 倍）。
4. 停止点：M15 の完成（停止点 1）、G12 の完成（停止点 2）。どちらも単独で取り込む。報告して、次へ止まらずに進む。

## 4. 報告

`bhatt-scholze/report-codex-m15.md` に節を足して、自分の枝にコミットする。区切りごとに実測（本数・行数・宣言数）、対象ビルドと監査の結果、一覧の進み、追加した補題の型。
