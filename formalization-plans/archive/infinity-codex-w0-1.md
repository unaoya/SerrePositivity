# Codex 作業指示書 IF-W0-1：verify.sh を合否の関門にする（R41）

作成：2026-10-28（∞ 基盤の整備、管理は Claude）。宛先：Codex。
計画：[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md) の段 0・R41。この指示書の §0 は、以後の IF-Wn 指示書に共通する前提とする。

## 0. 共通の前提（IF-Wn 共通）

- **作業場所**：同じワークスペースで他のレーン（KST 各レーン、Bhatt–Scholze）が作業し、`lake build` も走らせている。main の作業木では作業もビルドもしない。
  使い捨ての worktree を作り、その中だけで作業する。

  ```bash
  set -o pipefail
  cd /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity
  git worktree add ../SerrePositivity-ifw0-1 -b infra/if-w0-1 main
  cp -Rc .lake ../SerrePositivity-ifw0-1/.lake     # APFS の複製。olean を共有しない
  cd ../SerrePositivity-ifw0-1
  ```

- **所有範囲**：指示書に書いたファイルだけを変更する。それ以外（`.lean` の本文、計画文書、他レーンのファイル）は変更しない。
- **コミット**：worktree のブランチにだけコミットする。`git add -A`・`git commit -a` は使わず、`git commit --only <paths>` を使う。main への取り込みは Claude が検収の後に行う。
- **失敗したとき**：次の二つを区別する（10-28 に明確化）。
  - **自分がこの指示書の作業で新しく書いた・書き換えたもの**（新しいスクリプト、新しいファイル、所有範囲の変更）のコンパイルエラー・構文の誤り・試験の失敗：自分で直して進めてよい。直した内容は報告に書く。
  - **それ以外**：既存のコード・監査・ビルドが想定外に失敗したとき、指示書と現状が食い違うとき（件数の違いなど）、直すには所有範囲の外を変える必要があるとき。このときは直さずに止め、コマンドとエラーをそのまま報告する。
- **報告**：§4 の受入条件の結果（コマンド、終了コード、要約）、変更したファイルの一覧、かかった時間を書く。

## 1. 背景

`scripts/refactor/verify.sh` は、各段の合格を判定するのに使う予定だが、いまは次の問題がある（第 1・2 回の外部レビューと内部調査で確認済み）。

1. **失敗しても正常終了する。** `lake build` の失敗も監査の失敗も記録するだけで、最後の `echo` で終了コード 0 になる。
2. **監査が固定の一覧になっている。** 実行するのは 24 本だけで、`scripts/audit_*.lean`（94 本）と `scripts/audit/*.lean`（5 本）の残りは実行されない。
3. **ビルド対象に漏れがある。** 監査対象は `^import SerrePositivity` の行だけから集めている。`public import` の行と、`scripts/audit/*.lean` が import するモジュールが対象に入らない。このため、ルートと `scripts/audit_*.lean` の閉包に含まれないモジュール 993 本（10-28 の再計算）がビルドされない。参考：直接の import 先は `scripts/audit_*.lean` が 2,745 本、`scripts/audit/*.lean` が 4,207 本で、和集合は約 6,600 本（10-28 の Codex の報告で訂正）。
4. **sorry 閉包の検査が判定になっていない。** `audit_sorries.lean` は結果を表示するだけである。しかも「直接 sorry を持つ宣言」の一覧が、引用の 3 件があるにもかかわらず `[]` と表示される（補助宣言 `_proof_n` などに埋もれている可能性がある）。
5. 生成物の `scripts/refactor/audit_targets.txt` が git で追跡されている（実行のたびに変わる）。

## 2. 作業

変更してよいファイル：
- `scripts/refactor/verify.sh`
- `scripts/refactor/audit_sorries.lean`
- 新規の `scripts/refactor/verify_baseline.txt`
- 新規の `scripts/refactor/audit_manifest.txt`
- 新規の `scripts/refactor/README.md`
- `.gitignore`

`scripts/refactor/audit_targets.txt` は git の追跡から外す（`git rm --cached`）。
§4 の故意の失敗の試験のために worktree に一時的なファイルを作るのはよいが、コミットしない。試験の後で消す。

### 2.1 verify.sh の要件

1. **終了コード**：次のどれか一つでも失敗したら、最後に非零で終了する。
   - ルートの `lake build SerrePositivity`
   - 監査対象のビルド
   - 各監査（`lake env lean <file>` の終了コード）
   - sorry 閉包の判定（2.2）
   - 監査の一覧の照合（下の 3）

   zsh なので、パイプの各段の終了コードは `$pipestatus` で取る。`grep` が何も出さないことで失敗扱いにならないようにする。
2. **監査の自動列挙**：`scripts/audit_*.lean` と `scripts/audit/*.lean` をすべて実行する。基準の HEAD では 99 本のはず。違ったら作業を止めて報告する。
3. **監査の一覧の照合**：列挙の結果を、追跡するファイル `scripts/refactor/audit_manifest.txt`（基準の HEAD で作る）と比べる。
   - 一覧にあるのに見つからない監査があれば **FAIL**（削除や改名で、監査が黙って減るのを防ぐ）。
   - 一覧にない新しい監査は実行し、「一覧への追加が必要」と表示する。
4. **ビルド対象**：すべての監査ファイルの `import` と `public import` の行から `SerrePositivity.*` を集める。結果は追跡しない場所（`.lake/verify/audit_targets.txt`）に書く。
5. **既知の失敗の照合**：`scripts/refactor/verify_baseline.txt` の各行は、次の 4 項目を持つ。
   - 監査ファイル
   - 基準コミット
   - 期待する失敗の署名：エラーの件数と、各エラーの「ファイル:行・宣言名・エラー文の先頭 1 行」を正規化したもの
   - 理由と担当

   照合の規則：
   - 失敗が一覧の署名と**ちょうど一致する**ときだけ「既知」として、合否に数えない。
   - 一覧にある監査でも、エラーが増えたり変わったりしたら **FAIL**。
   - 一覧にない失敗は **FAIL**。
   - 一覧にある監査が通るようになった場合は「一覧から外せる」と表示する（失敗にはしない）。
6. **要約**：最後に `PASS` または `FAIL` の一行と、件数（ビルド・監査の成功／失敗／既知）を出す。同じ内容を `.lake/verify/summary.json` にも書く。
7. **試験用の入口**（検収には使えない）：
   - `VERIFY_EXTRA_AUDITS`（空白区切りの .lean のパス）：これも監査として実行する。
   - `VERIFY_SKIP_BUILD=1`：ビルドを飛ばす。
   - `VERIFY_BASELINE=<path>`：別の既知の失敗の一覧を使う。

   これらのどれかを使った実行では、`summary.json` に `"gate": false` と書き、要約の行にも `(non-gate)` と付ける。
8. **ログ**：今と同じく `scripts/refactor/verify.log` に追記する（追跡はしない）。各段の所要時間も残す。
9. 今と同じく、ソースのない古い olean を除く処理を最初に行う。

### 2.2 sorry 閉包の判定（audit_sorries.lean）

- 判定の内容：根（既定は `main_statement`）の定数閉包の中で `sorryAx` を直接使う宣言を集め、補助宣言（`_proof_n`、`match_n` など）は親の宣言にまとめる。
  その集合が、許された引用の集合と**ちょうど一致**することを確かめる。許された引用は次の 3 件。
  - `SerrePositivity.theorem_3_1_K0`
  - `SerrePositivity.Section4.supportedRankK0_descent`
  - `SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`

  あわせて、`kanQuillen_model_exists` が閉包に入らないことも確かめる。
- 一致しなければエラー（`throwError`）にする。これで `lake env lean` の終了コードが非零になる。
- 試験のため、根と許された集合を環境変数（`SORRY_AUDIT_ROOT`・`SORRY_AUDIT_ALLOWED`）で差し替えられるようにする。既定値は上のとおり。
- いまの表示が `[]` になる原因を調べ、報告に書く。

### 2.3 README

`scripts/refactor/README.md` に次のことを書く。
- 使い方。
- 合否の基準。
- 監査の一覧と既知の失敗の一覧の更新手順。既知の失敗の一覧は、Claude（またはコーディネータ）の承認なしに変えないこと。
- 所要時間の目安。

書式はリポジトリの docstring の様式（概要・方針・規約・使われ方）に合わせる。

## 3. 手順

1. §2 を実装する。`verify_baseline.txt` はまだ空（見出しの行だけ）にしておく。
2. **基準実行**：worktree で、試験用の入口を使わずに verify.sh を通しで実行する。既知の失敗の一覧が空なので、基準状態に失敗する監査があれば FAIL になる（それでよい）。
   報告に書くこと：
   - 全体の所要時間と、各段の所要時間。
   - 監査の本数。
   - 失敗した監査ごとの失敗の署名と、エラーの先頭 3 行。
   - 理由の候補。
3. **ここで止めて報告する。** Claude が、どの失敗を既知として承認するかを決め、`verify_baseline.txt` に書く内容を指示する。
4. 指示どおりに `verify_baseline.txt` を書き、もう一度通しで実行して PASS になることを確かめる。
5. §4 の故意の失敗の試験を行う。

## 4. 受入条件

1. 手順 4 の実行で、ビルドがすべて成功し、要約が `PASS`、`"gate": true`、終了コードが 0。
2. 故意の失敗の試験。どれも要約が `FAIL` で、終了コードが非零になること。試験には §2.1-7 の入口を使ってよい（`gate:false` になるのは正しい動作）。
   - (a) 新しく失敗する監査：`VERIFY_EXTRA_AUDITS` で、エラーになる /tmp のファイル（例：`example : False := by decide`）を加える。
   - (b) 既知の監査での別のエラー：`VERIFY_BASELINE` で、実際とは署名の違う既知の失敗の一覧を渡す。
   - (c) ビルドの失敗：worktree に一時的に壊れたモジュール（例：`SerrePositivity/IFW0Broken.lean`）を作り、それを import する /tmp の監査を `VERIFY_EXTRA_AUDITS` で加えて、ビルドを飛ばさずに実行する。試験の後でモジュールを消す。
   - (d) 新しい sorry：`SORRY_AUDIT_ROOT` を、sorry を使う一時的な定理（(c) と同じく worktree の一時ファイル）に向けて audit_sorries.lean を実行し、非零で終了することを確かめる。
   - (e) 監査が減った場合：`audit_manifest.txt` に存在しない監査名を一時的に 1 行足して実行し、FAIL になることを確かめる。試験の後で元に戻す。
3. `git status` で、変更が §2 の所有範囲だけであること（一時ファイルが残っていないこと）。
4. `zsh -n scripts/refactor/verify.sh` が通ること。

## 5. コミット

一つのコミットにする。

```bash
set -o pipefail
git rm --cached scripts/refactor/audit_targets.txt
git commit --only scripts/refactor/verify.sh scripts/refactor/audit_sorries.lean scripts/refactor/verify_baseline.txt \
  scripts/refactor/audit_manifest.txt scripts/refactor/README.md scripts/refactor/audit_targets.txt .gitignore \
  -m "$(cat <<'MSG'
chore(refactor): make verify.sh a pass/fail gate (IF-W0-1, R41)

- enumerate all audits and check them against a tracked manifest
- build every module imported by any audit, including public imports
- aggregate build, audit and sorry-closure failures into a non-zero exit
- known failures must match a recorded signature in verify_baseline.txt
- test hooks mark the run as non-gate in summary.json
- audit_sorries.lean asserts the exact set of cited sorries

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
MSG
)"
```

## 6. 禁止事項

- `.lean` の本文（scripts/refactor/audit_sorries.lean を除く）・計画文書・監査ファイルの変更。
- 監査の検査条件を弱めること。
- main の作業木での作業・ビルド。
- 既知の失敗の一覧を、Claude の指示なしに書くこと（§3 の手順 3）。
- 一時的な試験用ファイルをコミットすること。
