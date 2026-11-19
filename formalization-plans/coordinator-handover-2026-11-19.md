# 調整役の引き継ぎ（2026-11-19、リポジトリの移動に伴う切り替え）

作成：2026-11-19（前の調整役）。宛先：`~/LEAN_Projects/SerrePositivity` で開いた新しい調整役のチャット（Claude Code）。リポジトリを `~/Documents/LEAN_Projects.nosync/` から `~/LEAN_Projects/` へ移したので（`stage-ii/repo-move.md`）、Claude Code のプロジェクトが変わり、前のチャットの文脈は引き継がれない。メモリは新しいプロジェクトへ写した。前の引き継ぎ（`coordinator-handover-2026-11.md`、11-05）は履歴。

## 1. 最初に読むもの（この順）

1. 本書。
2. メモリの `MEMORY.md` の索引（とくに `no-formalization-during-cleanup`、`stage-ii-second-half`、`infinity-consolidation`、`lanes-closed-2026-11-17`、`main-worktree-shared-index`、`verify-build-costs`、`lake-artifact-cache`、`faithful-generality`、`progress-report-format`）。
3. `stage-ii/stage-ii-second-half.md` §12（大きな流れ）。
4. `stage-ii/consolidation/infinity-consolidation-w1.md` §13・§14（IC-2 の段 0 と決定）。
5. `stage-ii/consolidation/bs-cleanup-w1.md`（BS の整理の段 0）。
6. root の `README.md` の「Documents」（文書の場所と参照の向きの正本）。

## 2. 今の状態（11-19 朝）

- **大きな流れ**（`stage-ii-second-half.md` §12）：(1) ③-a の 5∞-1 と ⑦ の IC-1 の取り込み → **済み** → (2) コードの整理と文書の整備 ← **今ここ** → (3) 計画の立て直し（P⁰ の段 0、モデル圏を通る 32 項目）→ (4) BS の sorry → (5) K 理論の sorry。
- **整理が終わるまで新しい形式化はしない**（ユーザー、11-19）。昼夜の区別なく適用・検証を回してよい。鍵（`scripts/refactor/with_build_lock.sh`）は残す（全体の Lean のプロセスは同時に二つまで）。
- **main**：cbcb40a59（③-a の取り込み、push 済み）。以後、移動の記録などがあれば README とこの紙に。
- **主定理の閉包の sorry**：3 つのまま（E3、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`）。
- **作業木と枝**：main・⑦ `SerrePositivity-ic`（`refactor/infinity-consolidation`）・⑧ `SerrePositivity-cited`（`research/cited-coverage`）の三つだけ。③-a・coord・IC-1 の比較用は 11-19 に消した。③-a の夜の探索はタグ `archive/coverage-weak-descent-2026-11-19`（ローカル、未 push）、旧 R2 の未追跡 4 本は `~/serre-evidence/inf-supply/old-r2/`。

### 2.1 レーン

| レーン | 作業木 | 今 | 次 |
| --- | --- | --- | --- |
| ⑦ IC-W1 | `SerrePositivity-ic` | IC-2 の段 0 の紙をコミットして止まっている | IC-2 の適用。**1,390 本の案**（逆向き import の起点 235 本は据え置き）、互換の入口 4 本は条件付きで Archive へ、削除 0。組に分けて、組ごとに調整役が取り込む。並行して 235 本の置き場所の紙 |
| ⑧ 文献の対応表・原稿 | `SerrePositivity-cited` | BS の整理の段 0（紙、BC-W1）を実施中（11-19 朝に開始） | 段 0 の報告で止まる。その後、ブループリントの HTT・HA の部の原稿 |
| ③-a・⑥・③-b | — | 閉じた／止まっている | 整理の完了の後に再開を決める |

### 2.2 調整役の次の仕事

1. 移動の後の確認（`repo-move.md` §2 の 7）：root のビルド、監査一本、`scripts/check_documentation.py --links-only`、鍵の動作。Lake の成果物がキャッシュから戻るか、作り直しになるかを記録する。
2. ⑦・⑧ のチャットを新しい作業木で開き直してもらう（ユーザー）。それぞれの開始文に「`pwd` を確かめ、`git merge main`」を入れる。
3. IC-2 の適用の組ごとの取り込み（下の 3. の道具）。IC-2 の実測で IC-3・IC-4・IC-5 の範囲と順序を決める（IC-4 の K 固有 912 本だけ先に `KTheory/` へ、という案もある）。
4. ⑧ の BS の段 0 の報告を見て、適用の時期と作業木を決める（IC-2 の後の見込み）。
5. ブループリント：③-a の成果で対応表の宣言の位置を更新して建て直す。依存グラフが実際のブラウザで色つきで描かれるかは、ユーザーに見てもらう件が残っている（重ければ部ごとに分ける）。保留の段落の行き先（BS 9、Kerodon 5 と定義 15.1）。
6. ③-a の R06.1 の型の修正と「途中の補題の型では論文の誤植を直す」規則の記録は、③-a の閉鎖で宙に浮いた。再開の計画のときに拾う。

## 3. 道具（`scripts/coord/`、11-19 に main へ）

- `merge_check.py <出力> "<ラベル>"`：未コミットの merge を作った後に nohup で。root → 監査の対象 → 全監査（並列 6）→ sorry の閉包。最後が `MERGE-CHECKS-DONE` なら通過。前回の束の所要時間は `~/serre-evidence/coord/a3-merge/run-batch-*.json` を出力ディレクトリに写すと見積もりに使う。検証中は `$TMPDIR/serre-lake-build.day-capacity` を 1、終わったら 2。実測：IC-1（場所の移動あり）約 6 時間、③-a（追加だけ）36 分。
- `blueprint_build.py`：ブループリントの Lean を塊で建て、`lake exe vbp build`。その後 `rsync -a --delete blueprint/_out/site/html-multi/ ../SerrePositivity-blueprint-site/` と `python3 blueprint/scripts/style_site.py ../SerrePositivity-blueprint-site`。生成は `blueprint/scripts/gen_paper.py`、`gen_cited.py clmst bs vdescent`、`gen_kerodon.py 1`〜`10`、`gen_blueprint.py` の順。
- `serve_nocache.py <サイト>`：プレビュー（127.0.0.1:8790）。移動で止まるので、新しい場所で起動し直す。
- 新しい模型の 75 モジュールのように、root から届かないモジュールが枝で増えたら、取り込みのときに入口（`InfinityCategories/Project/Entrypoints/…`）へ登録する。

## 4. やり方（前の調整役から）

- 取り込みは main で `git merge --no-commit --no-ff` → `merge_check.py` → 通ったらコミット。main の作業木と index は共有なので、直接のコミットは `git commit --only -- <files>`（merge の途中はできない）。
- push はユーザーが言ったときだけ。
- レーンへの文は `/goal` の形で、そのまま貼れるものを。報告は ⑦・⑧ の報告ファイルと、各レーンの最新コミットを自分で確かめてから受ける（数字の照合）。
- 外枠を上げる・削除・Archive への移動・範囲の変更はユーザーに諮る。「ここを区切りとする」と書いたレーンはそこで止める（11-19、③-a の件）。
