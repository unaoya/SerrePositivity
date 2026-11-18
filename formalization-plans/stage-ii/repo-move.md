# リポジトリを `~/Documents` の外へ移す手順（紙、未実施）

作成：2026-11-18（調整役）。決定：ユーザー（11-18、移動先 `~/LEAN_Projects/`）。理由：`~/Documents` は iCloud「デスクトップと書類」の領域（File Provider）で、`.nosync` でもアップロードされないだけ。`.lake` などへの大量の書き込みのたびに fseventsd・fileproviderd が重くなる。

## 0. 時期と前提

- 全レーンが止まれる区切り（候補：⑦ の IC-1 の取り込みの後）。全ビルド・鍵待ちが 0、各作業木に未コミットの追跡ファイルなし（未追跡の下書きは一覧にして一緒に移る）。
- 同じボリューム（APFS）の中の移動なので `mv` は一瞬で、`.lake`（各 100 GB 超）も作り直さずに済む。

## 1. 移すもの

- `~/Documents/LEAN_Projects.nosync/SerrePositivity`（main）と作業木（その時点の `SerrePositivity-*`）、`SerrePositivity-blueprint-site`。
- **未決**：`LEAN_Projects.nosync/` には他のプロジェクト（AG、BSDConverse、arxiv_formalization など約 20）もある。フォルダごと `~/LEAN_Projects/` に移すか、SerrePositivity だけ移すか（ユーザーに確認）。
- `/private/tmp` の作業木（⑦ の移動前の環境など）、`~/.cache/lake`、`~/serre-evidence` は領域の外なので動かさない。

## 2. 手順

1. 各レーンに停止を伝え、作業木の `git status` と鍵の `--status` を確かめる。ブループリントの配信（8790）を止める。
2. `mkdir ~/LEAN_Projects`、対象を `mv`。
3. main で `git worktree repair <新しい各作業木のパス>`、`git worktree list` で確かめる（`/private/tmp` の作業木は main の場所だけが変わるので、同じ repair で直る）。
4. 絶対パスの書き換え：
   - git の中：現役の道具と文書だけ（`scripts/` の現役のスクリプト、`formalization-plans/` の現役の指示書、`blueprint/`）。`evidence/` と `scripts/refactor/targets/` の記録（約 270 ファイル）は当時の記録なので書き換えない。
   - git の外：`~/.codex/config.toml`、鍵の履歴（`$TMPDIR/serre-lake-build*`）、調整役の scratchpad のスクリプト。
   - `.lake` の中の絶対パス（Lake の trace・成果物キャッシュの対応）：移動後に `lake build SerrePositivity` を流し、キャッシュから戻るか（数分）、作り直しになるかを確かめる。作り直しなら夜に。
5. Claude Code のプロジェクトのメモリは作業場所のパスで決まる（`~/.claude/projects/-Users-sugakubunka-Documents-LEAN-Projects-nosync-SerrePositivity/`）。新しい場所で開くと別のプロジェクトになるので、`memory/` を新しいプロジェクトのディレクトリへ写す。
6. Codex の各レーンのチャットは、新しい作業木で開き直す（指示書の冒頭のパスも直す）。
7. 確認：root のビルド、監査一本、`scripts/check_documentation.py --links-only`、鍵の動作、fseventsd・fileproviderd がビルド中に上がらないこと。
8. 記録：coordination.md の作業木の表、README、メモリ。

## 3. 戻し方

うまくいかなければ `mv` で元に戻し、`git worktree repair` をもう一度。
