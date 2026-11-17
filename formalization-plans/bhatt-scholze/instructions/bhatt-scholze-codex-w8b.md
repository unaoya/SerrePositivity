# Codex 作業指示書 BS-W8b：転送スタブ 29 本と直下の集約 PerfectoidizationInterface.lean を削除する

作成：2026-10-26（BS 作業チャット）。宛先：Codex。
**前提：進捗確認チャットが root・`audit_f5`・`audit_f7`・EInfinity の import を書き換えたコミット `e660efe6b` の後に行う**
（root の BS の import を `SerrePositivity.BhattScholze` の 1 行に、両監査も同じ 1 行に、EInfinity の
`…PerfectoidizationInterface.Interface` を `…Perfectoidization.Derived.Interface` に）。BS-W8a（`6e1da9815`・`d3895b976`・`a79f1711f`）の後。
ユーザーの決定（10-25）：転送スタブを無くす。以後は BS の集約 `SerrePositivity/BhattScholze.lean` だけを直す。

## 0. 前提

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
- 宣言・証明は変えない。消すのは宣言を持たない転送スタブ 29 本と、import だけの直下の集約 1 本。

## 1. 作業

```bash
set -o pipefail
git log --oneline -1 e660efe6b   # 進捗確認チャットの書き換え（E3 の coconnective 欄の削除も含む）があること
git status --short SerrePositivity/BhattScholze scripts/audit   # 空であること
# (a) 削除する 30 本の一覧
{ grep -rl "互換用の転送モジュール" SerrePositivity/BhattScholze; echo SerrePositivity/BhattScholze/PerfectoidizationInterface.lean; } | sort > /tmp/bs_w8b_delete.txt
wc -l < /tmp/bs_w8b_delete.txt   # 30
# (b) 削除する 30 本を import しているファイルが、BS の領域監査の 1 本以外にないこと（進捗確認チャットの書き換えの確認）
python3 - <<'PY'
import re, pathlib, subprocess
dele = [l.strip() for l in open('/tmp/bs_w8b_delete.txt')]
mods = {'SerrePositivity.' + f[len('SerrePositivity/'):-5].replace('/', '.') for f in dele}
for f in subprocess.check_output(['git', 'ls-files', '*.lean'], text=True).split():
    if f in dele: continue
    s = pathlib.Path(f).read_text()
    hit = [m for m in mods if re.search(rf'import\s+{re.escape(m)}\s*$', s, re.M)]
    if hit: print(f, hit)
PY
# 期待値：scripts/audit/bhatt_scholze.lean ['SerrePositivity.BhattScholze.PerfectoidizationInterface'] の 1 行だけ。
# ほかのファイル（SerrePositivity.lean、audit_f5・audit_f7、EInfinity）が出たら、進捗確認チャットの書き換えがまだなので止めて報告する。
```

(c) `scripts/audit/bhatt_scholze.lean` の `import SerrePositivity.BhattScholze.PerfectoidizationInterface` の行を、次の 3 行に替える（ほかは変えない）：

```lean
import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence
import SerrePositivity.BhattScholze.Perfectoidization.Derived.Excision
```

同じファイルの `let mods` の名前一覧に、削除する 30 本の名前が入っていれば、その名前を一覧から外す（スタブは宣言を持たないので監査対象から外れてよい）。

(d) 削除：

```bash
xargs git rm -q < /tmp/bs_w8b_delete.txt
find SerrePositivity/BhattScholze -type d -empty -print -delete
```

## 2. 受入条件

BS-W1 §5「作業 3 の後」と同じコマンド一式に加え、次がすべてエラーなし・終了 0。

```bash
lake build SerrePositivity.BhattScholze SerrePositivity.EInfinity.Perfectoidization.Comparison 2>&1 | tail -2
lake env lean scripts/audit_f5.lean 2>&1 | tail -2
lake env lean scripts/audit_f7.lean 2>&1 | tail -2
lake env lean scripts/audit/bhatt_scholze.lean 2>&1 | tail -1
grep -rl "互換用の転送モジュール" SerrePositivity/BhattScholze | wc -l   # 0
ls SerrePositivity/BhattScholze/*.lean 2>/dev/null | wc -l                # 0（直下のファイルはなくなる）
ls -d SerrePositivity/BhattScholze/PerfectoidizationInterface 2>/dev/null   # 出力なし
```

## 3. コミット

```bash
set -o pipefail
git commit --only $(cat /tmp/bs_w8b_delete.txt) scripts/audit/bhatt_scholze.lean -m "$(cat <<'EOF'
refactor(bs): remove the 29 forwarding stubs and the interface aggregator

The root aggregator, the F5/F7 audits and EInfinity now import SerrePositivity.BhattScholze or
the current module names, so no file imports the old names any more. Later BS
reorganizations only update SerrePositivity/BhattScholze.lean.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 4. 報告してほしいこと

コミットハッシュ、(b) の出力、(c) で直した行、ビルドのジョブ数・所要時間・grep の結果、§2 の追加確認の出力、想定と違ったこと。
失敗したときは直さずにエラーをそのまま報告する。
