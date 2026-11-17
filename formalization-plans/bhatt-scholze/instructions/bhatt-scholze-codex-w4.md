# Codex 作業指示書 BS-W4：André の部品を Andre/ へ、Inputs/ を E3 だけに、使われなくなった転送スタブを消す

作成：2026-10-25（BS 作業チャット）。宛先：Codex。BS-W3 のコミット（`f4dcf1d1a`・`7b82e02aa`）の後に行う。
ユーザーの決定（10-25）：ディレクトリを原典の章の内容に合わせる。(1) RootedExtension のうち Thm 7.14 が使う部分を `Andre/` へ、
主定理に使われない部分も `Andre/` の下にまとめて残す、(2) `Inputs/` を本物の文献入力（E3）だけにする、
(3) 直下の `Perfectoidization.lean` を `PerfectoidizationInterface/` へ、(4) 所有範囲内の import 元だけが使う転送スタブを消す、
(5) 空のディレクトリを消す。`Almost/` は変えない。

## 0. 前提と全体の方針

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
  所有範囲に `scripts/audit_andre_*.lean` を含める。
- **宣言名・名前空間・型は一切変えない**。`Inputs` から移すファイルの宣言（`Inputs.exists_perfectoidization_of_integral` など）も
  名前空間 `Inputs` のまま。変わるのはモジュール名（ファイルの場所）と import 行だけ。
- 新しい sorry・axiom・文献入力を加えない。

## 1. 作業 A：移動（スクリプト）

移動先は [bhatt-scholze-codex-w4-moves.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w4-moves.json)（211 本、転送スタブ 2 本）。
分類は主定理（`Paper/Statement`）と Thm 7.14（`Andre/Transfinite/Theorem714`）の import 閉包で決めた。

| 移動元 | 移動先 | 本数 | 中身 |
| --- | --- | --- | --- |
| `Semiperfectoid/RootedExtension/`（Thm 7.14 の閉包に入るもの） | `Andre/RootedExtension/`（サブディレクトリはそのまま） | 108 | Thm 7.14 の一段の拡大に使う根付き拡大。直下 14・DeltaAlgebra 16・Division 40・DeltaRoot 38 |
| `Semiperfectoid/RootedExtension/`（主定理に使われないもの、CompatibleRoot を除く） | `Andre/RootedExtension/Supplement/`（同上） | 98 | 同じ構成の変種。Variants・Remark715・RootEnvelope からの利用 18 本を含む。直下 5・Division 53・DeltaRoot 40 |
| `Inputs/AndreFlatness` | `Andre/AndreFlatness` | 1 | Thm 7.14 の公開入口（証明済み）。root が旧名を import するので**スタブを置く** |
| `Inputs/ArcExcision` | `PerfectoidizationInterface/ArcExcision` | 1 | Cor 8.12 の環の帰結（E3 から導出） |
| `Inputs/Perfectoidization` | `PerfectoidizationInterface/IntegralPerfectoidization` | 1 | Thm 1.17(1) の環の帰結（E3 から導出） |
| `Inputs/SemiperfectoidSurjectivity` | `Semiperfectoid/TorsionFreeQuotientSurjectivity` | 1 | Thm 7.4 の旧い適用形（証明済み） |
| `Perfectoidization`（直下） | `PerfectoidizationInterface/FiniteIntegralExistence` | 1 | 有限代数・完備化への系。root が旧名を import するので**スタブを置く** |

`Semiperfectoid/RootedExtension/` に残るのは 20 本（主定理が Thm 7.14 以外の経路で使う 17 本と、CompatibleRoot の 3 本）。
Thm 7.4 の降下（`RootedPerfectoidSurjectivityDescent` ほか直下 4 本）と CLMST の perfectoid イデアルが使う両立根（CompatibleRoot）である。
`Inputs/` に残るのは `PerfectoidizationInterface.lean`（E3）と、root の import が切り替わるまでの転送スタブ `AndreFlatness.lean` だけ。

```bash
set -o pipefail
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/CommutativeAlgebra   # 空であること
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w4-moves.json
# 期待値（2026-10-25 13:25、0d67f4e1a で確認）："moves": 211, "stubs": 2, "owned_files_rewritten": 262,
#   "foreign_importers_left_unchanged": {"SerrePositivity.lean": 2}, "foreign_imports_without_stub": []
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w4-moves.json --apply
```

件数が違う場合は `--apply` せずに報告する。ここでコミット 1（§5）。その後：

```bash
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w4-moves.json --stubs
# 期待値：wrote 2 stubs
```

ここでコミット 2。

## 2. 作業 B：所有範囲内の import 元の切り替えと転送スタブ 4 本の削除（手作業）

次の 4 本の転送スタブ（BS-W1 で作ったもの）は、旧名で import しているのが `CommutativeAlgebra/` の BS・CLMST 用ファイル 1 本ずつだけである。
import 行を新しい名前に替え（`public import` のまま）、スタブを削除する。

| ファイル:行 | 今の import | 新しい import | 削除するスタブ |
| --- | --- | --- | --- |
| `CommutativeAlgebra/AbsolutelyIntegrallyClosedPerfectoidQuotient.lean:6` | `…BhattScholze.RootedIdealSurjectivity` | `…BhattScholze.Semiperfectoid.RootedExtension.RootedIdealSurjectivity` | `BhattScholze/RootedIdealSurjectivity.lean` |
| `CommutativeAlgebra/PerfectoidIdealCompatibleRoots.lean:4` | `…BhattScholze.CompatibleRootCompletionPerfectoid` | `…BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootCompletionPerfectoid` | `BhattScholze/CompatibleRootCompletionPerfectoid.lean` |
| `CommutativeAlgebra/PerfectoidIdeal.lean:3` | `…BhattScholze.QuotientPerfectoidization` | `…BhattScholze.Semiperfectoid.QuotientPerfectoidization` | `BhattScholze/QuotientPerfectoidization.lean` |
| `CommutativeAlgebra/PerfectoidIdealCover.lean:4` | `…BhattScholze.CompatibleRootFamilyCompletionPerfectoid` | `…BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootFamilyCompletionPerfectoid` | `BhattScholze/CompatibleRootFamilyCompletionPerfectoid.lean` |

（`…` は `SerrePositivity.`。新しい import 先はどれも作業 A で動かないファイル。）削除の前に、各スタブの旧名を import するファイルが
上の 1 本だけであることを確かめる：

```bash
for m in RootedIdealSurjectivity CompatibleRootCompletionPerfectoid QuotientPerfectoidization CompatibleRootFamilyCompletionPerfectoid; do
  echo "$m: $(grep -rlE "import SerrePositivity\.BhattScholze\.$m\$" SerrePositivity SerrePositivity.lean scripts | tr '\n' ' ')"; done
# 期待値：各行に CommutativeAlgebra のファイル 1 本だけ（切り替えの後は空）
```

最後に空のディレクトリを消す（git は追跡しないので手元の片付け）：

```bash
find SerrePositivity/BhattScholze -type d -empty -print -delete
```

## 3. 禁止事項

- 宣言名・名前空間・型の変更。移動するファイルの中身の変更（import 行を除く）。docstring の書き換え（W5 以降で扱う）。
- §2 の 4 行以外の `CommutativeAlgebra/` の変更。所有範囲外のファイルの変更（`SerrePositivity.lean`、`scripts/audit/shared.lean`、
  `scripts/audit_f5.lean`・`audit_f7.lean`、`scripts/refactor/` を含む）。
- 残りの転送スタブ（root・`audit_f5`・`audit_f7` が import する 30 本と、今回の 2 本）の削除。

## 4. 受入条件

BS-W1 §5「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
`scripts/audit_andre_*.lean`、構造監査、CommutativeAlgebra の 4 モジュール）をコミット 3 の後に実行し、すべてエラーなし・終了 0。
ログの全体を `grep -nE "^error|error:|sorryAx"` で確かめてから報告する（宣言名に含まれる `error` は除いてよい）。加えて：

```bash
ls SerrePositivity/BhattScholze/Inputs/                                  # AndreFlatness.lean（スタブ）と PerfectoidizationInterface.lean（E3）だけ
find SerrePositivity/BhattScholze/Semiperfectoid/RootedExtension -name '*.lean' | wc -l   # 20
find SerrePositivity/BhattScholze/Andre/RootedExtension -name '*.lean' | wc -l           # 206
ls SerrePositivity/BhattScholze/*.lean | wc -l                           # 30（直下：W1 の転送スタブ 28 本 + 集約 PerfectoidizationInterface.lean + 今回のスタブ Perfectoidization.lean）
find SerrePositivity/BhattScholze -type d -empty                         # 出力なし
git diff HEAD~3 --stat -M -- SerrePositivity/BhattScholze | tail -1      # 移動は rename として検出されること
```

## 5. コミット

```bash
set -o pipefail
OWN="SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean \
  scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean"
# コミット 1（作業 A の --apply の後）
git commit --only $OWN -m "$(cat <<'EOF'
refactor(bs): move André's rooted extensions to Andre/ and leave only E3 in Inputs/

Move the 108 RootedExtension modules used by BS Thm 7.14 to Andre/RootedExtension/ and the 98
that the main theorem does not use to Andre/RootedExtension/Supplement/; the 20 used by Thm 7.4
and CLMST stay in Semiperfectoid/RootedExtension/. Move the four proved former inputs out of
Inputs/ (AndreFlatness to Andre/, ArcExcision and Perfectoidization to PerfectoidizationInterface/,
SemiperfectoidSurjectivity to Semiperfectoid/) and the top-level Perfectoidization to
PerfectoidizationInterface/FiniteIntegralExistence. Plan:
formalization-plans/bhatt-scholze-codex-w4-moves.json. Only import lines change.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
# コミット 2（--stubs の後）
git add SerrePositivity/BhattScholze/Inputs/AndreFlatness.lean SerrePositivity/BhattScholze/Perfectoidization.lean
git commit --only SerrePositivity/BhattScholze/Inputs/AndreFlatness.lean SerrePositivity/BhattScholze/Perfectoidization.lean -m "$(cat <<'EOF'
refactor(bs): forward the old names of the two modules the root aggregator imports

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
# コミット 3（作業 B の後）
git commit --only SerrePositivity/CommutativeAlgebra/AbsolutelyIntegrallyClosedPerfectoidQuotient.lean \
  SerrePositivity/CommutativeAlgebra/PerfectoidIdealCompatibleRoots.lean \
  SerrePositivity/CommutativeAlgebra/PerfectoidIdeal.lean SerrePositivity/CommutativeAlgebra/PerfectoidIdealCover.lean \
  SerrePositivity/BhattScholze/RootedIdealSurjectivity.lean SerrePositivity/BhattScholze/CompatibleRootCompletionPerfectoid.lean \
  SerrePositivity/BhattScholze/QuotientPerfectoidization.lean \
  SerrePositivity/BhattScholze/CompatibleRootFamilyCompletionPerfectoid.lean -m "$(cat <<'EOF'
refactor(bs): import the new BS module names from CommutativeAlgebra and drop four stubs

The four CommutativeAlgebra modules used by BS and CLMST import the moved BS modules by their
new names, so the forwarding stubs that only they used are removed.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

削除したスタブは `--only` にパスを渡せば削除として記録される（事前に `git rm` してもよい）。

## 6. 報告してほしいこと

三つのコミットハッシュ、dry-run の出力、`--stubs` の出力、§2 の grep の結果（切り替えの前と後）、ビルドのジョブ数・所要時間・grep の結果、
§4 の追加確認の出力、想定と違ったこと。失敗したときは直さずにエラーをそのまま報告する。
