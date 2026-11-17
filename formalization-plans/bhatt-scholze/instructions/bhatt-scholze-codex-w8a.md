# Codex 作業指示書 BS-W8a：E3 の界面を Perfectoidization/Derived/ へ移し、BS の集約ファイルを作る

作成：2026-10-25（BS 作業チャット）。宛先：Codex。BS-W7（`98849e356`）の後に行う。
ユーザーの決定（10-25）：(1) `PerfectoidizationInterface/` は §8 の導来 perfectoid 化とその環への帰結なので `Perfectoidization/Derived/` へ移す。
(2) 転送スタブを無くし今後も生まないため、BS が所有する集約 `SerrePositivity/BhattScholze.lean` を作り、所有範囲外（root・`audit_f5`・`audit_f7`）には
この 1 本だけを import してもらう（書き換えは進捗確認チャットに別途依頼する）。集約の中身は今の root が import している BS のモジュールと同じ範囲。

## 0. 前提

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
- **宣言名・名前空間・型・証明は一切変えない**。
- 新しい sorry・axiom を加えない。

## 1. 作業 A：移動（スクリプト）

計画は [bhatt-scholze-codex-w8a-moves.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w8a-moves.json)、スクリプトは [bhatt-scholze-move-modules.py](../../../evidence/bhatt-scholze/bhatt-scholze-move-modules.py)（W2〜W4 で使った移動用）。

| 移動元 | 移動先 |
| --- | --- |
| `PerfectoidizationInterface/Interface` | `Perfectoidization/Derived/Interface`（**以後この名前は変えない**。EInfinity が import する） |
| `PerfectoidizationInterface/IntegralExistence` | `Perfectoidization/Derived/IntegralExistence` |
| `PerfectoidizationInterface/Excision` | `Perfectoidization/Derived/Excision` |

所有範囲外の import 元は `EInfinity/Perfectoidization/Comparison.lean`（`…PerfectoidizationInterface.Interface`）だけなので、その旧名にだけ転送スタブを置く。
直下の集約 `BhattScholze/PerfectoidizationInterface.lean` と、W7 の転送スタブ `PerfectoidizationInterface/FiniteIntegralExistence.lean` は
スクリプトが import 行を新しい名前に書き換える（削除は進捗確認チャットの書き換えの後、W8b で行う）。

```bash
set -o pipefail
git log --oneline -1 --grep="merge Prism, Semiperfectoid"   # 98849e356 があること
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST   # 空であること
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8a-moves.json
# 期待値（98849e356 で確認）："moves": 3, "stubs": 1, "owned_files_rewritten": 12,
#   "foreign_importers_left_unchanged": {"SerrePositivity/EInfinity/Perfectoidization/Comparison.lean": 1}, "foreign_imports_without_stub": []
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8a-moves.json --apply
```

件数が違う場合は `--apply` せずに報告する。ここでコミット 1（§4）。その後：

```bash
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w8a-moves.json --stubs
# 期待値：wrote 1 stubs
```

ここでコミット 2。

## 2. 作業 B：BS の集約ファイル（手作業、新規 1 本）

新規ファイル `SerrePositivity/BhattScholze.lean` を、次の内容で作る（import の順もこのとおり）。

```lean
module

public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDeltaTensor
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismTensor
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectPrismResidueTensor
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedBaseChange
public import SerrePositivity.BhattScholze.Perfectoidization.Excision
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Excision
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
public import SerrePositivity.BhattScholze.Almost.SupportedQuotient
public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.BhattScholze.Andre.Transfinite.Basic
public import SerrePositivity.BhattScholze.Andre.Variants.MonicRootedExtension
public import SerrePositivity.BhattScholze.Andre.Remark715.Unoriented

/-!
# Bhatt–Scholze の形式化の集約

## 概要
所有範囲外（root の `SerrePositivity.lean`、`scripts/audit_f5.lean`・`audit_f7.lean`）が BS を読み込むための唯一の入口。
2026-10-25 時点で root が個別に import していた BS のモジュール（32 行）を、整理後の名前で 15 本にまとめたもの。

## 方針
BS の中でモジュールを移したりまとめたりしたときは、このファイルだけを直す。所有範囲外の import は変わらないので、転送スタブは要らない。

## 規約
宣言は持たない。BS の全モジュールではなく、root が読み込んでいた範囲（主定理の経路と、選ばれた照合・変種）だけを入れる。

## 使われ方
root の `SerrePositivity.lean`、`scripts/audit_f5.lean`・`audit_f7.lean`（進捗確認チャットが書き換えた後）。
-/
```

（`audit_f5`・`audit_f7` が見る `Delta.Perfect.DistinguishedRegular`・`Prism.Perfectoid.WittQuotientPerfectoid` は、この 15 本から import をたどって届くことを確認済み。）

ここでコミット 3。

## 3. 禁止事項と受入条件

禁止：宣言・証明の変更、上の 3 本以外の移動、所有範囲外のファイルの変更（root、`audit_f5`・`audit_f7`、EInfinity）、転送スタブの削除。
ビルドが失敗した場合は、直さずにエラーをそのまま報告する。

受入条件：BS-W1 §5「作業 3 の後」と同じコマンド一式に加え、次がすべてエラーなし・終了 0。

```bash
lake build SerrePositivity.BhattScholze SerrePositivity.EInfinity.Perfectoidization.Comparison 2>&1 | tail -2
ls SerrePositivity/BhattScholze/Perfectoidization/Derived/   # Excision IntegralExistence Interface
ls SerrePositivity/BhattScholze/PerfectoidizationInterface/  # FiniteIntegralExistence（W7 のスタブ）と Interface（今回のスタブ）
lake env lean scripts/audit/bhatt_scholze.lean 2>&1 | tail -1
```

## 4. コミット

```bash
set -o pipefail
OWN="SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean \
  scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean"
# コミット 1（作業 A の --apply の後）
git commit --only $OWN -m "$(cat <<'EOF'
refactor(bs): move the E3 interface under Perfectoidization/Derived

The interface type and its two ring-level bridges (Thm 10.11 and Cor 8.12 as rings) are §8
material, so PerfectoidizationInterface/{Interface,IntegralExistence,Excision} move to
Perfectoidization/Derived/. Plan: formalization-plans/bhatt-scholze-codex-w8a-moves.json.
Only import lines change.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
# コミット 2（--stubs の後）
git add SerrePositivity/BhattScholze/PerfectoidizationInterface/Interface.lean
git commit --only SerrePositivity/BhattScholze/PerfectoidizationInterface/Interface.lean -m "$(cat <<'EOF'
refactor(bs): forward the old interface name that EInfinity imports

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
# コミット 3（作業 B の後）
git add SerrePositivity/BhattScholze.lean
git commit --only SerrePositivity/BhattScholze.lean -m "$(cat <<'EOF'
feat(bs): add the BS aggregator that outside files import instead of individual modules

SerrePositivity/BhattScholze.lean imports the 15 BS modules that the root aggregator reached
through 32 lines, under their current names. Once the root and the F5/F7 audits import only
this file, BS reorganizations no longer need forwarding stubs.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 5. 報告してほしいこと

三つのコミットハッシュ、dry-run と `--stubs` の出力、ビルドのジョブ数・所要時間・grep の結果、§3 の追加確認の出力、想定と違ったこと。
