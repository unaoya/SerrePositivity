# Codex 作業指示書 BS-W2：§2.1（δ 環の定義と基本）のファイルを Delta/Basic/ にまとめる

作成：2026-10-25（BS 作業チャット）。宛先：Codex。**BS-W1 の作業 3b のコミットが済んでから始める。**
宣言の名前・名前空間・型・証明は変えない。変えるのはモジュールの場所と import 行だけ。

## 0. 前提

BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。

## 1. 移すもの

`SerrePositivity/BhattScholze/Delta/` にある次の 22 本を `Delta/Basic/` へ移す。ファイル名は変えない。
移動先は [bhatt-scholze-codex-w2-moves.json](bhatt-scholze-codex-w2-moves.json)。

| 原典（著者版 §2.1） | モジュール |
| --- | --- |
| Def 2.1、Rem 2.2・2.4（定義、Frobenius 持ち上げ、W₂ 切断） | `DeltaRing`、`DeltaIdentities`、`DeltaFrobenius`、`DeltaFrobeniusNaturality`、`DeltaSectionNaturality`、`DeltaTransport`、`WittTwoMap`、`WittTwoUnits` |
| Ex 2.6（δ(p) の計算） | `DeltaPrime` |
| Lemma 2.9、Ex 2.10（商と δ 閉包） | `DeltaQuotient`、`DeltaIdeal`、`DeltaClosureGeneration` |
| Rem 2.7（余極限・部分環・Witt への写像） | `DeltaDirectLimit`、`DeltaSubring`、`DeltaWittGhostCoefficients`、`DeltaWittGhostCoefficientTwo`、`DeltaWittGhostFrobenius`、`DeltaWittGhostLowCoefficients`、`DeltaWittGhostNaturality`、`DeltaWittGhostRingHom`、`DeltaWittGhostStep`、`DeltaWittJetComparison` |

`Delta/Free/`（Lemma 2.11）はそのまま残す。§2.2〜2.4 のファイルも `Delta/` 直下に残す。

## 2. 実行

所有範囲だけを書き換える汎用スクリプト [bhatt-scholze-move-modules.py](bhatt-scholze-move-modules.py) を使う
（W1 の apply スクリプトの計画ファイルを引数にした版。動作は同じ）。

```bash
set -o pipefail
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST    # 空であること（W1 がコミット済み）
python3 formalization-plans/bhatt-scholze-move-modules.py formalization-plans/bhatt-scholze-codex-w2-moves.json
python3 formalization-plans/bhatt-scholze-move-modules.py formalization-plans/bhatt-scholze-codex-w2-moves.json --apply
```

dry-run の期待値（2026-10-25、W1 の移動を適用した作業ツリーで確認）：

```text
"moves": 22, "stubs": 0, "owned_files_rewritten": 60, "foreign_importers_left_unchanged": {}, "foreign_imports_without_stub": []
```

件数が違う場合は `--apply` せずに報告する。所有範囲外から import されるモジュールはないので、スタブは作らない（`--stubs` は使わない）。

## 3. 受入条件

BS-W1 §5 の「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
構造監査、CommutativeAlgebra の四モジュール）を実行し、すべてエラーなし・終了 0。加えて次を確認する。

```bash
git diff --cached -M --stat | tail -1     # 22 本の rename と import 行の変更だけ
git diff --cached -M --diff-filter=RM -- SerrePositivity scripts | grep -E '^[-+]' | grep -vE '^(\+\+\+|---) ' \
  | grep -vE '^[-+][ \t]*(public )?import '    # 出力が空
ls SerrePositivity/BhattScholze/Delta/Basic | wc -l                    # 22
```

## 4. コミット

```bash
set -o pipefail
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): gather the §2.1 delta-ring basics in Delta/Basic/

Move the 22 modules for BS §2.1 (Def 2.1, Rem 2.2/2.4/2.7, Ex 2.6, Lemma 2.9, Ex 2.10) from
Delta/ to Delta/Basic/, following formalization-plans/bhatt-scholze-codex-w2-moves.json.
Only import lines change; declaration names and namespaces are unchanged.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
git show --stat -M HEAD | tail -2
```

## 5. 報告してほしいこと

コミットハッシュ、dry-run の出力、受入条件の各コマンドの出力末尾、ビルドのジョブ数と所要時間。
失敗したときは直さずにエラーをそのまま報告する。
