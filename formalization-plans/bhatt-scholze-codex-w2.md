# Codex 作業指示書 BS-W2：Delta/ 直下を原典 §2.1〜§2.4 の節ごとのサブディレクトリにまとめる

作成：2026-10-25（BS 作業チャット）。宛先：Codex。**BS-W1 の作業 3b のコミットが済んでから始める。**
宣言の名前・名前空間・型・証明は変えない。変えるのはモジュールの場所と import 行だけ。

## 0. 前提

BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。

## 1. 移すもの

`SerrePositivity/BhattScholze/Delta/` 直下の 55 本をすべて次のサブディレクトリへ移す。ファイル名は変えない。
移動先は [bhatt-scholze-codex-w2-moves.json](bhatt-scholze-codex-w2-moves.json)。移動後の `Delta/` 直下にはファイルが残らない。

| 移動先 | 原典（著者版） | モジュール |
| --- | --- | --- |
| `Delta/Basic/`（21） | §2.1：Def 2.1、Rem 2.2・2.4・2.7、Lemma 2.9、Ex 2.10 | `DeltaRing`、`DeltaIdentities`、`DeltaFrobenius`、`DeltaFrobeniusNaturality`、`DeltaSectionNaturality`、`DeltaTransport`、`WittTwoMap`、`WittTwoUnits`、`DeltaQuotient`、`DeltaIdeal`、`DeltaClosureGeneration`、`DeltaDirectLimit`、`DeltaSubring`、`DeltaWittGhost*`（7 本）、`DeltaWittJetComparison` |
| `Delta/Extension/`（13） | §2.2：Lemma 2.15・Rem 2.16（局所化）、Lemma 2.17（I 進完備化）、Lemma 2.18（導来 (p,d) 完備化の H⁰ への延長） | `DeltaLocalization`、`DeltaLocalizationSaturation`、`DeltaAdic*`（5 本）、`DeltaPDCompletion`、`DeltaPDCompletionUniversal`、`DeltaFrobeniusComplete`、`WittTwoModuleComplete`、`WittTwoModuleSequence`、`WittTwoPDComplete` |
| `Delta/Distinguished/`（2） | §2.3：Ex 2.20(1)、Lemma 2.23〜2.25 | `Distinguished`、`DeltaPrime` |
| `Delta/Perfect/`（13） | §2.4：Rem 2.27、Lemma 2.28、Cor 2.31、Lemma 2.32〜2.34 | `DeltaPerfection`、`DeltaPerfectionUniversal`、`DeltaTorsion`、`DeltaRankOne`、`PerfectDeltaFrobenius`、`PerfectDeltaModP`、`PerfectDeltaWittRecovery`、`WittDelta`、`WittDistinguished`、`DistinguishedPowerTorsion`、`DistinguishedQuotientComplete`、`DistinguishedRegular`、`DistinguishedTorsion` |
| `Delta/Free/`（+2） | 原典の番号なし。相対自由 δ 環の有限段の計算で使う補題 | `DeltaResidueArithmetic`、`DeltaAdditionCarryProduct` |
| `Delta/Division/`（+2） | 原典の番号なし。δ 除算で使うねじれの除去 | `DeltaTorsionReduction`、`DeltaPTorsionReduction` |
| `RootedExtension/`（+2） | 原典の番号なし。B4 の完全化と PD 完備化の順序の比較（RootedExtension と Andre だけが使う） | `DeltaPDCompletionPerfectionComparison`、`DeltaPDCompletionPerfectionUniversal` |

Lemma 2.34 は distinguished 元の性質だが、原典では §2.4 にあるので `Delta/Perfect/` に入れる。
既存の `Delta/Free/`（Lemma 2.11）、`Delta/Division/`、`Delta/DividedPower/`（§2.5）はそのまま。

## 2. 実行

所有範囲だけを書き換える汎用スクリプト [bhatt-scholze-move-modules.py](bhatt-scholze-move-modules.py) を使う
（W1 の apply スクリプトの計画ファイルを引数にした版。動作は同じ）。

```bash
set -o pipefail
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST    # 空であること（W1 がコミット済み）
python3 formalization-plans/bhatt-scholze-move-modules.py formalization-plans/bhatt-scholze-codex-w2-moves.json
python3 formalization-plans/bhatt-scholze-move-modules.py formalization-plans/bhatt-scholze-codex-w2-moves.json --apply
```

dry-run の期待値（2026-10-25 11:40、W1 の移動を適用した作業ツリーで確認。W1 のスタブ 32 本が未追跡でも追跡済みでも同じ）：

```text
"moves": 55, "stubs": 0, "owned_files_rewritten": 147, "foreign_importers_left_unchanged": {}, "foreign_imports_without_stub": []
```

件数が違う場合は `--apply` せずに報告する。所有範囲外から import されるモジュールはないので、スタブは作らない（`--stubs` は使わない）。

## 3. 受入条件

BS-W1 §5 の「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
構造監査、CommutativeAlgebra の四モジュール）を実行し、すべてエラーなし・終了 0。加えて次を確認する。

```bash
git diff --cached -M --stat | tail -1     # 55 本の rename と import 行の変更だけ
git diff --cached -M --diff-filter=RM -- SerrePositivity scripts | grep -E '^[-+]' | grep -vE '^(\+\+\+|---) ' \
  | grep -vE '^[-+][ \t]*(public )?import '    # 出力が空
ls SerrePositivity/BhattScholze/Delta/*.lean 2>/dev/null | wc -l       # 0（直下に残らない）
```

## 4. コミット

```bash
set -o pipefail
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): group the Delta/ modules by BS sections 2.1-2.4

Move the 55 top-level Delta/ modules into Delta/Basic/ (§2.1), Delta/Extension/ (§2.2),
Delta/Distinguished/ (§2.3) and Delta/Perfect/ (§2.4); six helpers without a BS number go to
Delta/Free/, Delta/Division/ and RootedExtension/ next to their users. Plan:
formalization-plans/bhatt-scholze-codex-w2-moves.json.
Only import lines change; declaration names and namespaces are unchanged.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
git show --stat -M HEAD | tail -2
```

## 5. 報告してほしいこと

コミットハッシュ、dry-run の出力、受入条件の各コマンドの出力末尾、ビルドのジョブ数と所要時間。
失敗したときは直さずにエラーをそのまま報告する。
