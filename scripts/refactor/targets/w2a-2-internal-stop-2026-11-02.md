# IF-W2a-2 内部検証の停止（2026-11-02）

## 状態

main の `8a6f1d918` を取り込んだ（merge `7a1fe85bf`）。3ea13677a、7e1fb1dea、58d8e1551 を含む。取り込み後の `merge_modules.py --check --max-lines 1700` は PASS（25 群・95 元ファイル）。循環 0。R76 → R77 → R67 の適用は完了したが、内部ビルドで 2 モジュールが失敗し停止。下流の一回ビルド・保存比較・verify は未実行。

## 実行結果

| 段 | 結果 | 秒 |
|---|---|---:|
| キャッシュから before 環境を復元（43 根） | PASS、7,603 jobs、新規 Built 0 | 6.394 |
| proof-irrelevant before snapshot（16 本ずつ） | PASS、273 モジュール・3,526 行 | 220.358 |
| 宣言単位 preflight | PASS、参照対 9,449、失われる参照 0、Foundation 禁止参照 0 | — |
| R76 適用 | PASS、move 9 | 36.169 |
| R77 適用 | PASS、95 → 25 | 34.572 |
| R67 適用 | PASS、move 3 | 43.387 |
| 内部ビルド（37 対象、根 10） | FAIL、exit 1、Built 245、失敗 2 モジュール | 410.917 |

時間は各コマンドの実測。内部ビルドの worker タスク全体は 479.052 秒（キャッシュ成果物の集計等を含む）。R77 の import 重複除去で残った空白のみの 14 行を取り除き、`git diff --check` を再実行して PASS。道具本体や宣言には変更していない。

## 失敗と診断

### RelativeBoundaryFunctor（158・169 行）

`Functor.map_id` が `CategoryTheory.Functor.map_id` ではなく applicative の補題へ解決され、`rw` に失敗。

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  fun x ↦ id <$> x
in the target expression
```

DG-W2 §14 の完全修飾の対象と判断できるが、もう一方の停止条件が判明したため**未修正**。before snapshot を追加採取済み。

### Spectra/ModelCategory/SimplicialLevel（最初のエラー 45:22）

```text
Application type mismatch: The argument
  Cardinal.aleph0
has type Cardinal.{u} ... but is expected to have type Cardinal.{0}
```

後続に ModelCategory の instance 合成失敗、rfl の不一致等が連鎖する。

束の直前の scratch worktree（`7a1fe85bf`）をキャッシュから復元。元ソースの `lake env lean` は exit 0（4.259 秒）、現在の同一ソースでは exit 1（5.602 秒）。`levelModelCategoryOfMonoidalGenerators` と `_generated` の `#print`（`pp.explicit true`・`pp.universes true`）は前後でバイト単位に一致した。2 箇所の呼出しを `SerrePositivity.SpectrumLevelModel.…` へ完全修飾した**診断用ファイル**でも exit 1（5.347 秒）、同じ宇宙の不一致が残った。元の Lean ファイルは変更していない。

現時点の候補は import の和で環境が広がったことによる暗黙の宇宙・インスタンス推論の変化。原因の instance までは未特定。完全修飾だけでは解消せず、宇宙引数の明示等を宣言へ加える処置はまだ行っていない。IF-W2a-2 §4 の宣言変更禁止と §10.31 の停止規則に従い、ここで判断を求める。

## コミットと再開時の状態

| 内容 | commit |
|---|---|
| R76 | `36f9b1bd0` |
| R77 | `3ae691eba` |
| R67 | `ecc0be826` |

すべて `infra/if-w2a-2` の `git commit --only`。main は変更していない。

コミットには外部 import の付け替えまで含むが、内部検証を先に行うため、内部ビルドに不要な外部利用者 **92 ファイル**は worktree 上だけ before の内容へ戻して保留している。これは意図した未コミット差分。内部の上流に当たる外部利用者 76 モジュールは先行して付け替え済み。保留ファイルの一覧と before/after SHA256 は `deferred-imports.json` にある。内部検証が通った後に各ファイルの hash を確認して HEAD の内容へ戻すこと。全差分を一括 commit/reset しない。

下流の対象は同一名の統合分を整理して **11,818 本**（旧名では 11,888 本）。失敗 2 ファイルに修正はまだない。停止時は worker の未実行タスクを保留し共有鍵を解放する。診断 scratch は削除する。

ログ・コマンド・前後 snapshot・比較記録は `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/.lake/verify/ifw2a2-batch` に保存。主要ファイルは `internal-round1/build.log`・`state.json`、`diagnose/source-comparison.json`、`diagnose/before.json`、`diagnose/before-probe.log`・`after-probe.log`、`stop.json`。ログ全体を error／PANIC で確認した。全体保存比較の PASS や verify の PASS は主張しない。

補足：診断中の `ps` で `SerrePositivity-refactor-1-4` の別レーンの `lake build` を検出した（こちらの共有鍵とは独立）。こちらの診断復元はキャッシュのみで新規 Built 0。その後は単独の Lean 診断だけで、内部／下流ビルドは再開していない。共有鍵の解放と scratch worktree の削除を確認済み。
