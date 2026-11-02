# DG-W2(b) §16：universe スコープの修正と D4 再適用

**停止点 2：verify PASS・gate:true。保存比較の未説明差分 0。**

## 履歴

旧 HEAD `1ff0ac691` は `codex/dg-w2-before-universe-fix` に保持した。
指定どおり `git reset --hard 0fe63746a`（D3 直後）へ戻し、main の `9c36a95f9` を `60889ec9d` で取り込んだ。衝突なし。scratch は `887896bba` のまま。

| 区分 | 旧コミット | 新コミット |
|---|---|---|
| 道具・回帰試験 | — | `7e1fb1dea` |
| D4 | `f7933ec9d` | `fb94eb45e` |
| D5 | `3a9f78a1a` | `e57011761` |
| 名前の隠蔽の修飾 | `3a08fb3c7` | `34cf26c3e` |
| heartbeat | `023b0c098` | `b2c92fb64` |
| 外部 import・監査一覧 | — | `3ec3cae16` |
| import 境界の道具修正・試験 | — | `58d8e1551` |
| 監査 assertion の復元 | — | `fee95cbf2` |
| layers.json | — | `f911ddf9b` |
| 監査一覧の重複と旧名の修正 | — | `fa7c0e898` |

`merge_modules.py` は、元の universe 行を順序を保って各元ファイルの section の直後へ置く。統合先の先頭の和は廃止。972 元ファイルに universe 行が各 1 本、7 元ファイルにはない。再生成 78 本の最大は 1,630 行、1,700 行超過 0。旧生成結果との差は universe 行と空行だけ（D5・修飾・heartbeat の再適用後に比較）。

道具の既存ファイルの修正は `merge_modules.py` だけ。試験は新しい `test_merge_universe_order.py` と `test_merge_import_boundaries.py` に追加した。

## 試験と内部ビルド

- opt-in 試験 1 件 PASS（17.613 秒）。`universe v u`／`universe u v` の独立した 2 ファイルを統合し、4 宣言の型ハッシュ・保存比較・明示 universe 表示の一致を確認。旧方式で先頭へ集約する対照例では `secondId` の型ハッシュ不一致を検出。
- 通常の `test_merge_modules.py`：20 PASS、1 skip、1 FAIL。FAIL は既存の `test_snapshot_cli_delegates_and_ignores_module`（module の違いを無視する旧期待値）。修正前の HEAD の道具でも同じ失敗を再現した。所有範囲外の比較道具・旧試験は編集していない。
- 内部 111 本：PASS、580.234 秒、依存先を含む新規ビルド 117 本。Boundary の heartbeat 行も維持して成功。
- after snapshot：112 本（修飾を確認する ModuleShiftOpposite を含む）、85.423 秒、PASS。before は前回採った scratch の新規則 snapshot 1,013 本をそのまま使用。
- fresh shell の Lake キャッシュ設定と `with_build_lock.sh` の共有鍵を使用。main の作業木での編集・ビルドなし。

## 保存比較：個別レビュー後 PASS

機械比較の元データは **FAIL、393 件**として保持する。内訳は追加 246・本体 96・型 28・補助群 23。前回の 418 件から、宇宙順序に由来する 25 件が消えた。

宇宙順序が変わっていた **13 宣言すべて**で、型と本体の pp、明示引数の順序が元に戻った。旧差分の 163 宣言は通常 pp 同一 158、生成された証明参照名だけの差 5。その 5 組の定理は型ハッシュ・公理・属性も同一。

残り 393 件は §15–16／IF-W0-3 §10.34 の規則で個別に照合した。

| 項目 | 件数 | 根拠 |
|---|---:|---|
| 追加扱いだが同名の生データが一致 | 240 | 型・本体ハッシュ・kind・公理・属性が同一。統合先の一部構文をソース解析器が扱えず、親への束ね方が変わる |
| 生成等式補題などの追加扱い | 6 | pp の型・公理が同一。4 件は before でも名前の指定時に遅延生成される |
| 型／本体のハッシュ差 | 119 | pp の型・本体が同一 |
| 型／本体の生成証明参照名の差 | 5 | pp の差が、同じ型ハッシュを持つ生成定理の参照名だけ |
| 補助群の分類差 | 23 | 128 個の片側のみにある値のうち 124 は同名の生データで一致。残りは生成 matcher の共有／遅延生成を個別確認 |

matcher の対応 3 組も型・本体ハッシュ・公理・属性がすべて一致：

- `DGCellAttachment.Family.includeDoubleFace.match_1.splitter` → `…negateDoubleFace.match_1.splitter`
- `DGGeneratedHomWord.encode.match_1.splitter` → `…evaluate.match_1.splitter`
- `DGQuotient.includeDoubleFace.match_1.splitter` → `…negateDoubleFace.match_1.splitter`

未確定だった補助 10 件は #print・通常／明示 #check・#print axioms で再照合し、最終採取は両側とも終了 0。生成された private 名は before での遅延生成に由来し、比較対象の型と公理は同一。比較道具の規則や元ハッシュを変更して PASS にしたものではない。

全 393 件の判定は `preservation-review.json`（`PASS_AFTER_REVIEW`、未説明 0）に保存。元の `comparison.json` も保持する。

## 外部の付け替えと下流

最終差分は 348 ファイル（本体 341・監査 7）。本体は import 以外が不変であることを独立した行単位の比較で確認した。監査は import とモジュール一覧を更新し、DG／Shared の領域監査を再生成。監査のモジュール名リテラルは当初 138 箇所、verify で見つけた漏れ 2 箇所を含め計 140 箇所を付け替え、重複 5 行を除いた。ルートには移動した `Asymptotic.DGVerdier.OrderSquare` を直接 import した。保存検査後の対象 112 本に追加変更なし。

| 下流 round | 結果 | 対象数 | 秒 | 新規ビルド | 実モジュールの失敗 |
|---|---|---:|---:|---:|---:|
| 1 | FAIL（対象抽出の誤り 83 件） | 6,945 | 5,094.402 | 5,750 | 0 |
| 2 | PASS | 6,862 | 16.255 | 0 | 0 |

round 1 の誤りと修正は下記。正規の対象は verify.sh の抽出結果と完全一致し、欠落 0。下流の追加 import 補充・名前修飾は不要だった。各 round は `dg-w2-b-downstream-imports.json` と成果物に記録した。

## 層の検査

`f911ddf9b` で DG の規則と承認済みの PerfectComplex への例外 3 辺を登録した。

- `DG.Perfect.Basic` → `PerfectComplex.KoszulLength`
- `DG.Perfect.Ring.FiniteProjectiveComparison` → `PerfectComplex.BiproductPerfect`
- `DG.Perfect.Ring.FiniteProjectiveComparison` → `PerfectComplex.Perfect.HomotopyCategory`

`DG` は `SerrePositivity.DifferentialGraded` の略。DG の raw 直接違反 3 はこの 3 辺だけで、未承認の直接違反 0。

| 既存 core | 禁止モジュール（前→後） | 直接違反（前→後） | 閉包の対（前→後） |
|---|---|---|---|
| W1 | 1→1 | 3→3 | 11→11 |
| W2a | 166→166 | 28→28 | 316,547→316,547 |
| W2b | 166→166 | 294→294 | 316,547→316,547 |

同じ現行設定で旧ソースを測った基準と比較し、各 core モジュールごとの禁止閉包の増加も 0。`layer-comparison.json` に全値を保持。

## verify

**PASS・gate:true**。`VERIFY_JOBS=6 VERIFY_MEMORY_GB=45 VERIFY_CACHE=0`、共有鍵の下で完走。検証 HEAD は `fa7c0e898b9bc29009d04744725cb38126b62402`。所要 1871.362 秒。

```text
PASS build(success=2,failure=0,known=0) audit(success=100,failure=0,known=0) sorry(success=1,failure=0,known=0) preparation(success=1,failure=0,known=0) retried=0
```

監査 100/100 本を実行し、監査対象 6,862 本。監査結果キャッシュの利用なし。環境エラーの再試行 0。スケジューラーの最大同時実行 6、RSS 見積もりの最大予約 44.972 GB。同時 RSS の実測ピーク 50.770 GB。45 GB は過去の測定値に基づく予約枠で、プロセスの RSS を強制制限する値ではない。RSS 測定欠落 0。sorry の閉包検査も成功した。終了後、DG の共有鍵は解放済み。

停止点 2 に到達。以降の束・main への取り込みは行っていない。

## 記録

`.lake/verify/dg-w2-b-s16/`（作業原本 `/tmp/dgw2b-s16/`）に保存。before snapshot は `.lake/verify/dg-w2-b-v2/before.json`。回帰試験の成果物は `.lake/verify/merge-universe-order/`。
この報告が停止点 2 の完了報告。最終 verify の summary・runner・各監査ログは同ディレクトリの `verify/` に保管。比較コマンドの FAIL とレビュー後の PASS は区別して保存する。

verify の RSS 実測初期値は `../SerrePositivity-ifw0-3/.lake/verify/audit-stats.json` の 101 件（測定コミット a26eb3351）をコピーした。DG と main には実測ファイルがなかったため。監査結果キャッシュの再利用ではなく、今回の実測で更新されるスケジューリング用の見積もり。出所と SHA-256 は `audit-stats-seed.json` に記録。

## 下流 round 1 中に見つけた import 解析の不具合

`assert_no_sorry` を import の続きと誤認し、同じトークンの重複除去で 11 監査ファイルのコマンド名 70 個を消していた。全行を b2c92fb64 の記述へ復元した。独立した行単位の差分検査により、本体 341 ファイルにはこの誤変更がなく、復元後は監査も import・モジュール一覧以外に差がないことを確認。`merge_modules.py` の境界に監査コマンドを加え、Python 回帰試験 2 件 PASS。既存 layer_check.py 等には変更なし。

round 1 の実行器も元の layer_check.imports を使ったため、監査内の定理名等 83 件をビルド対象と誤認していた。正規対象の取りこぼしは 0。round 1 は正規モジュールのビルドを完了し、存在しない対象だけが失敗した。round 2 は修正済みの import 解析による 6,862 対象で PASS。存在しない対象の失敗も記録に保持する。最初の差分 359 ファイルから、元と完全に同じ内容へ復元した 11 監査ファイルを除き、最終差分は 348 ファイルになった。

## verify round 1 で見つけた監査一覧の漏れ

最初の verify（HEAD f911ddf9b）は 1,792.745 秒で FAIL。ビルド 2 件・監査 97 件・sorry 閉包 1 件は成功、監査 3 件のみ失敗した（既知の失敗 0・再試行 0）。

- `audit_dg_cell_comparison.lean`：統合で `Resolution.Cell` が 4 回現れ、idxOf? が最初だけを数えるため、重複した項目を宣言 0 と判定。重複 3 行を除いた。
- `audit_dg_perfect_projective_image.lean`：単独の `target` に旧名 `Morita.PerfectProjectiveImage` が残っていた。`Morita.Perfect` に付け替えた。
- `audit_dg_quotient_parameter.lean`：配列末尾の `Quotient.ParameterExtension` を `Quotient.DerivedComparison.Filtration` に付け替え、同じ配列の重複 2 行を除いた。

修正後の監査対象の集合は元の集合を対応表で写したものと一致し、監査内の旧モジュール名の残存は 0。検査処理・公理の許可条件は不変。修正した 3 本だけの確認は全て PASS（34.565／13.564／16.364 秒）。`fa7c0e898` に分けて記録した。全 verify を同じ条件で再実行し PASS した（上記）。最初の全結果は `.lake/verify/dg-w2-b-s16/verify-round-1/` に保存し、上書きしない。
