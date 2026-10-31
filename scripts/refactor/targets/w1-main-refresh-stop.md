# IF-W0-3 §7-1：最新mainでの再検査・停止報告

基準 `cdbefbde9342369033ac4449c9868501e0f7d078`、ブランチ `infra/if-w0-3`。`git merge --ff-only main` で取り込んだ。今回の検査開始から停止まで 1673.147 秒（約27分53秒）。コミット・W2aへの進行なし。

**層検査・68件のJSON検査・手作業込みの模擬は成功。全体verifyは、既存のaudit_f5の旧importを検出して停止したため未完。PASS・gate:trueは確認できていない。**

## 停止理由

`scripts/audit_f5.lean:2` が `SerrePositivity.CommutativeAlgebra.AdicBoundedTorsionQuotient` をimportしている。対象は `f00bad23f` で `SerrePositivity/CommutativeAlgebra/Adic/BoundedTorsionQuotient.lean` へ再編されており、旧ファイルは存在しない。前回のaudit_clmstのPowerSeriesCoefficientQuotient参照は今回のmainで解消済み。今回のaudit_f5は変更していない。

失敗の署名：監査対象ビルド / CommutativeAlgebra.AdicBoundedTorsionQuotient / ファイル欠落 error code 2。診断の3行（保存したbuild-2.log:22289）：

```text
✖ [28254/28268] Running SerrePositivity.CommutativeAlgebra.AdicBoundedTorsionQuotient
error: no such file or directory (error code: 2)
  file: /Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/SerrePositivity/CommutativeAlgebra/AdicBoundedTorsionQuotient.lean
```

共通§0に従って今回起動したプロセス群だけをSIGTERMで停止。自然終了の終了コードは取得していない。99監査とsorry検査は未実行、今回のsummary.jsonは未生成。以前のsummaryを今回の結果として使わない。ビルドログ全体の検索で、監査対象ビルドのエラーは上の1件。ルートビルド・層・validator・模擬のログはエラー0件。

## 成功済みの検査と時間

| 検査 | コマンド | 終了コード | 秒 |
| --- | --- | ---: | ---: |
| layers | `/opt/homebrew/opt/python@3.14/bin/python3.14 -B scripts/refactor/layer_check.py --report` | 0 | 30.673 |
| validator | `/opt/homebrew/opt/python@3.14/bin/python3.14 -B scripts/refactor/validate_targets.py scripts/refactor/targets/w1.json` | 0 | 31.94 |
| simulation | `python3 -B scripts/refactor/targets_builder.py --plans ...` | 0 | 37.52 |
| verify準備 | 監査一覧・ビルド対象収集 | 0 | 4.363 |
| ルートbuild | `lake build SerrePositivity` | 0 | 1417.450 |
| 監査対象build | `lake build <全監査のimport先>` | 中断 | — |

全体verifyのコマンドは `VERIFY_JOBS=3 VERIFY_CACHE=0 zsh scripts/refactor/verify.sh`。今回の試行は1回のみ。監査結果キャッシュを無効にし、試験用の環境変数は設定していない。監査一覧は99本で増減なし。直接ビルド対象は6,533→6,502本。準備記録のexecuted_audit_count=99は予定件数で、完了件数ではない。

## 数値の比較

層の組ごとの直接違反、全ratchet_metrics、各tierの入口辺一覧は、前・JSON後・手作業込みの3段階すべてで旧基準b11b42cedと一致した。変わったのはグラフ全体の本数と辺数。

| 段階 | モジュール数：旧→新 | 辺数：旧→新 |
| --- | ---: | ---: |
| before | 34073 → 34042 | 113703 → 113620 |
| targets | 34076 → 34045 | 113811 → 113728 |
| manual | 34071 → 34040 | 113796 → 113713 |

| 指標 | 前 | JSON後 | 手作業込み |
| --- | ---: | ---: | ---: |
| 直接違反 | 371 | 325 | 318 |
| W1禁止閉包 / 入口辺 | 2986 / 32 | 1 / 3 | 1 / 3 |
| W2a・W2b禁止閉包 / 入口辺 | 3257 / 90 | 257 / 59 | 257 / 59 |
| 中核のDifferentialGraded | 910 | 0 | 0 |
| 中核のEInfinity | 0 | 0 | 0 |

**W1終了条件の模擬判定は引き続き達成**。残るW1禁止閉包1本は、W2b/R73へ回すFilteredSpaceBridgeInput。JSONの構成はmove 62・split 3・reimport 3・archive 0、保留13で維持。層指標の増加0、validator PASS。

## 今回変更した計画と作業木

- `w1.json`：ルートreimportの完全なimport一覧を最新mainへ追従させた。mainの追加14本・削除24本を反映し、承認済みのInfinityCategories入口追加5本を維持。他の項目は変更なし。これにより削除済み可換代数ファイルを再導入しない。
- `w1.md`：現在の停止状況と本報告へのリンクを追記。三案比較・roof15本・保存証拠は保持。
- `w1-main-refresh-stop.md`：本報告。
- 数学のLeanソース、監査、道具のコードは今回変更なし。既存の所有範囲内の未コミット変更は保持。`git diff --check`成功。

## 証拠の所在

今回のログとJSONは `.lake/verify/ifw0-3-resume-cdbefbde9/`。`state.json`に各コマンドの完全な引数・終了コード・時間、`layers.json`、`targets-w1.json`、`simulation/`に層・JSON・手作業込みの結果、`metric-comparison.json`に前回との一致判定、`log-audit.json`に全ログのエラー検索結果、`unexpected-build-stop.json`に停止記録を保存した。標準の `.lake/verify/targets-w1.json` も今回の結果へ更新済み。
