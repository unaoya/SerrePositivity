# IF-W0-3 §10.9：環境失敗の再試行・絞り込み検査

**実装と試験は成功。実際の絞り込み検査は PASS（non-gate）、gate:false、終了コード0、retried:0。** 前回環境で失敗した3対象はすべて初回で成功した。ここで報告して待つ。audit_f5 の修正通知前に全体 verify は実行しない。

基準 main `0695a9553d90d07dee632ce65067c6b4d87bf23d` を `git merge --ff-only main` で取り込んだ。専用 worktree `SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3` の中だけで作業した。数学のLeanソース・監査は変更していない。コミットなし。

## 実装

- 通常監査だけを並列poolで実行し、すべてのプロセスが終了してから再試行する。`audit_axioms.lean` はpoolに入れず、その後に直列実行。sorry閉包も直列実行。
- 非零終了の診断が `Too many open files` または `failed to open file` に当たる場合、直列で1回だけ再試行する。`object file ... does not exist` は、pool終了後の確認でそのファイルが実在する場合だけ対象にする。意味的なエラーも混在する場合は再試行しない。
- 初回ログは保持し、再試行ログは `*-retry-1.log` に保存。再試行ではキャッシュを使わない。最後の終了コード・ログを合否に使うので、初回失敗から回復したものは成功に数える。再失敗はFAILのままで、3回目は行わない。
- summary のトップレベル `retried` は再試行した検査の件数（sorryも含む）。各 audit/sorry 段には `retried`（bool）、`retry_reason`、`attempts`（初回・再試行それぞれの終了コード・ログ・秒数など）を記録する。各段の `seconds` は試行時間の合計。
- `gate` の条件式は変えていない。再試行だけでは non-gate にならない。今回の実測は `VERIFY_ONLY_AUDITS` を指定したため non-gate。

## 試験

| 試験 | 結果 | 時間 |
| --- | --- | ---: |
| test_verify_retry.py | 12件成功、終了コード0 | 5.494秒 |
| test_final_tools.py（既存） | 11件成功、終了コード0 | 0.637秒 |
| zsh -n scripts/refactor/verify.sh | 終了コード0 | — |
| git diff --check | 終了コード0 | — |

新しい試験では分類・直列スケジュール・実際の verify.sh の summary 集計を確認した。統合試験だけは一時ディレクトリの模擬lakeを使い、実リポジトリの全体verifyとは区別する。一時ファイルは試験後に削除する。

| 分岐 | 確認結果 |
| --- | --- |
| 環境失敗→成功 | 2試行、成功1件、retried=1、gate:trueを維持 |
| 2回とも環境失敗 | 2試行で停止、FAIL、再試行は1回だけ |
| object file欠落後、ファイルが実在 | 再試行する（相対・絶対パスを確認） |
| object fileが実在しない／ディレクトリのみ | 再試行しない |
| 未知の宣言・未解決の証明・環境/意味エラー混在 | 再試行しない |
| audit_axioms・sorryの環境失敗→成功 | pool終了後に直列、各1回再試行、summary retried=2 |
| VERIFY_ONLY_AUDITS使用時の再試行 | gate:falseを維持 |
| 再試行の記録 | 初回/再試行のログを別々に保持、両終了コードをattemptsに保存 |
| キャッシュ | 再試行では読まず、既存の成功キャッシュ・無効化試験も成功 |

実装中、自分が新しく書いた統合試験の期待段数を、ビルド2段を含む数より1段少なく数えて失敗した。試験用のビルド対象を明示し、期待段数を「通常監査数+4（準備・root・audit-targets・sorry）」へ修正した。上表は修正後の結果。既存監査・既存Leanコードの修正はしていない。

新試験ログ：`.lake/verify/ifw0-3-addendum9/test-verify-retry.log`。試験のコマンド・結果は `test-results.json`。

## 実際の絞り込み実行

```sh
VERIFY_ONLY_AUDITS='scripts/audit_axioms.lean scripts/audit_derived_cell_projective.lean' \
VERIFY_JOBS=3 VERIFY_CACHE=0 zsh scripts/refactor/verify.sh
```

VERIFY_ONLY_AUDITS は通常監査2本を選ぶ。sorry 閉包は verify の常設段として実行されるため、この設定で指定された3対象だけを検査した。監査一覧は99本のまま、実行監査2本、sorry1本。audit_f5 は実行していない。ビルドは省略していない。端末から独立したプロセスで実行し、ログを保存した。

| 段 | 終了コード | 再試行 | 秒 |
| --- | ---: | ---: | ---: |
| preparation / manifest-and-targets | 0 | 0 | 2.999 |
| build / root | 0 | 0 | 22.326 |
| build / audit-targets | 0 | 0 | 20.489 |
| audit / scripts/audit_axioms.lean | 0 | 0 | 302.203 |
| audit / scripts/audit_derived_cell_projective.lean | 0 | 0 | 33.801 |
| sorry / scripts/refactor/audit_sorries.lean | 0 | 0 | 198.790 |
| verify 全体 | 0 | 0 | 660.277 |

全体の秒数には層レポート・依存情報準備・集計も含む。監査poolは33.803秒、直列audit_axiomsを含む監査段は336.006秒。

```json
{
  "status": "PASS",
  "gate": false,
  "retried": 0,
  "audit_count": 99,
  "executed_audit_count": 2,
  "target_count": 2,
  "counts": {
    "build": {
      "success": 2,
      "failure": 0,
      "known": 0
    },
    "audit": {
      "success": 2,
      "failure": 0,
      "known": 0
    },
    "sorry": {
      "success": 1,
      "failure": 0,
      "known": 0
    },
    "preparation": {
      "success": 1,
      "failure": 0,
      "known": 0
    }
  },
  "failures": []
}
```

runner の jobs=3、cache_enabled=false、全段 cached=false を確認した。3対象は各1試行で成功したため、今回の実測では環境エラーの再現も再試行もなかった。再試行分岐は上記の模擬試験で確認した。

sorry閉包の実出力：

```text
visited 103485 constants; root: SerrePositivity.main_statement
direct sorry declarations: [SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3,
 SerrePositivity.Section4.supportedRankK0_descent,
 SerrePositivity.theorem_3_1_K0]
sorry declarations grouped by parent: [SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3,
 SerrePositivity.Section4.supportedRankK0_descent,
 SerrePositivity.theorem_3_1_K0]
SerrePositivity.Inputs.Homotopy.kanQuillen_model_exists in closure: false
sorry closure PASS
```

全ログを検索した結果、エラー診断は0件。`log-diagnostics.json` に記録した。summary全文・各段と各試行のログは `.lake/verify/ifw0-3-addendum9/real-summary.json` と同ディレクトリに保存済み。

## 今回の変更・待機位置

- `scripts/refactor/verify_runner.py`：環境失敗の識別、1回の直列再試行、重い検査の直列化、試行記録。
- `scripts/refactor/verify.sh`：summaryへの試行情報・retried件数の反映。
- `scripts/refactor/test_verify_retry.py`：新しい12試験。
- `scripts/refactor/targets/w1-environment-retry-report.md`：本報告。
- `scripts/refactor/targets/w1.md`：§10.9の成功と全体verify待ちの状態を追記。

既存のW1 JSON・他の前回までの変更は保持した。audit_f5 は変更していない。W1 の全体 gate:true PASS はまだ未確認であり、前回のFAILをこの非gate実行で置き換えない。audit_f5修正の通知を待ち、その後の全体verifyは別途1回だけ実行する。
