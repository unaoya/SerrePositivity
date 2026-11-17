# B3 検収用資料

数学基準 `c5c4436c0`。B2検収済み範囲を新しいmainの増分へ再構成して適用した。文書だけのmain更新は許容し、ビルド入力の変更は停止する。

| 検査 | 結果 |
|---|---|
| 対象と前提 | 10,227対象・前提込み29,776本、全件成功 |
| root | 31,251ジョブ成功。full verify内でも再実行成功 |
| 正式監査 | 106/106成功。E∞の引用名2件を訂正し当該監査を再実行 |
| full verify | 正式ゲートPASS、監査106本をキャッシュなしで再実行 |
| 保存比較 | 元10,195モジュール、未説明0 |
| 属性・タグ | 引用1,883組・Kerodon672組、欠落・余分0 |
| 宣言名 | 前140,687・後140,705記録、著者宣言の未対応0 |
| 互換 | 90名・20包み、二重instance/simpなし |

## 主な資料

- `full-verify-summary.json`・`full-verify-current-run.tar.gz`：現在の正式verifyの集計と、その実行が参照するログだけ。
- `all-audits-complete.json`・`formal-audit-log-index.json`：正式監査106本の受理した実行。
- `formal-audits-complete-logs.tar.gz`：初回と訂正後E∞のログ。初回失敗の履歴は残す。
- `preservation-evidence.tar.gz`：178組の比較receipt・結果・前後356snapshotの検証済みSHA。
- `preservation-snapshot-source.tar.gz`：検査用実行ソースと元ソース・実行ソース・binaryのSHA。
- `declaration-names.jsonl.gz`・`declaration-inventory-{before,after}.jsonl.gz`：所有元付き実名と完全な索引。compiler-onlyを順番で対応させない。
- `full-path-table.json.gz`：元パスから新パス・分割先への全表。
- `retained-and-deferred.json`：追加取り下げ0、指定維持、B3′へ残す既存の辺と範囲。
- `completion-audit.json`・`approved-scope-audit.json`：全要件と具体的な承認内容の照合。
- `B4-README.md`：元環境での採取・一行のrewriteコマンド・引用名の扱い。
- `b4-branch-impact.json`・`b4-*-files.json`：4枝のgit参照だけに基づく対象一覧。
- `module-map.json.gz`・`namespace-rewrite-map.json.gz`・`namespace-map.json.gz`：通常import・書き換え用実名・恒等6メソッドを含む全名表。

## 残す既存事項

層の順序・実装境界・欠落import・循環0。厳密な節順序の15辺は凍結mainから存在し、両端ともB3で移動していない。BSの論文順逆向き34辺（直接31・見せ直し3）は承認どおり一覧のみ。免除を増やさずB3′で確認する。Kerodon7.4→9.3の1辺は明示的な承認済み例外。

mainへの取り込みは調整役が行う。B4は取り込み前の原環境で参照を採取し、枝のHEADが一覧から進んでいれば対象を更新する。
