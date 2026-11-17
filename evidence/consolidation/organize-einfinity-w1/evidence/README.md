# OE-W1 段1の証拠目録

今回の最終証拠は調整役の明示承認（11-17、約9.1 MB）により `../preparation/` に保存した。**次回以降、証拠本体は git の外へ置き、git にはこの形式の目録だけを残す。** 新しい証拠本体をこのディレクトリへ追加する方針ではない。

検証対象HEAD：`76dfccc3a93007b6bf54523b528913e87e69effa`。数学ソースの移動は `6678d6a9a`。判定は調整役指定の同一HEADの二回の結果による **verify PASS**。通し実行はsorry閉包中にガードで停止したため、機械のgateは **non-gate** のまま。機械のsummaryやgateを作成・書換えしていない。

| 確認 | 保存先（本目録から相対） | 結果 |
|---|---|---|
| 全106監査を実行した通常verifyのログ | `../preparation/normal-60min-controller.log.gz` | 全106監査成功後、sorry閉包中に時間枠で停止 |
| 106監査の個別実ログ・時間・成功記録 | `../preparation/normal-106-audits-success-records.tar.gz` | 現在の入力キー・実ログの一致を確認、106／106成功 |
| 106監査のHEAD・SHA対応 | `../preparation/normal-106-audits-success-evidence.json.gz` | HEAD・ソース・ログ・時刻・成功記録の対応 |
| 通し実行の資源・終了理由 | `../preparation/normal-60min-resource.json` | rc −15、bounded batch、RSS最大22,934,683,648 bytes |
| 同じHEADのsorry閉包の単独検査 | `../preparation/sorry-alone-success.log.gz`、`sorry-alone-success.json` | rc 0、PASS。102,479定数、許可3件と一致、禁止宣言なし |
| 調整役指定の合成判定 | `../preparation/composite-verification.json` | PASS、machine gateはnon-gate |

抽出補助：`../preparation-code/extract_composite_audits.py`。これは実行済みログと入力キーの一致を読むだけで、監査実行や機械のgateの生成を行わない。root・対象ビルド・v3b・引用照合・独立した106正式監査の証拠は `../preparation/` と報告の各節を参照する。

## 外部に残す原資料

- `/private/tmp/oe-w1-composite-verification/audits-success-evidence.json`
- `/private/tmp/oe-w1-full-verify-005.log` と `.log.json`
- `/private/tmp/oe-w1-final-sorry-alone.log`
- `/private/tmp/oe-w1-before-30ae8948f/`（独立した移動前の環境）
- その他の `/private/tmp/oe-w1-*`（原参照、preview、snapshot、失敗試行、対象ビルド等）

**これらは消していない。取り込み後に調整役が確認して削除する。** 作業レーンから清掃しない。
