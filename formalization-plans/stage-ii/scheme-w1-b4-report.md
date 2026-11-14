# SC-W1：B4 途中報告（採取器の失敗）

2026-11-14。B4 は未完了。main の取り込み、取り込み後の対象ビルド・監査はまだ行っていない。

一覧：済み 7／全体 12（うち追加 3）。これは 2g-1 の主項目の台帳であり、B4 の件数とは別。

## 対象と固定したソース

- worktree：`SerrePositivity-scheme`、枝：`math/scheme`。
- 検証済み数学の先端：`122ac972cd74c5d1d2a04ca623dab53f921c6c37`。
- 基準：`c5c4436c0`。観測した main：`efa846fe81f40ac663cff5af62f55b901763d676`（B3 `16d6b4547` を含む）。
- 対象は基準から枝で追加・変更した Lean 289 本。drafts を除き、全て AlgebraicGeometry 配下。提供された 284 本に、その後に検証済みの IntegralModel 系 5 本を加えた。全一覧は [files.json](scheme-w1-b4/files.json)。
- main の B4-README と citation-attributes.md §14 に従い、共有の `bulk_namespace.py` を使った。展開した `namespace-rewrite-map.json` は modules 5,337、namespaces 45、declarations 19。通常 import の module-map との照合は該当 0。
- 全 289 本の SHA-256 と採取前 HEAD を [collection-state.json](scheme-w1-b4/collection-state.json) に保存した。失敗後にも全バイトが不変であることを確認した。Lean の修正、資源上限の変更、採取器の変更は行っていない。

## 完了した採取とプレビュー

各 20 本の組 00〜08、合計 180 本で collect と rewrite が正常終了。各組の review.json は空、ソース差分は 0 本・0 行。参照が空のための結果ではなく、例として組 07 の一つの capture に refs 543、commands 7 がある。

共有鍵は `--class impl --wait 3600`。一つの worktree からの待ちは常に一つとし、各採取は `gtimeout --kill-after=3s 280` で区切った。組の間には鍵を解放した。

原ソース、表、索引、プレビュー、全ログは作業木内の `formalization-plans/stage-ii/scheme-drafts/b4/` に保持した。`index-00`〜`index-08` のみ完全な files.json を持つ。これらは main 取り込み前のソースに対するものであり、取り込み後のソースへ流用しない。

## 失敗の診断

組 09 は 6 本を採取した後、次で終了コード 1：

```text
SerrePositivity/AlgebraicGeometry/ProjectivePerfCechH0SquareData.lean:59:0:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

失敗ファイルより後の 13 本を新しい出力先（09-tail）で切り分けたところ、10 本を採取した後、次で終了コード 1：

```text
SerrePositivity/AlgebraicGeometry/ProjectivePerfectAffineCechComparison.lean:30:4:
(deterministic) timeout at `«abstract nested proofs»`, maximum number of heartbeats (200000) has been reached
```

いずれも 280 秒の壁時計の時間切れではなく、採取器が実行する Lean 内部の heartbeat 上限による失敗。採取器は Lake の setup を使い、`Elab.async` を false にする実装である。この同期化が失敗の原因かどうかは未確定。通常の対象ビルド成功と同期採取の違いを、道具側で確認する必要がある。

完全なログは `collect-09.log` と `collect-09-tail.log` に保存した。エラーとログの SHA-256 も collection-state.json に記録した。部分索引 6 本・10 本は診断用に残しただけで、組の成功数にもプレビュー完了数にも含めない。組 10〜14 は未実行。

## 次の作業

採取器の失敗を解消した後、固定した取り込み前ソースで未完の採取を新しい出力先へ行い、全 289 本のプレビューを揃える。保留 0 と差分を確認してから main を取り込み、差分を適用する。その後、対象ビルドと小さい監査を通して B4 の完了を報告する。今回の 180 本の保留 0 を、全対象の保留 0 と読み替えない。

数学の直前の検証は 122ac972c に記録済み（AlgebraicGeometry の対象ビルド 4,824 ジョブ成功、新しい IntegralModel 系 5 本の小監査 26 宣言・標準三公理）。これは取り込み前の検証であり、B4 後の検証ではない。B4 が済んでから、2g-1 の A07 内の I03（実際の filtered colimit）へ戻る。
