# SC-W1：B4′ 完了報告

2026-11-15。**B4′ 完了**。main `58d6a0de9` を `math/scheme` に取り込み、対象ビルドと新規モジュールの小監査を確認した。2g-2 の停止点ではない。続いて G3・S04 の Segre の大域の射・ファイバー積・有限冪の表示へ戻る。

2g-2 の一覧：済み0／全体3（うち追加0）。G3〜G5 を数え、B4′ や既存の構成の法則は追加の主項目に数えない。

## 結果

| 項目 | 確認した結果 |
| --- | --- |
| 取り込み前の検証済み先端 | `cac6b317d` |
| main の取り込み | `0f41722a4`、第二親 `58d6a0de9`、衝突0 |
| 採取と原ソース照合 | 全285本、欠落0、参照250,452件・commands 2,375件 |
| 全件 rewrite | 保留0、差分0本・0行、追加import0 |
| 取り込みによる自レーンのソースの変化 | 元の285本は全件SHA-256一致、AlgebraicGeometry配下の差分0 |
| 対象ビルド | 新規23モジュールと入口 `SerrePositivity.AlgebraicGeometry`、5,117ジョブ成功、終了状態0 |
| 小監査 | 新規23モジュール・174宣言（生成宣言を含む）、標準三公理のみ、終了状態0 |
| 直接 importer | 18本すべて上記の23本と入口1本の範囲内、範囲外0 |

## 対象と順序

基準は B3′ の `391b2a0d2`。この基準は取り込み前の枝の祖先ではなく、共通祖先は `78d0feeab`。単純な二点差分357本にはmain側だけの変化とdraftsが含まれるため、`git diff 391b2a0d2...cac6b317d -- '*.lean'` の自レーン側の285本を採取した。全て AlgebraicGeometry 本体284本と入口1本で、提供された候補7本も全件含む。この範囲は取り込み後にも元のGitコミットから再導出して一致を確認した。

未検証の `SegreProjectiveProjections.lean` とその他のdraftsは採取・書換・今回の対象ビルドの外に置き、作業木に保持した。実際の取り込みの直前に、未追跡ファイルとmainのパスの上書き衝突も0件であることを確認した。

採取は取り込み前の同じworktree・ソースで15組に分け、各組を共有鍵 `--class impl --wait 3600` の下で280秒以内に実行した。一つのworktreeからの待ちは常に一つ。各採取の後に鍵を返してから、共有の `bulk-b3prime/B4/rewrite.py`（内部で `bulk_namespace.py` を使用し、実際の宣言の所有元のimportも照合）でプレビューを作った。原ソース・主要な道具・改名表のSHA-256を固定した。

全285本の `schema/module/source` と原ソース全バイトの一致を共有の `checked_capture` で検査し、新しい `before-all` へ集約した。collector SHA-256は全件同じ。**mainを取り込む前に**、この完全な索引と同じソースで全件rewriteを再実行し、保留0と全バイト差分0を確認した。

その後、mainを衝突なく取り込んだ。プレビューの差分が0なので、旧ソースのコピーや変更の適用は行っていない。取り込み後のソースへ旧索引を流用するrewriteも行っていない。このB4′追従による名前・型・数学的仮定・aliasへの自レーンの変更は0。

## 取り込み後の検証範囲

取り込み待ちだった新規モジュールは23本、入口を含む対象は24本。[一覧](scheme-w1-b4prime/unmerged-files.json)と[監査の23モジュール](scheme-w1-b4prime/audit-modules.json)を固定した。取り込み後のcore Leanとscriptsでimportを再照合し、直接importer18本も全てこの範囲内であることを確認した。

対象ビルドは23モジュールと直接importerの入口だけを指定した。小監査は、23モジュール全ての読み込みを確認し、環境の定数の実際の所有元を使って、そのモジュール由来の公開・非公開・生成宣言を全件走査した。`collectAxioms` の許容集合は `propext`・`Classical.choice`・`Quot.sound` だけ。23モジュールの宣言数の和と最終ログの174宣言が一致した。ビルドと監査も別々の共有鍵で実行した。

検証範囲は上の対象と小監査で、プロジェクト全体のroot・下流全ビルド・AlgebraicGeometry全体の監査は調整役の担当とする。

## 記録

- [取り込み前の対象・原ソース・道具・表のハッシュ](scheme-w1-b4prime/before-state.json)、[全対象](scheme-w1-b4prime/files.json)。
- [全285本の採取と照合](scheme-w1-b4prime/full-before-summary.json)、[全件プレビューの差分と保留](scheme-w1-b4prime/full-rewrite-summary.json)。
- [main取り込みと285本の保存](scheme-w1-b4prime/merged-main.json)、[取り込み後のビルド・監査・ログと監査ソースのハッシュ](scheme-w1-b4prime/after-merge-summary.json)。
- [取り込み後の直接importer](scheme-w1-b4prime/after-merge-import-coverage.json)。モジュールごとの監査数は `after-merge-summary.json` に記録した。

完全な索引・プレビュー・ログ・検証用スクリプトはworktree内の `formalization-plans/stage-ii/scheme-drafts/b4prime/` に保持した。`.lake` や `/tmp` を成果の置き場所には使っていない。この報告を含む先端をB4′の取り込み点とする。

## 続ける数学

追従前の最後の検証済みの二束は、`a90012f40`（次数一被覆を持つProjの任意の係数移送の実際のpullback、4本243行・19宣言）と `cac6b317d`（Segreの行・列の局所射の重なりでの一致、4本385行・36宣言）。いずれも既定の資源制限で対象ビルドと標準三公理の小監査が成功しており、今回の取り込み後の検証にも含めた。

[2g-2の型と宣言・実装記録](scheme-w1-2g-2-report.md)のとおり、S03のチャート同型と重なりの射の一致は済み、S04の大域の貼り合わせ・ファイバー積・有限冪、およびG4〜G5は未完。2g-2の本体3,041行・入口込み3,089行、見込み約5,500〜12,000行・外枠16,000行は変更しない。B4′の後は承認を待たず、この続きに戻る。

一覧：済み0／全体3（うち追加0）。
