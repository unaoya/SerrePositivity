# IF-W0-3 §10.32：round 8〜11 と停止点2の前の停止（2026-11-01）

**追記（§10.33）**：以下は§10.32で停止した時点の履歴。新規ビルド数による停止は承認により解除済み。下流PASSを受理してafterを採取し、保存比較69件の不一致で停止点2に停止した。監査の追従は適用済み・未コミット、verify未実行。[現在の報告](batch-w1w2a-stop2-2026-11.md)。

**下流ビルドは round 11 で PASS（終了コード0、エラー0）。保存比較は未実施。** 補充だけの round 10 → 11 の新規ビルドが78 → 101に増えたため、§10.32 条件5で停止する。85本の時点で停止処理を要求したが、処理時には101本で正常終了しており、プロセスへのシグナル送信は行っていない。

作業木：`../SerrePositivity-ifw0-3`、ブランチ `infra/if-w0-3`。mainの変更・ビルドはしていない。新しいコミット、after snapshot、保存比較、verify は行っていない。

## 今回の round

| round | 対象 | 新規成功 | 失敗モジュール | 結果・終了コード | ビルド時間 |
|---:|---:|---:|---:|---|---:|
| 8 | 20,291 | 8,601 | 22 | FAIL / 1 | 85分32.90秒 |
| 9 | 913 | 733 | 3 | FAIL / 1 | 9分46.65秒 |
| 10 | 179 | 78 | 1 | FAIL / 1 | 1分43.85秒 |
| 11 | 101 | 101 | 0 | PASS / 0 | 4分12.19秒 |

ビルド時間の合計は 101分15.59秒。新規成功ジョブの合計は 9,513（round間の再ビルドは重複計上）。`✔` と `⚠` の両方の `Built SerrePositivity.*` を数え、各round内では重複なし。過去の途中報告で警告付き成功を除いた件数があったため、記録の全roundを同じ規則にそろえた（round 6: 72、round 7: 1,378）。

## 補充と静的検査

承認済みの5 importを補ってround 8を実行し、その失敗22モジュールに22 import、round 9の失敗3モジュールに3 import、round 10の失敗1モジュールに1 importを補充した。今回の追加は合計31 import。新しいmove・split・入口の#check移動・リポジトリの道具変更は0。
束全体の補充記録は 75 モジュール・83 import。[全一覧と各roundの失敗署名・エラー先頭3行](batch-w1w2a-downstream-imports.json)。すべての記録上のimportが実ファイルに存在することを確認済み。承認済み構文修正3ファイル以外のLean差分はimportの追加だけ。

各補充の直接違反・各tierの禁止閉包の増加は0。最後の実ファイルのimportグラフは保存済み模擬と完全一致。直接違反294、禁止閉包 W1=1・W2a=166・W2b=166を維持。W1＋W2aの対象一覧1,285項目はPASS（57.728秒）。実ファイルのratchet検査はPASS（53.062秒）。その後の4 importも各回増加0で、実グラフとの一致を再確認。

補充先は、Coreの2つのFunctorIso補題群、FramePreservation、ModelBridge.HAの分割先、およびMathlibのFunctorToTypesのMonoidalClosedインスタンス。`LargeParameterRelativeChoice` は純粋な定義だけが不足したため、ModelBridgeでなくkeep側の`HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions`を補った。

## 条件5に該当した理由と判断材料

round 10の対象179本のうち78本が成功し、`OrdinaryBarMappingComparison` が `UniverseLift.anodyneQ_map_isIso_of_weakEquivalence` の不足で失敗。その提供元へのimportを補うと、未着手だった下流101本（179 − 78）がround 11で全件成功した。対象集合は913 → 179 → 101と縮み、round 11のエラーは0である。新規ビルド数は78 → 101となるため、現行の文言どおり停止した。収束していない処置の拡大ではなく、先行エラーの解消で下流へ進んだことによる増加と考えられる。

次の判断が必要：このPASS済みの下流ビルドを受理して、after snapshot・保存比較を再ビルドなしで開始してよいか。停止点2への到達は、その保存比較の完了後になる。

## 保存検査とキャッシュ

beforeは3,020モジュール・30,828行まで統合済み。after予定は3,033モジュール。新しく必要になったbeforeは元ソース・元成果物から採り、ソース閉包のハッシュ一致を確認した。afterの採取・保存比較は開始していない。

round 8〜11でキャッシュに増えた成果物は約63,730ファイル・2.774 GB。束の全roundでは約255,113ファイル・12.807 GB。各実行はLakeの3変数を確認し、開始時に他のlake buildがないことと排他ロックを確認。報告作成時に実行中のlake buildはない。

## verify前に必要な監査の名前一覧の追従（未変更）

静的な調査で、7監査の必須モジュール名一覧に、W1・W2aで移動済みの旧名が合計325件残っている。宣言名・名前空間の変更とは区別する。これらの監査は実行しておらず、ファイルも変更していない。

| 監査 | 旧モジュール名の件数 |
|---|---:|
| `scripts/audit_derived_infinity.lean` | 36 |
| `scripts/audit_homotopical_foundations.lean` | 27 |
| `scripts/audit_homotopical_general_tools.lean` | 27 |
| `scripts/audit_homotopical_rectification.lean` | 37 |
| `scripts/audit_infinity_stable.lean` | 34 |
| `scripts/audit_kst_spectra.lean` | 156 |
| `scripts/audit_localizing_invariants.lean` | 8 |

`audit_kst_spectra` と `audit_localizing_invariants` は定義元モジュールを旧接頭辞で絞っているため、名前一覧の更新だけでなく移動先も監査対象へ含める追従が必要。`audit_einfinity` の同名7件は宣言名なので変更対象に含めない。verify.sh・runnerは変更していない。

## 記録と一時ランナーの修正

証拠は `.lake/verify/batch-w1w2a/stop2/round-{8,9,10,11}`、今回の要約は `stop2/addendum32/stop-summary.json`。ログの末尾だけでなく全体のエラー行を確認した。round 11にはエラー行がない。
自作の一時ランナーで、round 8開始時にファイル生成行がコメントに巻き込まれていた点と、round 10の補充前検査で基準JSONをまだ作っていなかった点を修正した。前者はビルド開始前、後者はソース補充前の失敗で、検査条件やリポジトリの道具は変更していない。
今回の変更は未コミット。既承認の道具 `9bc69dc79`・keep側move `8dc0f29a0` はそのまま。downstream importsのコミットと停止点2の保存比較は保留。

## §10.35：保存比較PASS

旧停止は解消済み。承認済みの規則と復元環境のppで全件一致、scratch削除済み。[保存比較の最終記録](batch-w1w2a-preservation-10-35.md)。指定3コミット後にverifyへ進む。
