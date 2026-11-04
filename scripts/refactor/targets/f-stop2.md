# IF-F F-1 — 停止点2

**PASS**。検証したソースは 392ddcc88（infra/if-f、基点 main 29d9ad0e7）。承認：IF-F §6 main 9f59541d3 と、FirstVertexOppositeChart の private 改名に対するユーザーの §5-4 例外承認。main 作業木で変更・ビルドなし。

## 適用内容

19補助定理を定義元で公開し、KSTからの import all 15辺を通常 import にした。残る本番 import all は Mathlib.CategoryTheory.Grothendieck 向け2辺で、今回の対象外。型・証明本文・配置は保持。変更した本番モジュールは、定義元15＋利用元15＋下記の局所改名1＝31本。

R67 check 2本の所有モジュール名を ModelBridge/Inputs の現配置へ追従。sorryAx の許可は従来の3所有モジュールだけに限定し、直接引用 HT-KQ 1件の検査を維持。ArrowFactorization 系3本を Foundation に分類。台帳のその他の処置は記録のみ。

### 承認済み private 改名

公開名との衝突で内部ビルドが1度停止（178e70671）。ユーザー承認後、FirstVertexOppositeChart 内の private 定理 mapNormalizeCompositionWithEq を firstVertexOppositeChart_mapNormalizeCompositionWithEq に改名し、参照1か所を追従（392ddcc88）。公開API・型・証明本文は不変。対応表は [f-private-name-map.json](f-private-name-map.json)。同じ旧名を持つ公開定理は改名していない。

## 検証

| 検査 | 結果 |
| --- | --- |
| 改名候補の小さなビルド | PASS、11.6秒 |
| 内部ビルド（変更30本＋R67依存3本） | PASS、89.8秒 |
| R67 level / resolution Hom | PASS、31 / 155宣言、直接引用は各HT-KQ 1件 |
| 下流144本・3根 | PASS、245.1秒 |
| private込み before / after snapshot v3b | 各144本 PASS |
| 保存比較 | 961 → 961宣言、生差2、対応後0、未説明0 |
| 層検査3条件 | PASS、直接禁止辺0、F1B入口・監査のstraightening 0 |
| 正式verify | PASS、gate=true、監査102本、対象5118本、49.2分、6 jobs / 40 GB |

正式verifyはキャッシュによる監査省略や選択実行の設定を外して実行。summary: PASS build(success=2,failure=0,known=0) audit(success=102,failure=0,known=0) sorry(success=1,failure=0,known=0) preparation(success=1,failure=0,known=0) retried=0。

verify対象収集修正は別コミット45969ee0a（通常importに加えて importModules の配列リテラルを収集、計算形は準備失敗）。草案時の31試験PASSに加え、今回の正式verifyで検証した。正式監査102本の検査条件は変更していない。

## 保存比較

比較器は変更していない。元のsnapshotと生の差分を保持し、private改名の1件だけを対応表に従ってモジュール単位の名前同一視に投影した。型・本体のハッシュは書き換えず、全項目を再比較して差分0。定理はv3bでbody=nullとなるため、19個の公開化と局所改名は証明ソースの一致も別途確認した。本番Lean144本の比較範囲では、privateキーワード19か所・import allキーワード15か所・承認された名前2か所以外に差分なし。

| 公開した補助定理（KST以下） | 型 | 本体 | 公理・属性 |
| --- | --- | --- | --- |
| LocalizingInvariants.comp_app_congr | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.ScaffoldTransportComparisonSpan.fiberPoint_ext | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.prependEq_heq | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.pointNormalize | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.component_reindex | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.mapNormalizeComposition | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.normalizeValueComposition | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.point_normalize_both_inv | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.mapNormalizeTriangle | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.endpointSpan_heq | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.pointTriangle | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.appendPointTriangle | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.point_normalize_inv | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.firstVertex_zeroSimplex | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.uliftMapVertex | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.uliftOppositeVertex | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.mapNormalizeCompositionWithEq | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.appendPoint | 一致 | 一致（証明ソース保持） | 一致 |
| Fibration.recoverPoint | 一致 | 一致（証明ソース保持） | 一致 |

private改名の1件も型ハッシュ・bodyハッシュ・公理・属性が一致し、証明ソースのSHA256も一致。検証結果は [f-stop2.json](f-stop2.json)。

## 層指標と残務

禁止モジュール74本（M16）・affected core 1,732本は適用前後で同じ。全ratchet数値も同一。Foundation分類で設定ハッシュだけが変わったため enforcement 基準を追従したが、許容辺・数値上限・例外は追加していない。現行基準は [f-layer-baseline.json](f-layer-baseline.json)。

W2c報告時1,730からの既存+2は F2.Tensor.SetSections / Space（G8、3e7942aac由来）。W2a/W2bの閉包指標4件を記録。F-1による増加ではない。

F-2は未適用。旧名aliasは利用者が多い方のみという方針を記録済み。G2・BSの区切りの合図を待つ。F-2の草案計数は29d9ad0e7時点なので、適用前にF-1で公開した19個のprivate/public区分を更新するよう対応表へ追記した。

## コミットと証跡

- 45969ee0a：verify対象収集修正と試験（別コミット）
- 20b781f39：F-1/F-2草案
- 178e70671：F-1適用とprivate衝突の停止記録
- 392ddcc88：承認されたprivate改名、小さなビルドPASS
- この報告のコミット：記録のみ。検証したソースは上記392ddcc88。

ログ・snapshot・比較・正式verifyのsummary・実行スクリプトは .lake/verify/if-f-apply/。旧W2bの未追跡5ファイルは変更していない。取り込みはClaude。
