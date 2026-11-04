# IF-F F-1 草案 — 停止点 1

基点 main `29d9ad0e7`（`8878743e3` の後）、既存作業木 `infra/if-f`。F-2 の判断 `65c321e1f` §5 も読んで反映。**Lean ビルド 0、verify 実行 0、本番 Lean 変更 0。**

## R60 台帳

[f-ledger.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/f-ledger.json) は **7,764 行**（現在の1モジュール=1行、所属タグは重複あり）。本番ルート到達、監査到達、入口からの経路、直接の利用者、旧判断と理由を付けた。

| 分類 | 行数 |
| --- | ---: |
| 主経路 | 1,010 |
| archive | 1,912 |
| 診断 | 4,378 |
| 一般論を抽出 | 464 |

| 領域 | 現在 | ルート到達 | 正式監査到達 |
| --- | ---: | ---: | ---: |
| FilteredExchange | 1726 | 0 | 0 |
| F1/Cocartesian | 619 | 129 | 619 |
| HA/Rectification | 415 | 1 | 415 |
| ClosureFunctoriality | 35 | 9 | 35 |
| KST/Comparison | 353 | 353 | 353 |
| KST/ProExcision | 367 | 367 | 367 |
| Spectra | 279 | 35 | 279 |
| R67/Coxeter | 4 | 4 | 4 |
| R67/Inputs | 3 | 0 | 0 |
| R67/CategoryTheory | 55 | 35 | 55 |

FilteredExchange **1,726 本は archive 維持**。外部の本番・監査から入る辺 0、ルート・監査閉包との交差 0。KST.Comparison・ProExcision は現在どちらも全件が本番ルート上なので、旧「休止」という記述だけでは外さない。
R33 の旧41本は現存41本。再分類は {'診断': 15, '主経路': 20, 'archive': 6}。旧 archive 候補でも本番の実依存に入ったものは維持し、診断や証明を削除しない。R36 の旧未登録一覧と移動／不在になった入口、R43 の転送・集約・検査専用を各行へ照合した。
R42 の旧156本を照合。今回の対象収集修正で16本の被覆漏れを解消する。現在の非 archive 未被覆は **145 本**（HA/Simplicial の孤立互換入口121本を含む）。未被覆を正常監査済みと扱わず、保持・診断登録／隔離の候補として台帳へ残す。
台帳中の archive 候補・監査登録候補は処置案であり、この草案で移動・削除・一括登録をしていない。F-1 の小さな適用案は次の private 参照と R67 の追従。段 G の分数・保留98・K固有211・M16は既存入力を参照するだけ。

## import all 15 辺

[f-private-edges.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/f-private-edges.json)。**15 辺すべて、定義元に置いたまま private を外して19個の補助定理を公開**する案。宣言の型・本文は保持し、15行を通常の import にする。K 固有の利用者を下層へ戻す案は W2c の分離と層順序を崩しうるため採らない。

| 利用元（KST 以下） | 補助定理 |
| --- | --- |
| LocalizingInvariants.RelativeFunctorCoreRestriction | `comp_app_congr` |
| Fibration.ScaffoldWeightedResolutionPoint | `fiberPoint_ext` |
| Fibration.StraighteningBaseChangeChartComponents | `prependEq_heq` |
| Fibration.ScaffoldVertexBaseChange | `pointNormalize` |
| Fibration.TransportRepresentationFiberPointHom | `component_reindex` |
| Fibration.StraighteningUnderSectionChart | `mapNormalizeComposition` |
| Fibration.ScaffoldRestrictionChart | `normalizeValueComposition` |
| Fibration.ScaffoldBaseChangeLeftPoint | `point_normalize_both_inv` |
| Fibration.StraighteningBaseChangeSectionCharts | `mapNormalizeTriangle` |
| Fibration.ScaffoldBaseChangeCoefficientNaturality | `endpointSpan_heq`, `pointTriangle` |
| Fibration.ScaffoldBaseChangeRightPoint | `appendPointTriangle`, `point_normalize_inv` |
| Fibration.StraighteningBaseChangeVertex | `firstVertex_zeroSimplex` |
| Fibration.PointedLeftResolutionVertices | `uliftMapVertex`, `uliftOppositeVertex` |
| Fibration.StraighteningUnderRealizationChart | `mapNormalizeCompositionWithEq` |
| Fibration.ScaffoldCocartesianBaseChange | `appendPoint`, `recoverPoint` |

明示的な public 宣言名の衝突はソース全体で0。`mapNormalizeCompositionWithEq` は別ファイルの private 同名が1件あり、内部名が別なので公開名とは衝突しないが、適用時に局所の名前解決を確認する。生成名を含む検査は承認後の before snapshot と小さなビルドで行う。比較器の条件は緩めず、private → public の対応を19件明示する。
変更候補 **30 モジュール**、逆依存 **144 本・3 根**。温まった木で内部・下流の予備見積もり5–15分（未実測）。これに正式 verify が別途必要（W2c 実測約44分）。R67 の check 2本は本番下流を増やさない。

## verify 対象収集 — 別コミット済み

`45969ee0a`：通常 import と `importModules` の配列リテラルを `audit_imports.py` で共通収集し、準備段とキャッシュ依存へ反映。監査の環境・検査条件は変更しない。計算された配列やモジュール名は準備失敗として報告する。特別な sorry probe の計算 import はキャッシュ不可として毎回検査する。
対象 **5019 → 5118**、追加99・削除0。閉包の新規被覆16本。コメント／文字列中の偽 import、複数呼出し、複数 record、Unicode、クリーンな一時木の準備段、推移依存によるキャッシュ無効化、未対応形の拒否を試験した。
新規9試験＋既存のスケジューラ10・再試行/集計12試験=**31件 PASS**。既存集計試験は偽 lake の一時木だけで、Lean は実行していない。`zsh -n`・差分の空白検査も PASS。

## R67 の残り

- Coxeter 4本は Foundation 登録済み。移動しない。Mathlib 置換 R78 は対象外。
- Inputs 3本は ModelBridge/Inputs への配置と import の追従済み。check_kan_quillen_level / resolution_hom の所有モジュール一覧・許可判定だけ旧パスが残る。現所在へ追従し、直接の引用は HT-KQ 1件、sorryAx の許可は同じ3所有モジュールだけに保つ案。宣言 namespace は F-2 対象外。
- CategoryTheory の55本も再計数。Foundation 29本は維持。未分類26本のうち ArrowFactorization 系3本は Mathlib と自身だけに依存し、一般基盤として Foundation へ登録する候補（移動なし、例外なし）。残りは混在した紙・DG・KST の経路として所在を保持。

## 停止点1での確認対象

19補助定理の公開化／15 import all の解除、R67 check 2本の追従、ArrowFactorization 3本の分類案。台帳の広い隔離・削除・登録はこの小さな適用範囲に含めない。

検査記録：[f-draft-validation.json](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ifw0-3/scripts/refactor/targets/f-draft-validation.json)。F-2 の適用は G2・BS の区切りの合図を待つ。

## 適用後の追記

草案の private 同名に関する見込みは実ビルドで訂正した。公開名の導入後、FirstVertexOppositeChart の同じユーザー名の private 宣言が拒否された（178e70671）。ユーザーの §5-4 例外承認を受け、private 定理と参照1か所だけを改名（392ddcc88）。保存比較・内部検証・下流・正式verifyの最終結果は [停止点2](f-stop2.md) に記録した。
