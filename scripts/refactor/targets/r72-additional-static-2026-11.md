# R72(4) 静的調査：§10.25 と BoundaryOne の現状の食い違い

指示：main `321cc6287`、IF-W0-3 §10.25。状態：**適用前 STOP**。

中核から到達する補充先は `HA.Transfer.EvaluationFamily` と `HA.Simplicial.LargeParameterHomotopy` の2本。

## EvaluationFamily の候補

保存済み snapshot の used_modules / used_constants と補助宣言の帰属から、ModelBridge.HA.Basic に移された CofibrantlyGenerated を使うソース宣言は7件。keep候補は9件。これは候補であり、他モジュールへの連鎖・中核の使用の調査は未完了。適用可能との判定ではない。

移動候補（共通接頭辞 `SerrePositivity.ModelGeneration.EvaluationFamily`）：

- `modelCategory`
- `modelCategory_weakEquivalences`
- `modelCategory_fibrations`
- `modelCategory_generated`
- `evaluation_isRightQuillen`
- `free_isLeftQuillen`
- `functorialFactorizations`

## BoundaryOne の食い違い

§10.25 の補足は BoundaryOne を「モデル側の塊」としているが、既存の w2a.md:79 は moved 0 / keep 5、「分割不要：純粋部分の move は後の窓」と記録している。現在のソースも5宣言すべて純粋な単体集合・余極限の構成で、直接 import は Mathlib の SimplicialSet.Boundary と SubcomplexColimits の2本のみ。

宣言は `square`, `zero_comp`, `one_comp`, `faceCofanIsColimit`, `isColimit`。LargeParameterHomotopy.lean:52 の boundaryColimit が使うのは `BoundaryOne.isColimit`。

layers.json:129 は HomotopyFunctionComplex 以下を接頭辞で禁止する。そのため純粋部分を現在の BoundaryOne に残しても禁止閉包からは外れない。モデル側へ切り出せる宣言はない。

提案（未承認・未実施）：5宣言全体を `HA.Simplicial.BoundaryOne` へ move し、宣言名を保持して直接 import を更新する。これは指示の追加 split と異なるため、独断で w2a.json に加えない。

今回の数学ソース変更・snapshot・ビルド・コミットは0。既存の未コミット補充は保持。w2a.json は未変更。詳細は `.lake/verify/batch-w1w2a/stop2/r72-additional-static/analysis.json`。

## §10.26 の承認後：静的検査 PASS

BoundaryOneのmoveが承認されたため上記STOPは解消。追加はEvaluationFamilyの1 split（moved 7 / keep 9）とBoundaryOneの1 moveのみ。LargeParameterHomotopyはBoundaryOne.isColimitとLargeParameterExtensionのkeep側のextend/extend_initialを使い、モデル側への依存がないためmoved 0。

EvaluationFamilyのmoved宣言の実使用は4モジュール10宣言。保存済み/追加snapshotのused_constants、全ソースの名前参照およびnamespace/open/exportを照合した。HA.Diagram.Projective、HA.Monoidal.ManyObjectTransfer、EInfinity.BarrattEccles.CarrierDiagramModel、同DiagramModelの4本はいずれも中核の閉包外。中核の使用0、追加の分割連鎖0。

適用前snapshotは2モジュール約7.865秒、元baselineの追加利用元snapshotは10モジュール約15.185秒、両方rc 0。追加2項目のvalidator PASS、模擬と実グラフは一致。W1=1、W2a/W2b=172、増加0。詳細は `.lake/verify/batch-w1w2a/stop2/addendum26/`。下流ビルド・保存比較は続行中。

## 再ビルド後の停止：F2入口の #check

R72追加分割・moveは `16e808ff6` にコミット済み。改訂w1+w2a 1,278項目の静的検査PASS、実グラフの禁止閉包はW2a/W2b=172。

round-3: 20,194対象、174入口、1721.918秒、rc 1、新規3,059モジュール、失敗28モジュール。必要な29 importを補充し、各補充の層検査は増加0。
round-4: 10,394対象、124入口。F2.lean:210の #check が参照する CoherentColimitUnitFirstTotalRelation の直接importを模擬すると、F2入口自身の禁止閉包がW2a/W2bとも0→141。直接違反は増えず、全中核の和集合も172のままだが、モジュールごとのratchetに反するためSTOP。該当importは未追加。F2入口には1,497行の #check が残り、Leanは100エラー上限に達した。

共有ロックの親PIDへSIGTERMを送りビルド全体を停止し、psでlake buildが残っていないことを確認。停止点2は未到達。EvaluationFamilyのrlp用import（自身の追加分割の選定漏れ）、LargeParameterRelativeChoiceのsimplicial_pushoutProduct_mono用importも未補充のまま記録。保存比較とdownstream importsコミットは未実施。

F2-lite入口とFilteredExchange向け #check の配置を分離する判断が必要。詳細は `.lake/verify/batch-w1w2a/stop2/stop-f2-entry-26.json`。

## §10.27：全件分類と verify の探索規則の食い違いによる停止

定義元の照会は既存 main の成果物から decl_snapshot.lean --resolve-modules で行い（38.144秒、rc 0）、move・split の対応表を通して現在の import 閉包と照合した。F2 の #check 1,497件は全件が入口の閉包外（残す0、移す1,497、直接 import 候補769モジュール）。ルートと InfinityCategories 直下の他の入口には #check はない。全件の宣言名・元/現在の定義元・判定を `.lake/verify/batch-w1w2a/stop2/addendum27/classification.json` に保存した。

未処理の2件は補充済み：EvaluationFamily に Mathlib.CategoryTheory.MorphismProperty.LiftingProperty、LargeParameterRelativeChoice に HomotopicalAlgebra.Simplicial.ModelCompatibility。補充ごとの層検査は増加0、直接違反296、禁止閉包 W1=1・W2a/W2b=172 のまま。w2a.json の import 指定と downstream 記録を同期した。コンパイルはまだ行っていない。

§10.27-2 は scripts/check_infinity_f2_pending.lean を manifest に登録して verify で走らせる指示だが、既存 verify.sh:63–74 は audit_*.lean と scripts/audit/*.lean しか探索せず、manifest は探索結果との照合用である。現在は99/99・missingなしだが、指定の行を追加すると `manifest audit missing: scripts/check_infinity_f2_pending.lean` になる。main でも同じ実装である。verify 本体を実行せず、探索と集合差の同じ式で再現した。

既存の道具と指示の食い違いなので停止。入口の #check の移動、検査ファイル作成、manifest変更、再ビルド、保存比較、新規コミットは未実施。既存の R72 コミット16e808ff6は保持。提案：manifest に明示された既存の scripts/check_*.lean も監査対象として扱うよう verify の探索規則を変更し、存在しない manifest ファイルは引き続き失敗とする（承認待ち）。詳細は addendum27/stop-manifest.json。

## §10.28：入口の移動完了、Generated.Basic の禁止閉包増加で停止

指定された audit_infinity_f2_checks.lean に旧入口の #check 1,497件（全文・順序一致）と直接 import 769本を移した。manifest は99→100本、探索結果と一致。意図はF2入口の閉包を広げずに既存の受入検査をverifyへ残すことで、verify本体は変更していない。入口は既存docstringとF2.CatInfinityへのpublic importのみ。コミット999d292e3（入口の #check の移動）。R72追加分割は承認済み16e808ff6。

round 5 は20,289対象・172入口、189.714秒、rc1、新規58本、キャッシュ405ファイル/99,363,867 bytes増加。F2入口のビルドは成功（2.8秒）。失敗2本はEvaluationSmallnessとEvaluationLeftProper。追加のbefore snapshot（2本、10.993秒、rc0）を保存し、前者へMathlib.CategoryTheory.SmallObject.Basic、後者へHomotopicalAlgebra.Transfer.CellMapを補充。各回の層検査は増加0、直接違反296・W2a/W2b=172。

round 6 は同じ20,289対象・172入口、73.665秒、rc1、新規71本、キャッシュ430ファイル/8,565,070 bytes増加。ログ全体を検索し、失敗はSimplicial.Generatorsだけ。60行目の generatedLeft_le_of_cells_le が未解決、61行目の No goals to be solved はその後続。定義元はGenerated.Basic:34。

Generated.Basicを補充すると、全体の和集合172と直接違反296は変わらないが、W2a・W2bのそれぞれで1,083個の中核モジュールの禁止閉包が1本増える（検査の増加項目2,166）。例：F1.Coherent.SpaceSmallLimits 49→50、F1.Diagrams.CocartesianKanUnstraighteningUnitPoints 2→3。§10.24に従って停止し、このimportは未追加。Generatorsは未変更。

Generated.Basicは既存R72分割のkeep側で、残る2宣言は generatedWfs と generatedLeft_le_of_cells_le。モデル圏の5宣言はすでにModelBridge.HA.Basicに分離されているが、keep側の置き場所は依然として禁止接頭辞HomotopicalAlgebra.Generatedの中にある。提案：純粋なkeep 2宣言のモジュールを禁止接頭辞の外へmoveする。移し先・対象一覧の更新は未承認なので実施していない。

ビルドプロセスなしをpsで確認。停止点2未到達、after snapshot・保存比較・全体verifyは未実施。downstream importsは47利用元・51 importと構文修正3件を保持し、未コミット。詳しい全件の増加はround-6/*Generators-layer.json、停止集計はaddendum28/stop-generated-basic.json。

## §10.29：keep側7本の調査完了、split後moveの書式制限で停止

7本・31ソース宣言を確認し、全件純粋かつ中核から到達。7本一括move＋Generatorsの補充の模擬は禁止閉包172→166、直接違反296→294、増加0。ただし5本は既存splitと同じmoduleになり、validate_targets.pyがduplicate moduleで拒否する。適用・w2a.json更新・再ビルド・コミットはしていない。詳細は[r72-keep-moves-2026-11.md](r72-keep-moves-2026-11.md)。

## §10.30 適用後、§10.31 条件5による停止

道具9bc69dc79（split→keep moveのみ許可、試験2件追加・全170件PASS）、R72 keep側7本のmove 8dc0f29a0 をコミット。moveコミットはtargets READMEの例外規則を追加した版で、途中で報告したda0edfa79から文書のみを追加して置き換えた。既存の未コミット補充はmoveコミットに混ぜず保持した。

GeneratorsへSimplicial.GeneratedLeftClassの直接importを補充。層検査増加0。最終の1,285項目のvalidator PASS、実グラフの直接違反294・禁止閉包W1=1、W2a/W2b=166。対応表はkeep側のmodule moveとmoved宣言ごとの移し先を両立させた。

round 7：20,291対象・172入口、開始2026-11-01T15:46:51.198046+09:00、停止要求2026-11-01T15:56:18.609862+09:00、567.412秒。新規ビルド1,333本。直前round 6は71本であり、実行中に追加された§10.31の停止条件5（一つのroundの新規ビルドが前のroundより増える）に該当するためSIGTERMで停止した。今回は7本のmove後の再ビルドであるが、条文にその例外はないため独断で除外しない。psでlake buildが残っていないことを確認した。正常終了コードは得ていない。

ログ全体で失敗4モジュール：BoundaryReedyFactorization（余極限保存instance）、ModelCompatibility（CofibrantlyGenerated）、KanTestLiftingClass・KanMonoRelativeHomotopy（ParametrizedAdjunction.hasLiftingProperty_iff）。5本の直接import案は1本ずつ検査し、全件増加0、必要な元snapshotも採取済み。停止条件成立により補充は未適用。

この段階の表の適用件数：直接import補充1、純粋keep側move7、追加非中核split0、入口check移動0、split→keep moveのvalidator対応1。過去の入口移動・追加splitは既存コミットのまま。各roundの時間・新規ビルド・失敗署名はdownstream-imports.jsonのroundsと .lake/verify/batch-w1w2a/stop2/addendum31/rounds.json に記録。

キャッシュの増分目安は4,241ファイル・136,106,280 bytes。after snapshot・保存比較・verify・downstream importsコミットは未実施。停止点2には未到達。現在のビルド数増加について、7本のmoveを伴うroundにも直前roundとの比較を適用するかが再開時の判断点。

## §10.35：保存比較PASS

旧停止は解消済み。承認済みの規則と復元環境のppで全件一致、scratch削除済み。[保存比較の最終記録](batch-w1w2a-preservation-10-35.md)。指定3コミット後にverifyへ進む。
