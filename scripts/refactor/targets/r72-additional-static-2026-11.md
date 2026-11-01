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
