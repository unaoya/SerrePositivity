# IC-W1 ∞ コード整理報告

## 現在地（2026-11-17 18時、IC-1適用前で停止）

**IC-1は未適用。root外の直接importerである既存下書きが、凍結した原ソースのまま19エラーで型検査に失敗した。証明変更なしで追従の検査を満たす扱いが未確定のため、§11の停止指示に従って適用前で停止する。IC-1完了の報告ではない。**

- 検証済みの数学ソースのmain：`35988dd08b05d27a263fc210bafdadd0b1fc4c11`。root・全監査・sorry閉包通過は調整役の11-17夕の連絡に基づく。最新main `adc221d19c22ce2063690b1daff999b03cb70452` はその後の文書差分だけで、merge `7101c0da6` で追従した。
- main追従：`414be0de2d7c125167e4ed77505c8de44cddfe31`。承認済み2,264本のソースSHAは全件一致。本体・検査スクリプトはこのmainと同一。
- 移動前の独立環境：`/private/tmp/ic-w1-before-414be0de2`（同じHEADのdetached worktree）。mainのビルド済み成果物をCOW複製し、projectのoleanを共有せず保持する。第三者packagesのみ参照共有。
- 採取：native所有元（private/生成宣言を含む）→原compiler参照/openの束縛→正式な改名案→他枝の影響を再集計。影響30ファイル以下なら11-17夕の追加承認により昼から適用してよい。適用直前に一行連絡する。昼のbulkは3〜5分、夜は30分以内。静的→対象build→v3b→引用/タグ→rootまで確認し、root成功で報告をコミットして停止。正式全監査は調整役が実行する。影響30本超、または直せない移動が出た場合は停止・報告する。
- §10（BR56）：Archiveを追従対象と外部importer数から除外。復帰時に改名表で直す。
- BR55不明356件は据置。B1/B4はIC-1移動後の別amendment（B1最初4本/400行、B4最初1節/50本）。

移動適用一覧：済み **0／全体26（うち追加0）**。原環境の正式採取と検査は進捗に応じて以下へ記録する。

<details>
<summary>承認済み段0の停止時点（履歴）</summary>

## 現在地（2026-11-17、レーン⑦）

**IC-1 段0（紙）を提出し、適用前の停止点。Lean変更・ビルド・native宣言採取は実行していない。ユーザーの11-17の指示に従い、この紙をコミットして止まる。§3の条件付き事前承認による準備・適用への自動続行はしない。**

- 最初の `pwd` は `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ic` と一致。枝 `refactor/infinity-consolidation`。起点 `98a6465b4` は `merge/night-2026-11-17` と同じで、OE-W1段1の停止点を含む。
- 指定の `git merge main` を実施し、`1cfcb6856ae922b3c8d047fe223173d0681f71ae`。取り込んだmainは `a87444d438295e71a461fb945d02d5537288ed9c`。差分は調整記録だけ。今夜のroot・全監査の結果を先取りしない。
- 指示書 [infinity-consolidation-w1.md](infinity-consolidation-w1.md) §0〜§8、[OE-W1報告](report-organize-einfinity.md) とその全件分類・B4、`research/infinity-outside-map/files.csv`、費用計画、③-aの指定md/jsonを参照。
- 今日の資料はソースの静的な案。**正式な宣言所有元、private/kernel名、生成宣言、open経由の束縛の採取は、今夜のroot後、明朝以降**。`.olean` の不足を理由に今日ビルドしていない。

段0一覧：済み **5／全体5（うち追加0）**：IC1-0a 移動/改名・層/他枝、IC1-0b BR55、IC1-0c B1、IC1-0d B4、IC1-0e §6のDG分類。
移動適用一覧：済み **0／全体26（うち追加0）**。単位IDは下表のIC1-族名。IC-2〜IC-5には進まない。


</details>

以下の§1〜§6は承認済み段0の紙を履歴として保持する。再開後の実測は先頭と§7以降を参照。

## 1. IC-1の範囲・全件の移動と改名の案

OE-W1の `stage2-classification.csv` は2,621本を数えるが、このうち357本（FrameHom144・HomotopyWeight61・SimplicialLocalization152）は段1済み。現存する残り **2,264本・165,536行**だけがIC-1。一般890、BE固有1,047、E∞一般論327。指示書§1の一般1,247は段1済み357を含む集計で、これを再移動しない。

[全件moves.csv](../../../research/infinity-consolidation-w1/moves.csv) に元パス→新パス、旧module→新module、namespace接頭辞案、行数、SHA、ソース名候補数を記載。[source-name-hints.csv](../../../research/infinity-consolidation-w1/source-name-hints.csv) は**名前付き宣言候補7,414行、改名候補7,414行（異なる索引名7,412）**の旧名→新名。匿名instance・private・生成宣言を網羅したkernel全表ではなく、適用入力にはまだ使わない。重複候補名 `tensorFamilySubstitutionStep_post` と `SimplexCuts.card_filter_lt_orderEmbOfFin` が各2行あり、native所有元で解消する。

下表はすべて `SerrePositivity/` 以下。ディレクトリ内の相対パス・ファイル名は維持する。「名」はソース上の改名候補数。単一ファイルの行はそのファイル自体の新パス。

|単位ID（IC1-を付す）|元 EInfinity/ 以下|新しい配置|本数|名|
|---|---|---|---:|---:|
|AlexanderWhitney|`AlexanderWhitney/`|`HomologicalAlgebra/SimplicialChains/AlexanderWhitney/`|28|135|
|BergerFresse|`BergerFresse/`|`InfinityCategories/Models/EInfinity/BarrattEccles/BergerFresse/`|3|20|
|ComplexLimits|`ComplexLimits/`|`HomologicalAlgebra/Complexes/Limits/`|382|908|
|CosimplicialNormalization|`CosimplicialNormalization/`|`HomologicalAlgebra/Cosimplicial/Normalization/`|9|35|
|DGAlgebra|`DGAlgebra/`|`DifferentialGraded/Algebras/`|26|143|
|FrameRealizationLifting.lean|`FrameRealizationLifting.lean`|`HomotopicalAlgebra/HomotopyFunctionComplex/FrameRealizationLifting.lean`|1|3|
|Hammock|`Hammock/`|`InfinityCategories/HA/ModelCategoryComparison/Hammock/`|354|1395|
|HomBiprodRestriction.lean|`HomBiprodRestriction.lean`|`HomologicalAlgebra/Complexes/HomBiprodRestriction.lean`|1|2|
|HomHomotopy.lean|`HomHomotopy.lean`|`HomologicalAlgebra/Complexes/HomHomotopy.lean`|1|4|
|HomRestriction.lean|`HomRestriction.lean`|`HomologicalAlgebra/Complexes/HomRestriction.lean`|1|2|
|HomologyZero|`HomologyZero/`|`HomologicalAlgebra/Complexes/HomologyZero/`|16|55|
|IntervalCuts|`IntervalCuts/`|`InfinityCategories/Models/EInfinity/BarrattEccles/IntervalCuts/`|205|898|
|NatTensor|`NatTensor/`|`HomologicalAlgebra/Complexes/NatTensor/`|5|24|
|NativeBinaryCoconeHom.lean|`NativeBinaryCoconeHom.lean`|`HomologicalAlgebra/Complexes/NativeBinaryCoconeHom.lean`|1|2|
|NegativeTensor|`NegativeTensor/`|`HomologicalAlgebra/Complexes/NegativeTensor/`|14|49|
|Operad|`Operad/`|`InfinityCategories/Models/EInfinity/DGOperads/`|327|1012|
|OppositeFactorization.lean|`OppositeFactorization.lean`|`HomotopicalAlgebra/ModelCategory/OppositeFactorization.lean`|1|2|
|ProjectiveCofibrantUnit.lean|`ProjectiveCofibrantUnit.lean`|`HomotopicalAlgebra/Complexes/ProjectiveCofibrantUnit.lean`|1|4|
|ProjectiveCofibration.lean|`ProjectiveCofibration.lean`|`HomotopicalAlgebra/Complexes/ProjectiveCofibration.lean`|1|1|
|ProjectiveHomotopyInverse.lean|`ProjectiveHomotopyInverse.lean`|`HomotopicalAlgebra/Complexes/ProjectiveHomotopyInverse.lean`|1|3|
|ProjectiveModel.lean|`ProjectiveModel.lean`|`HomotopicalAlgebra/Complexes/ProjectiveModel.lean`|1|19|
|Shuffle|`Shuffle/`|`HomologicalAlgebra/SimplicialChains/Shuffle/`|45|158|
|SimplexCuts|`SimplexCuts/`|`InfinityCategories/Models/EInfinity/BarrattEccles/SimplexCuts/`|426|1086|
|StrictAdjunctionBar.lean|`StrictAdjunctionBar.lean`|`HomotopicalAlgebra/Bar/StrictAdjunctionBar.lean`|1|19|
|Surjection|`Surjection/`|`InfinityCategories/Models/EInfinity/BarrattEccles/Surjection/`|202|767|
|TableReduction|`TableReduction/`|`InfinityCategories/Models/EInfinity/BarrattEccles/TableReduction/`|211|668|

旧名の基本は所有元ごとの接頭辞の移送。例：

|旧名/所有範囲|新名/接頭辞案|
|---|---|
|`SerrePositivity.EInfinity.ComplexLimits.*`|`SerrePositivity.ComplexLimits.*`|
|`SerrePositivity.EInfinity.Hammock.*`|`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.*`|
|`SerrePositivity.EInfinity.Operad` とそのメソッド|`SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad` とそのメソッド|
|Operad/ が所有する `EInfinity.schurDiagram` 等|`SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram` 等|
|`SerrePositivity.EInfinity.SimplexCuts.*` 等BE固有5族|`SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.*` 等|

`SerrePositivity.HomotopicalAlgebra` は作らず、主題名の `SerrePositivity.ProjectiveModel`・`OppositeFactorization`・`StrictAdjunctionBar` 等へ。移動先パスに合わせた一律namespace置換にはしない。Operad/にあるroot EInfinity宣言とOperad拡張は別規則で扱い、他ファイルの同じnamespaceは巻き込まない。既存Mathlibの `HomotopicalAlgebra` の解決はOE-W1の前例どおりcompiler参照で保存する。

Operad327本は対称 **dg** operad、Schur関手、自由代数、模型の移送を含むため `Models/EInfinity/DGOperads/` 案。HAの∞-operadの完成とは数えない。Hammock354本はDwyer–Kan／HA1.3.4の模型圏比較として、段1のSimplicialLocalizationと同じ比較領域に置く。模型のdocstringには「模型。文献の定義との比較は後で」を付す案。

今回の表はOE段2の分類範囲そのもの。**既存BarrattEccles本体・集約入口、Interface、Modules、PowerOperation、段1のStoppedRoutes99本を追加でModelsへ移す案は含まない**。したがってIC-1だけでEInfinity全体を空にする計画ではない。DGAlgebra26本の受入先の新設は当該26本の移動案であり、既存DG本体の再配置やIC-5の510本の整理ではない。

### 1.1 層・import・衝突の見込み

新パスの既存ファイルとの衝突0、移動先同士の重複0。対象外の直接importerは**311ファイル・2,434辺**（移動先のmodule名への追従が必要）。主張・証明は変えず、元の辺をmodule-mapで同型に移す案。

[層予覧](../../../research/infinity-consolidation-w1/layer-preview.json) は既存KL-W1 checkerと同じ設定を読んで、tier・実装境界・承認済み逆辺の理由を所有moduleと一緒に仮移送した。`layers.json` は未変更。baselineの∞ per-file tier未登録0。**基準172件→予覧172件、新規0・消失0**。内訳は既存のreverse-section63、tier-order23、blueprintの別source-rootの名前を本体のsource-rootとして読むためのunresolved-import86。本体の既存86件とblueprintの索引上の86件を混同しない。層の全件PASSではなく、同じ入力グラフ上で新規違反がないという予覧。

「一般」または「E∞一般論」でも、具体的なBE部品への直接依存は**41ファイル・50辺**ある。[境界表](../../../research/infinity-consolidation-w1/concrete-boundary-imports.csv) を参照。例：DGAlgebra/AWIntervalComonoidはIntervalCutsとBEの余単位計算を使う。`DifferentialGraded/` や `HomologicalAlgebra/` へ置くだけでPortableに格上げしない。Consumersと実装境界を保持し、一般論と具体的模型を分離するための証明変更をこの束へ混ぜない。移動で境界が保存できない単位は適用時に取り下げる。

引用はKerodon/HTT/HAの対応表の番号・own/partialに再照合する。新しい番号を名前から推測しない。Kerodon partialにはkerodon属性を付けず、略号表 `Util/Citation.lean` は変更しない。

### 1.2 他レーンへの影響

[枝影響の全件表](../../../research/infinity-consolidation-w1/branch-impact.json) は `main..branch` のコミットが触るLeanの和集合、merge-baseからの差分、および各worktreeの未コミット・未追跡を読み取ったもの。作業木は変更していない。調査中にも枝が進んだため、下表は最後の観測を固定した。head/head_afterが同じことを記録し、作業木は内容SHAの一覧のhashを記録した。未コミットの他者編集を凍結したという意味ではない。

|レーン・枝|観測HEAD|触るLean/読めたLean|IC-1に触るファイル|書換える直接import辺|直接KST import（ファイル/辺）|
|---|---|---:|---:|---:|---:|
|③-a `math/inf-supply`|`223e8ce2855c`|350/349|0|0|0/0|
|⑥ `math/scheme`|`6974d6e418e5`|3043/3043|0|0|0/0|

これはmodule/importと明示的なEInfinity修飾参照の静的照合。短名・open経由の束縛は未検収。正式所有元採取後、適用の直前に再計算する。BR55の追加候補で③-aが同じ**ファイル**を触るのは `smallLeftUnstraighteningComparisonOfFunctorIso`（ICCH179）。これはIC-1の移動対象ではないが、chooseを直す場合の重なりとして別記する。

現段階の直接影響0≤30であっても、ユーザーの11-17の指示が停止条件。紙の確認前に準備・適用へ進まない。

### 1.3 費用と今後の検査（未実行）

紙の見積り（鍵待ちを除く）：今夜のroot後の独立した原環境採取・所有元/参照確認3〜6時間、準備と静的な追従2〜4時間、移動・docstring/import適用2〜3時間、対象ビルドとv3b4〜8時間、root/正式全監査/verify4〜8時間、目録とB4追従1〜2時間。**合計16〜31時間、複数の夜を想定**。OE-W1段1の588本・10,476 native宣言の実績に対し、今回は2,264本で、ソース名件数だけでは費用を比例換算できない。B1/B4の実適用と「不明」chooseの構成変更は別途2〜5日程度の検討枠を見込み、上の移動だけの見積りに成功を織り込まない。

許可後も検査順は、静的import/層/衝突→対象build→独立した前後環境のv3b（型・本体・公理・kernel属性、未説明0）→引用/タグ欠落・余分0→root→正式全監査→verify。直せない移動は取り下げて報告。ビルドは `--class bulk`、昼3〜5分、適用と全体の検査は夜。凍結通知は実際の適用直前に短く出す。今日は鍵取得・Lake/Lean実行・ソース適用のいずれもしていない。

## 2. BR55：弱い存在命題からchooseする定義

### 2.1 ③-aの255本を再判定せず引き継ぐ

指定の `../SerrePositivity-bs-classical/formalization-plans/stage-ii/inf-supply-choose-1117.md` と `.json` を読取り専用で参照。[choose-inherited.json](../../../research/infinity-consolidation-w1/choose-inherited.json) に255行の判定・元ID・選択元・理由・推移importer・他枝を写した（原ソース全文の重複だけは省略）。そのファイルのSHA256は `d0ab05936e20caa7326ebd2b740db565b761c21456ba4e4ba5710f815c1364ea`。元のsource_headは `8f06e1bcd + approved LeftCoherentTransportDirectComparison three-body patch`。

**255行はいずれも置換見積り0行**という元の判定を維持する。ただし「17 rootからの残る型つき一覧が追加の指定構成との一致を要求しない」という範囲内の判定で、全利用者についてcanonicalだという主張へ拡張しない。CH141 chosenColimitSection、CH185 presheafElementsColimitCocone、CH025 chosenZeroVertexなどを再調査の件数に加算しない。importer数も元枝の35,015ソースのグラフに由来する値をそのまま残し、今日の本体の数字と混ぜない。

現HEADとの適用範囲の照合では **CH062/CH076のファイルSHAが違い、13行のファイルは本作業木にまだない**（CH067/073/074/246〜255）。これは他枝の判定を削除する理由ではなく、取り込み前・別HEADの資料であることを示す。取り込み後にパス/所有元を再照合する。差分ID全件は [補助集計](../../../research/infinity-consolidation-w1/supplement-summary.json)。

### 2.2 255本の外の追加走査

`InfinityCategories/` **15,972本**と `EInfinity/` の現ソースを走査。全件の内容別索引は [infinity-files.csv](../../../research/infinity-consolidation-w1/infinity-files.csv)、ディレクトリ別集計は [infinity-content.csv](../../../research/infinity-consolidation-w1/infinity-content.csv)。コメント・文字列をマスクし、Classical.choose/choice、Exists.choose、`.choose`を抽出し、元の255本とファイル・ソース宣言名で重複排除した。

追加の語の一致は**699宣言候補**：def364、instance2、lemma299、theorem34。証明専用333は [choose-new-candidates.json](../../../research/infinity-consolidation-w1/choose-new-candidates.json) に別種として保持する。未割当4出現はLegacy12/26の `deprecated_alias ...choose := ...choose` 各2出現で、新しいchoose定義ではない。数値の二項係数 `Nat.choose` 等4定義も除外する。

残る**データ候補362**のうち、固定比較射の逆・同値候補104、その他の存在証拠からのデータ候補258。これは「弱い存在だけの問題箇所362個」という判定ではない。概数23〜28に合わせて逆同値・局所的な有限組合せの選択を黙って落とさず、保守的な上位集合として全部残した。

[追加全行表 choose-additional.md](../../../research/infinity-consolidation-w1/choose-additional.md) に要求された宣言・ファイル・選択元・両立・処置・推移importer・他枝を列挙。[JSON](../../../research/infinity-consolidation-w1/choose-additional-review.json) に利用側のソース参照（path/line/原文）、短名一致数と理由を付す。静的な宣言境界・短名索引であり、匿名instance名・kernel名や短名の束縛は保証しない。推移importerは本作業木のtracked source graph、対象自身を除く値。

判定は **要らない6、不明356、要ると確定0**（二項係数の対象外4はこの362に含まない）。「不明」は新しい構成変更の承認として扱わない。ソースの利用箇所を採取し、以下の代表例は補題と利用側を読んだ。全356件の利用束縛・指定比較との両立を確定したという意味ではなく、適用前の確認資料である。

|追加ID・宣言|選ぶ証拠・利用側の確認|両立・処置|
|---|---|---|
|ICCH083 `CofiberSquareFamily.cocones`|exists_colimitCoconeFamily。cocones_projection→squares_spanで同じspanを回収|不明。任意の指定pushout族との比較・単位まで含むか確認して、必要なら同じ型/仮定で指定族に沿う選択へ|
|ICCH127/128 edgeLocalization / edgeLocalizationMap|exists_quasicategory_localizationと同じchoose_spec。GeneralLocalizationは局所化の普遍性を公開|不明。指定hammock/coherent nerve模型と同一視する利用があれば比較を組み込む。存在だけから指定模型との等号を宣言しない|
|ICCH467 strictSemifreeColimitFamily|exists_colimitCoconeFamily。forget/evaluationとの全高次単体の一致を回収|不明。後続の指定derived coconeの比較・単位との一致は追加照合が必要|
|ICCH519 dgGluingFactorZeroObject|dgGluingFactorZero_exists。同じchoose_specのisZeroをFactorObjectsで使用|要らない。選んだ零対象の性質を使用し、別の固定対象との等号を要求しない|
|ICCH520/521 dgGluingZeroObject / dgGluingZeroRepresentableIso|dgGluingZeroRepresentative_existsと同じchoose_spec。PositiveShiftRepresentationは同じ対象の零性を使う|要らない。対象と同型は同じ存在証拠から一組で選んでいる|
|ICCH499 dgGluingNormalizationCompositionTetrahedron|同名_existsが同じ正規化の三面を固定。NormalizationAugmentationCoherence / NormalizationSourceTetrahedronはその面等式を使う|要らない。別の指定充填との等号は追加要求しない|
|ICCH560 truncatedConeNormalizeNext|退化表示の存在。基本退化上の標準値の法則を同ファイルで回収|要らない。表示の選び方を標準値の補題で消してから使う|
|ICCH108 chosenEqToHom|∃ f, f = eqToHom h。chosenEqToHom_eqを後続のArrow等式で使用|要らない。存在命題自体が指定射を固定|
|ICCH179 smallLeftUnstraighteningComparisonOfFunctorIso|指定functorIsoからcomparisonの存在を選ぶ。③-aの変更ファイルに一致|不明。同じファイルの並行変更を取り込んでから利用側を再照合|

「要る」に変わるものの直し方は、**同名・同型・同仮定を保ち、指定対象・指定比較射・単位/評価の一致を含む証拠から選ぶ**こと。同じ仮定からその証拠を構成できなければ強い前提を足さず保留。存在命題を強く見せるだけ、任意の選択が指定構成と等しいと仮定するだけの修正はしない。意図的なchoose本体の変更は移動だけのv3b差分と区別し、承認された対応と検証を記録する。今日は置換0。

## 3. §6 DifferentialGraded/の分類（紙）

[dg-classification.csv](../../../research/infinity-consolidation-w1/dg-classification.csv) に指定と同じ形（path/module/lines/classification/destination/coverage_items/external_importers/basis）で**473本＝本体・集約164、Checks309**を全件記載した。既存の∞への直接接点はすでにInfinityCategories側にあり、DG本体にはdgNerve/QCat/Quasicategoryの新しい実装候補は見つからない。Category/ObjectImageのnamespaceはInfinityCategoriesでも、構成は充満dg像と厳密なdg関手分解なのでdg理論として据置。Presentation/GeneratedHomの∞ namespaceのopenも実内容は係数/生成Homの証明であり、名前だけで動かさない。

Derived/Projective、BimoduleTensor、ScalarExtension等のsemifree解像度は通常のdg・導来tensorの構成。semifreeという語だけを根拠にModelsへ移さない。現段階では**既存DGからの移動0、dg nerveの追加切出し0、∞模型の追加切出し0**を提案する。本文・module docstringと関連語の全体走査による主用途分類で、混在する宣言のnative所有元まで確認した分類ではない。

今後∞対象の模型としての宣言を分離する必要が見つかれば `InfinityCategories/Models/DGCategories/`、dg nerveの性質ならKerodon2.5の `ExamplesOfInfinityCategories/DifferentialGradedCategories/` へ別に表を出す。Checks309は動かさずDG監査の受け入れを保持し、Asymptotic側のVerdier5本への依存も今回切らない。対称スペクトルとBF Ωスペクトルの二系統はIC-3のModels/Spectra/Symmetric・OmegaSpectraで扱い、互い・HAとの比較が未実装である点を目録へ残す。

## 4. B1 小さい葉の統合案（適用なし）

80行以下の∞ファイルは現HEADで**10,447本・224ディレクトリ**。[章/主題別の全候補](../../../research/infinity-consolidation-w1/b1-chapter-candidates.csv)。これは内容・依存の統合可能性をまだ審査していない上限候補。rootや監査入口への直接importまで数えた「importerが0」の厳しい意味の葉は33本だけで、入口/互換moduleが多い（[別表](../../../research/infinity-consolidation-w1/b1-leaf-candidates.csv)）。したがってimporter0を統合対象の唯一の条件にはしない。

**単位**：同じ文献の同じ節、同じ主題、同じtier・実装境界の小さな連続依存群。章全体を一つにはせず、4〜8本を目安に1本の主題ファイルへ。範囲外のmoduleを経由して戻る依存がある群は統合しない（外部を挟む循環を作らない）。namespace、universe、section variable、include/omit、local notation/attribute、open/scoped、set_option、privateのscopeを群ごとに確認する。

**上限案**：1統合12元ファイルかつ800ソース行。最初の試行は4元ファイル・400行以内、初回の夜全体は10群・80元ファイルまで。保存比較でdriftが出た群は丸ごと取り下げる。main全体を一度に2,000本へ減らす目標をこの束の約束にはしない。

|最初の具体候補|元ファイル|合計行|狙う単位|
|---|---|---:|---|
|ComplexLimits/Codiskの小群|Codisk46・CodiskHom48・CodiskAdjunction38・CodiskFibrations50|182|複体のcodisk・Hom/随伴・fibration。依存凸性とscope確認後に1群|
|AlexanderWhitney/CochainCounitの小群|CochainCounit50・CochainCounitLaws49・CochainCounitValues65|164|余単位の値と法則。同じ仮定・notationの確認後に1群|

上は統合案で、ファイルは動かしていない。引用/タグと旧名の存在一覧を保存し、全宣言（private/生成を含む）のv3b未説明0、型・本体・公理・kernel属性を検査。B1と単なる移動は別のamendmentに分けて原因を追える形にする。

R8の275群/余分364個は [2026-10-23の調査](../../../research/infinity-refactor-audit/r8-duplication.html) の過去値。元の中間データは当時の一時ディレクトリだけ、と明記されている。現HEADの同一性とnative所有元を取り直してから同じ節内の共通所有元へ寄せる。文字列一致だけで証明・公開名を削除せず、元の禁止importを逃がすための重複（F1/F1B等）を再び逆依存に戻さない。今日は削除0、再実測した重複群0。

## 5. B4 root外監査モジュールの整理案（適用なし）

正式 `audit_manifest.txt` の106本の静的importを起点にした、tracked moduleの閉包からrootの閉包を引くと**4,332本**、∞分は**1,146本**。IC-1の2,264本は全てroot閉包内で、**IC-1移動対象のroot外0本**。[全件表](../../../research/infinity-consolidation-w1/root-outside-audit.csv)。旧監査/テストまで全scriptsを起点にすると4,459本となるため、正式106本に絞った4,332を採用した。計画書の2,794/未使用60は別時点・別計測なので、この紙の数字に合わせて書き換えない。run_cmd内の動的importModulesや .olean の実閉包を含む公式の計測ではなく、明朝のnative調査で差を照合する。

|現source-root外の領域|本数|今回の提案|
|---|---:|---|
|InfinityCategories|1,146|下記の領域単位でrootへ揃える候補を精査|
|KST|1,921|IC-2〜4の資料へ。IC-1では動かさない|
|HomotopicalAlgebra|689|模型/一般部品の整理と同時に精査|
|DifferentialGraded|309|Checks、指示により据置。rootへ足さない|
|Spectra|244|IC-3で精査|
|CategoryTheory / Asymptotic / BhattScholze|20 / 2 / 1|範囲外、所有レーンへ資料のみ|

**統合の単位と上限案**：Kerodonの一つの節、HAの一つの主題、Modelsの一つの模型ごとに「公開本体」「受け入れ/検査だけ」「互換/旧経路」の所有を分ける。公開本体だけは既存の章/主題の集約入口へimportを揃える。最初は**1節・50モジュールまで**、次の検収済み夜も1回**200モジュールまたは1領域**を上限とする。rootに全監査のmoduleを丸ごと足す方式は採らず、Checks/停止経路などの扱いを維持する。削除の初期上限は**0**。BR8の旧60本は現在の利用者・公開名・対応文献・他枝/blueprint/draftsの利用を照合し、削除個別表の確認を得るまで保持する。

A3/A4は同じ領域単位に合わせ、全対象を一回importし、moduleDataのconstNamesから各宣言を一回検査、訪問済みを領域で共有する案。既存の#checkは所有元付きの存在一覧（生成物）、禁止importはaudit_imports.py/layers.jsonへ移す。旧監査の「module/decl/公理/sorry/native_decide/禁止import/引用」の要件から新監査への対応に欠落0を確認してから旧監査を外す。今日の紙では監査・manifest・rootを一切変更していない。

## 6. 提出物・再開条件

資料の入口は [research/infinity-consolidation-w1/README.md](../../../research/infinity-consolidation-w1/README.md)。gitへ入れるのは紙、全件の移動/改名案、分類/候補の表、静的集計を再現する研究用Pythonのみ。raw source captureとsource graphのcacheは `/private/tmp/ic-w1-*` に置き、既存のOE-W1証拠本体は再追加しない。

紙の形式/件数/参照先/ソースSHA/移動先の単射性と、層の移送予覧を静的に確認した。Lean build、対象build、v3b、引用属性のnative照合、root、正式全監査、verifyは**全てこのレーンでは未実行**。紙をコミットしたら停止し、ユーザーの紙の確認と今夜のroot後の原環境の準備を待つ。他枝も進むので、再開時にmainをmergeし、表・分岐影響・原環境のHEADを取り直す。

## 7. 正式採取の再開（11-17 夕、準備中）

### 7.1 検証済みmainと独立した原環境

調整役の11-17夕の連絡を受け、main `35988dd08` を merge `414be0de2` で取り込み、同HEADの独立した `/private/tmp/ic-w1-before-414be0de2` を保持した。承認済み2,264ソースのSHAは全件一致。本体・検査スクリプトも検証済みmainと同一。その後のmain追従 `94b28b53b` は昼適用・root後停止の§11等の文書だけで、原環境の数学ソースは変わらない。

mainのbuild treeの広いCOW複製は、今回の依存閉包にないPointwiseColimitCoconeFamilyの成果物で待機したため中断。実際の対象のproject依存閉包 **9,222モジュール**について必要なolean/private/server/ilean/irを独立保持し、代表6本はSHA一致・inode相違を確認した。追加の5,726成果物をCOW複製。第三者packagesだけを共有し、projectのbuild directoryは共有していない。

最初のcompiler参照採取は `lake --no-build setup-file` のキャッシュ復元で、複製先のreadonly成果物を上書きできず停止した（sourceの型エラーではない）。リンク共有されたinodeは先に独立COWへ置き換えてから、複製先だけに書込み権限を付けた。355,155ファイル、うち新たにリンクを分離した5,949本。元cache/main/他worktreeのinodeの権限を変更していない。依存のno-build再確認は成功し、失敗ログもgit外に保持した。

### 7.2 native所有元と正式な改名案

`oe_native_owners.lean` の実環境で、**2,264モジュール、18,305宣言、private4,335**を採取。module・ユーザー名・privateフラグの組に重複0。宣言0のmoduleは3本（ComplexLimits/ExtendTruncationHom、ExtendTruncationHomNaturality、TruncationInclusionNaturality）で、module/importの移動対象から落とさない。

移送名を持つ実宣言は **18,254**。ソースの候補表では判断できなかった、他の移動型への拡張は、その型の実際の新namespaceへ揃えた。source-free compiler equation/congruenceは655件を別に調べ、所有ファイルの接頭辞だけでは誤る2件を親に合わせた：

- IdentityCoconeHomの `coconeIdentityProjectionNullhomotopy.eq_1` は実際の親に従いProjectiveHomotopyInverseへ。
- Surjection/CompositeRecoveryLabelsで需要生成された `BarrattEccles.insertedPosition.eq_1` は、非移動のBE本体の親名を保持。

opensの曖昧な宛先は0。移動しないBarrattEccles/StoppedRoutes/Interface/Modules/PowerOperationとroot EInfinityは明示的に元のopenを保持する。型・本体・公理を変える対応ではない。正式表はgit外の `preparation/namespace-rewrite-map.json`、`public-owner-map.json`、`compiler-children.json` に保持し、privateの移動後kernel名は移動後の実観測で対応する。ordinalで対応づけない。

既存の補助の名前検証が、実在する13件の`?`を含む名前を拒否したため、git外に置いた補助のコピーだけを当該識別子構文に対応させた。共有のrewriter・snapshot・比較器は変更していない。v3b専用binaryは既存と同じSHA `044d36482e16a0708bdb58e6b3f5cdbf1f53b5deec92e5921d07b290109d45b9`。

最初の所有元採取とv3b toolのコンパイルは84.80秒、RSS最大7,626,047,488 bytes、終了0、bulk鍵返却済み。

### 7.3 compiler参照・openの束縛（継続中）

nativeの実所有元、実ileanの参照、source importの閉包とliteralを合わせ、**3,858ファイル**を原ソースの採取候補にした（対象2,264本と利用側・監査）。Archiveは§10/BR56により除外。ileanの欠落を参照0と扱わず、依存閉包から保守的な候補を補った。

採取器のsource-exactness/configured options/async=falseと元のガードを維持する。native化した同じ採取器は、AW/BoundaryCutsとProjectiveModelで、元の方式とのsource/module/refs/commands/optionsの完全一致を確認した。Lake設定も、公式 `setupServerModule` API・同じno-build条件でまとめて読み出し、通常CLIの3ライブラリ例とaudit_einfinityの全JSON欄・出力バイトが一致した。visibility・importArts・dynlibs・plugins・package・optionsを省略しない。

最初の実採取は **92／3,858成功**、231.36秒、RSS最大5,915,787,264 bytes、2 reader、失敗0。設定採取は **3,682／3,858**まで完了。残りの原環境依存に既存Compatibility/Legacy群があり、同じbulk制限で順にキャッシュを用意している（Legacy19まで成功、数学ソースの変更なし）。92ファイルのdry previewは全て生成可・保留0、本体への適用0。匿名instanceの6 binderは、元のnative定義とcompilerのkeyword spanを確認し、local/private/型/値/priorityを保って同じ移送名を明示する案として記録。移動しないBE namespaceの3 openも元の束縛を保持する方針を明示した。以後の全件採取・previewは継続中で、対象build/v3b/rootの成功を意味しない。18時時点ではnative参照/open採取 **430／3,858**、プレビュー430本・変更218本・保留0。元ソースFreeProbeRelativeUnitWeakは190秒の期限切れ後、単独250秒枠で196.84秒・RSS5.31GBで成功した（OE-W1でも同じファイルに原環境の採取時間の問題があり、今回は原ソースそのままのInfoTree採取まで完了）。期限切れログも保存し、未完了を成功に数えていない。

### 7.4 他枝と停止条件

最初のnative所有元に基づく再照合は、math/inf-supply・math/scheme・research/cited-coverageの**合計0ファイル**。各枝と作業木が触るソースを読み、移動providerへ届くimport閉包と修飾参照を照合した。unqualified/open経由の利用も、providerがimport閉包にないことから排除する。作業中の枝なので、適用直前にもう一度取り直す。

証拠本体の正本は **`~/serre-evidence/ic-w1/ic-1/`**。既存の実行コマンドの `/private/tmp/ic-w1-evidence` はそこへの別名。リポジトリへは目録だけを追加する。source/context/configuration、実所有元、両採取器の同一性、各bulk枠の時間/RSS/失敗を保持する。

§11に従い、採取と影響確認が完了し30ファイル以下なら、開始前に一行知らせて昼から適用する。以後は静的→対象build→v3b未説明0→引用/タグ→root。root成功で報告をコミットして停止し、正式全監査は調整役へ。直せない移動または他枝30本超は停止・報告。BR55の356件・B1・B4には進んでいない。

移動適用一覧：済み **0／全体26（うち追加0）**。

### 7.5 適用前の静的照合（継続中）

現時点の全体graph 34,087モジュールに対し、移送したKL-W1設定で既存違反172件の像が完全一致し、追加・消失0。全モジュールのW1/W2a/W2b禁止判定と実装境界の判定、移動宣言を持つモジュールのtierを保存した。W1の移送禁止リストは、全モジュールの判定同値を確認した30接頭辞へまとめる案（適用なし）。既存の違反を解消したとの判定ではない。

監査の対象選択もArchiveを除く33,542 projectモジュールで、元の述語と移送後の述語が全件一致。新しい15ディレクトリの接頭辞と11単独モジュールを加える案で、対象の追加・欠落は0。数学的な監査やv3bの代替ではない。

17時台の他枝再照合では、③-aの364ソースと⑥の3,143ソースは影響0。新しい調整役BR54枝の `scripts/audit_citations.lean` がroot経由で移動providerに届くため保守的に1本を数え、合計1本（直接import変更0）。依然30本以内。各枝のHEAD前後一致を確認した。適用直前に再採取する。

## 8. 適用前の停止（11-17 18時）

### 8.1 原環境で失敗した直接importer

全tracked非Archive import辺の追加照合で、初期採取候補（library/scripts限定）に漏れていた [CrystallineInput.lean](../../bhatt-scholze/drafts/A1/CrystallineInput.lean) を発見した。移動対象 `SerrePositivity.EInfinity.Operad.CommutativeAlgebraFunctor` の直接importerで、採取候補を3,858から**3,859本**へ補った。移動2,264本・26単位の追加ではない。

同じ凍結原環境 `414be0de2`、**ソース無変更**で公式Lake設定を採取し、原native frontendを実行。ハイフンを含むmodule名の引用表記を直した後、18.60秒、終了1。エラー19件、先頭は81行の `SerrePositivity.EInfinity.EInfinityTheory` 不明、89行の `SerrePositivity.BhattScholze.PerfectoidizationInterface` 不明。そのほか `polyNerve`、`Cosimplicial.strictShapeNerve`、`discreteAlgebraModule` 等の不明名と型不一致がある。これは**移動後の失敗ではなく、現在の原環境の失敗**。root・全監査が通ったという調整役の連絡と矛盾するものではなく、当該下書きはroot外にある。

§11の「直せない移動が出たら止まって報告」に従い、当該下書きを黙って除外したり、数学的な定義・主張・証明を直したりして採取完了とせず、適用の前で停止する。原環境で型検査できない下書きの追従を、どの検査条件で扱うかが未確定。移動そのものによる不具合が見つかった、との判定ではない。

native所有元で分かる追従候補は以下の3箇所。ただし下書き全体の束縛・保存比較を確認したパッチではなく、**未適用の案**である。

|箇所|旧名／旧module|候補の新名／新module|
|---|---|---|
|34行 import|`SerrePositivity.EInfinity.Operad.CommutativeAlgebraFunctor`|`SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebraFunctor`|
|130行 関手|`SerrePositivity.EInfinity.commutativeAlgebraFunctor`|`SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraFunctor`|
|130行 制限|`SerrePositivity.EInfinity.Operad.restrictAlgebra`|`SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebra`|

### 8.2 停止時点の結果

|項目|結果|
|---|---|
|原native所有元|2,264 module・18,305宣言（private4,335）、採取済み|
|正式参照/open|**650／3,859成功**、未完了。原ソースの失敗を成功に数えていない|
|dry preview|650本、変更289本、ガード保留0。本体へ適用0|
|正式Lake設定|3,683／3,859、未完了|
|原環境の依存準備|既存Compatibility/Legacy01〜30のビルド成功、30／51。移動後の対象ビルドではない|
|KL-W1の層|移送予覧172→172、追加・消失0。既存違反あり|
|もう一方の層|DGAlgebra26本がDG基礎に自動分類されると新しい制約18辺。実装側の `DGAlgebras` 行（rank11、KL-W1はConsumersのまま）を置く案で、全140,967辺の直接規則が元と一致。既存DGの規則・core集合は不変。適用なし|
|禁止・実装判定|全34,087 moduleの元と移送先で一致|
|監査の対象範囲|非Archive project33,542 moduleで元の述語の像と一致。監査の実行・統合を完了した意味ではない|
|他枝影響の最新観測|③-a0、⑥0、cited0、調整役BR54のroot経由1本、合計1本。直接import変更0。適用前に再観測が必要|
|移動後の検査|対象build・v3b・引用/タグ比較・root **すべて未実行**|
|本体の変更|Lean・層設定・監査・rootへの適用なし。移動0／2,264本、済み0／26単位|

source・oleanの独立性の準備、同じ採取器のnative化、公式Lake設定APIの同一性確認、全chunkの時間/RSS、成功・期限切れ・原環境エラーのログを保持した。650本は同じ原ソースのInfoTree採取であり、エラーのある下書きを別方式で成功扱いに置き換えていない。A3/A4の監査統合も未実施。BR55不明356件・B1・B4、Archiveには変更なし。

### 8.3 証拠と再開点

正本は `~/serre-evidence/ic-w1/ic-1/`。リポジトリへは [目録](../../../evidence/ic-w1/ic-1/manifest.json) だけを置く。対象HEADは `7101c0da6`（main `adc221d19` を取り込み済み）、凍結した数学ソースは `414be0de2`／検証済みmain `35988dd08` と一致する。

- `preparation/draft-stop-review.json`：停止理由・原ソースSHA・native所有元に基づく3箇所の案。
- `preparation/references-native/formalization-plans.bhatt-scholze.drafts.A1.CrystallineInput.log`：原環境の19エラー。
- `preparation/draft-native-002-controller.log.json`：単独枠20.64秒、最大RSS2.54GB、終了1、鍵返却。
- `preparation/owners-before.json`・`public-owner-map.json`・`namespace-rewrite-map.json`：native所有元と改名案（B4の材料、後で移動後の実所有元を対応させる）。
- `preparation/preview-progress.json`・`reference-native-progress.json`・`setup-progress.json`：未完了件数。
- `preparation/layers-transport.json`・`layer-prefix-compaction.json`・`dg-layer-review.json`：層の移送案と同値性。DG分類を直す前の18辺も `top-layer-direct-transport.json` に保持。
- `preparation/branch-impact-native.json`：枝のHEAD前後一致付きの観測。再開後に更新する。
- `IC1_STATE.md`：原環境と再開手順。追加の採取を自動で走らせる処理は停止済みで、現在のbulk ticketはない。

下書きの扱いが確定したら、全採取・原環境準備を完了し、他枝影響を再取得する。30本以内を再確認し、開始前の一行連絡後に初めて適用する。以後は静的→対象build→v3b未説明0→引用/タグ→root。root成功で完了報告をコミットし停止する、という§11の停止点は未到達である。
