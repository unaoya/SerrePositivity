# IC-W1 ∞ コード整理報告

## 現在地（2026-11-17、レーン⑦）

**IC-1 段0（紙）を提出し、適用前の停止点。Lean変更・ビルド・native宣言採取は実行していない。ユーザーの11-17の指示に従い、この紙をコミットして止まる。§3の条件付き事前承認による準備・適用への自動続行はしない。**

- 最初の `pwd` は `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ic` と一致。枝 `refactor/infinity-consolidation`。起点 `98a6465b4` は `merge/night-2026-11-17` と同じで、OE-W1段1の停止点を含む。
- 指定の `git merge main` を実施し、`1cfcb6856ae922b3c8d047fe223173d0681f71ae`。取り込んだmainは `a87444d438295e71a461fb945d02d5537288ed9c`。差分は調整記録だけ。今夜のroot・全監査の結果を先取りしない。
- 指示書 [infinity-consolidation-w1.md](infinity-consolidation-w1.md) §0〜§8、[OE-W1報告](report-organize-einfinity.md) とその全件分類・B4、`research/infinity-outside-map/files.csv`、費用計画、③-aの指定md/jsonを参照。
- 今日の資料はソースの静的な案。**正式な宣言所有元、private/kernel名、生成宣言、open経由の束縛の採取は、今夜のroot後、明朝以降**。`.olean` の不足を理由に今日ビルドしていない。

段0一覧：済み **5／全体5（うち追加0）**：IC1-0a 移動/改名・層/他枝、IC1-0b BR55、IC1-0c B1、IC1-0d B4、IC1-0e §6のDG分類。
移動適用一覧：済み **0／全体26（うち追加0）**。単位IDは下表のIC1-族名。IC-2〜IC-5には進まない。

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
