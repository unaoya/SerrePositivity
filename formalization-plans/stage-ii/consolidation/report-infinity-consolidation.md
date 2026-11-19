# IC-W1 ∞ コード整理報告

## 現在地（2026-11-19、IC-2 第1組の停止点）

第1組の4単位・7本を移動し、205本の対象ビルドと v3b（未説明0）、引用・タグの再照合（欠落・余分0）を完了した。**一覧：済み4／全体28（うち追加0）**。次の組は調整役が第1組を取り込み、連絡を受けてから再開する。[第1組の結果](#ic-2-適用-第1組)

## IC-2 の段 0 の提出時点（履歴）

IC-1 は main `fdc4045ac` に取り込まれた。§13の調整役記録では root・正式全監査108本・sorry閉包が成功。IC-2 は main `1522321e5` で1,725本を再集計し、1,625本の配置案と三条件から届かない258本を報告した。main `cbcb40a59` の指示書 §14 で、235本を据え置く1,390本案を採用した。互換入口4本は台帳と外部利用を確認し、利用がなければ Archive へ移す。削除は0本。適用時期は調整役の計画に従い、今回は紙のコミットで止まる。[IC-2 の段 0](#ic-2-の段-0)

## IC-1の停止点（2026-11-18夜、履歴）

**IC-1の2,264本・26単位を完了。静的な移送・循環検査、数学4,314本と追従blueprint4章の通常ビルド、全4,314本のv3b（未説明0）、引用・タグ118→118件（欠落・余分0）、通常の `lake build SerrePositivity` が成功した。原参照3,858本と全native所有元の対応も検証済み。取り下げ0。承認済みのalias登録source-view補助を用い、raw FAIL2組・4件と診断・負例・承認を保持した（§12）。結果・改名表・証拠は§13。正式全監査とverifyは調整役が行う。完了報告をコミットしてIC-1で停止し、次の束へは進まない。**

- 現行の数学比較基準は引き続きmain `5cbfd7bb1` の独立環境。後続mainの470パス・93 Lean変更はblueprint・文書だけで、本体Lean・設定・scriptsへの変更0、IC-1適用パスとの重複0。全4,314対象の数学ソースSHAと、文書ビルド後のnative所有元採取に使った全成果物SHAは不変だった。
- 最新の静的結果は34,880モジュール・145,519辺、実適用と移送グラフの完全一致、循環0。3,020書込SHA・2,264旧パス削除を再検証。層は同じ診断条件で581→581、違反の厳密な移送差分0。上流395数学モジュールの未登録はそのままにし、同じ一時分類候補を両側だけへ渡した。未登録に接続する辺の移動端点0により、この差分は候補値に依存しない。絶対的な層PASSや395本の正式分類とは主張しない。
- 新しいblueprint93本の移動前後186ヘッダは、Leanの `Parser.parseHeader` と `Elab.HeaderSyntax.imports(includeInit=false)` で採取した。従来の全本文Python lexerが扱える184件はすべて一致し、独自の文字列記法で扱えない2件も除外せず、ソースSHA付きのcompilerヘッダを用いた。変更は4章のimport3トークン・完全修飾宣言名11か所だけ。4章の通常ビルド成功。文書生成データの本体を、数学4,314本のv3bが検査したとは記載しない。
- 他枝の最新再照合は1本（調整役BR54の `scripts/audit_citations.lean`）、新mainの文書追従4本を足して保守的に5ファイル。30本以下。改名表は実際の移動前後のnative所有元付きエントリに基づく `b4-actual/declaration-name-map.csv`（移動18,472件・private4,335件、26単位）。
- nativeの全体表41,197件（private6,316件）に対し、定義元別の表は41,490件。併合される証明の所有元293件を補い、全件対応。12件の生成matcher補助と8件のnotation補助の名前は、実際の公開親宣言の移送とcompilerが埋め込む所有元・namespace・参照宣言名の構造から解決し、同じ移送先の実観測名へ照合した。privateの番号で組み合わせず、Leanソース・共有v3b採取器・比較器には変更を加えていない。
- さらに併合された293証明（195定義元）の型・証明値から、nativeで直接参照定数と宇宙束縛数を採取し、実際の改名で差分0を確認した。元のv3bによる全体の型・公理比較と合わせて評価する補足証拠であり、この結果単独をv3b PASSと数えない。


<details>
<summary>採取・追従・限定修復の履歴</summary>


- 11-18午前の追従：③-aと⑥文書移動を含むmain `5cbfd7bb1` をmerge `eaa70995e` で取り込み済み。直前の対象ビルドは3,753／4,314本成功。incomingとIC-1の書込・削除パスの重複0。他枝のnative再照合は影響1ファイル（`coord/br54-citation-registry` の `scripts/audit_citations.lean`）、`math/inf-supply`・⑧は0、メタデータ重複0。30本以下の条件を維持する。
- 新しいmainの既存定義3本の変更が、保存比較対象437本・元採取ソース347本に届く（移動対象は `StrictHomology`・`HomInfinityComparison`・`HomInfinityComparisonInput`）。対象ビルドの次のbulk塊を止め、新しいmainの独立した移動前環境で比較基準を更新する。汎用監査2本は移動参照0・実参照先の依存変更0を再証明し、元の採取コンテキストを保持する。正式監査を再実行したとは記載しない。残る345本を再採取する。
- 14時の再開状況：数学ソース331本とrootの計332本、および監査ソース2本は新mainで再採取し、数学332本の書換えと適用済みソースの一致を確認した。さらに未変更の監査5本（F5・F7・infinity_stable・kst_fibration・localizing_invariants）は、実参照の移動先0・実参照先の依存変更0・module命令の追従0・書換えのバイト一致を証明した。汎用監査2本と合わせ7本は元の採取結果・元のreceiptを保持する。元receiptにコンテキスト欄がない場合も補作せずnullで記録する。残る監査ソース6本は新mainでの採取が未完了。BH stage2とderived_infinityの270秒期限切れは成功へ読み替えない。これはソース参照の検証であり、調整役が行う正式監査の完了を主張しない（`main3a-generic-audit-reuse.json`）。
- 新グラフ34,807モジュール・143,812辺の実適用輸送と全書込SHAは一致、循環0。上流の追加395本は層表に未登録で、IC-1前後とも未登録のまま保持。395本に接続する1,612辺には移動する端点が0本なので、未分類値は輸送差分に影響しない。同一の一時分類候補で検査器を動かすと289件→289件（差分0）だが、これは395本の正式分類や従来172件の結果の更新を意味しない。候補をリポジトリへ追加せず、上流の未登録事項として明示する（`main3a-static-rebase.json`・`main3a-unregistered-tier-independence.json`）。
- 昼の二枠化：main `657048b94` をmerge `0db86213b` で取り込み。incoming 53パスにLean変更0、IC-1適用パスとの重複0のため、数学上の比較基準は `5cbfd7bb1` のまま。⑦の鍵はbulk一本、全体読込も一本を維持し、共有設定による一枠への復帰を待機規則に従って受け入れる。
- 11-18昼のユーザー指示「まとめてビルド」「2レーンのうち1レーン自由」に従い、以後の対象ビルドは残りの全targetを同じ通常の `lake build` へ渡す。`LEAN_NUM_THREADS=1` と同時Lean読込1本のガードを維持し、同じbulk一本を使う。時間枠に達したら生成済みのネイティブ成果物を保持して再開する。各対象のreceiptには共通の実コマンドを残し、その呼出し全体が終了コード0になるまで完了とは数えない。昼3〜5分の区切りも維持する。
- 新しい移動前環境では、対象4,314本とrootの計4,315本が実際のLake鮮度検査を通過した。root外Legacy43本を依存順で補完ビルド。正式な全体所有元は41,197件で旧観測と名前・所有元・private・kernel名の差分0。モジュール別private表では41,490件を採取し、全体表で併合される公開された証明の所有元293件を補足した（すべてglobalの型・宇宙と一致）。移動する2,264モジュールの所有元付きエントリは18,472件、うちprivate 4,335件。これらは名前採取の結果で、移動後の保存比較PASSを意味しない。
- 新mainの依存変更に当たる成功証拠34本をログごと保存して再検査対象へ戻し、3,719本はソース署名と全依存の不変を検証して保持した。残りの対象ビルドは595本。再採取・書換え再照合後、IC-1に依存しない上流3,638本の成果物を独立して利用し、作業木で鮮度を検査してから対象ビルドを再開する。引用は新しい移動前環境と移動後環境の全4,314本を同じ範囲で採取し直す予定で、旧3,840本・96件を現在の比較基準として流用しない。

- 検証済みの数学ソースのmain：`35988dd08b05d27a263fc210bafdadd0b1fc4c11`。root・全監査・sorry閉包通過は調整役の11-17夕の連絡に基づく。⑥の291本はmain `1fb2c6dcc` のmerge `f43e76835` で取り込み済み。現在は2iを含むmain `5cd32e97b` をmerge `55edf0b90` で取り込み、最新の全体グラフで移送を再確認済み。
- 凍結した原環境：`414be0de2d7c125167e4ed77505c8de44cddfe31`。承認済み2,264本と採取候補全件のソースは、⑥取り込み後も差分なし。追加された上流ファイルを古いプレビューで上書きしない。
- 移動前の独立環境：`/private/tmp/ic-w1-before-414be0de2`（同じHEADのdetached worktree）。mainのビルド済み成果物をCOW複製し、projectのoleanを共有せず保持する。第三者packagesのみ参照共有。
- 採取：native所有元（private/生成宣言を含む）→原compiler参照/openの束縛→正式な改名案→他枝の影響を再集計。影響30ファイル以下なら11-17夕の追加承認により昼から適用してよい。適用直前に一行連絡する。昼のbulkは3〜5分、夜は30分以内。静的→対象build→v3b→引用/タグ→rootまで確認し、root成功で報告をコミットして停止。正式全監査は調整役が実行する。影響30本超、または直せない移動が出た場合は停止・報告する。
- 11-18未明：全体読込は常時1本に固定し、共通singletonとbulk鍵を併用。対象ビルドは652本通過後に、移動していない `OperadMonoidalImage` の補助関数のドット記法で停止した。元のnative所有元・binderを照合し、型の移動先の名前空間へ6個のaliasを追加した（元の宣言名・型・本体は変更なし）。修正後の当該モジュールのビルドは成功。実グラフ・全書込SHAの静的再照合もPASS。実際の移動後所有元とv3bによる確認は引き続き必要。
- 対象ビルド904本通過後、孤立したモジュール間で同じ公開名を持つ2宣言の所有元の取り落としを確認した。全採取のbinderを照合し、`FiberRanks.card_filter_lt_orderEmbOfFin` と `TensorFamilySubstitutionBlocks.tensorFamilySubstitutionStep_post` のcontext-native所有元を補足。改名先は既存表と同じまま、実際の改名漏れ3ファイルだけを修正した。`TensorFamilySubstitutionBlocks` 自身のソースは既に正しく、変更不要。元の型・本体は変更せず、3ファイルの逆依存に入らない904本の成功証拠をSHAと実グラフで検証して保持した。
- 1,941本通過後、`EraseAlgebraAdjunction` で同じドット記法の問題を確認。採取全件を再照合し、「直上のreceiver型が正式移動表にある」「補助関数自体は未移動」「元のnative所有元とbinderが一致」の条件を満たすドット参照は17補助関数・5ファイルだった。既修正の6個を保ち、残る4ファイルへ11個のaliasを元compilerの宣言末尾で追加。aliasを除くと修正直前のソースに完全一致することを確認した。成功済みで影響するのは `EraseOperad` 1本だけで、再ビルド対象へ戻した。
- 限定修復後の書換え器で正式採取3,858本を全件再検証し、保留0・raw改名ハッシュ不一致0、メタデータ付加後のプレビューと実ソースの不一致0を確認した（`preview-revalidated-after-repairs.json`、約101秒、Lean読込の追加なし）。aliasを追加した4ファイルのビルドも全件成功。対象ビルド全体は引き続き検査中。
- ⑥の2i（main `72bc75e8b` を含む最新 `5cd32e97b`）を、merge `55edf0b90` で取り込んだ。上流の33 Lean変更とIC-1書換え対象の重なり0。保存比較4,314本の全依存先に上流変更はなく、成功済み3,700本を保持できる。新しい全体グラフ34,410本・142,196辺で静的検査PASS、層172→172、他枝の再集計は対応表込み1本のまま。mainのソースを固定し、元の不変ライブラリ＋独立AG複製＋独自にコンパイルした適用前rootを用意してrootのnative採取を更新。公理・sorry監査の2ソースは、IC編集0・移動宣言参照0・実参照先の依存変更0を検証し、元のnative採取と元の実コンテキストを保持した（`main2i-generic-audit-reuse.json`）。公理監査ソースの再採取は250秒・270秒で期限切れであり、その再実行の成功を主張しない。現行の正式な全監査は調整役が行う。これは適用後rootの完了判定ではない。
- §10（BR56）：Archiveを追従対象と外部importer数から除外。復帰時に改名表で直す。
- BR55不明356件は据置。B1/B4はIC-1移動後の別amendment（B1最初4本/400行、B4最初1節/50本）。

</details>

一覧：束IC-1 **済み1／全体1（うち追加0）**、移動単位 **済み26／全体26（うち追加0）**。移動2,264本、取り下げ0。対象・保存比較は各単位、引用・rootは共通範囲の結果として検収した。

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

## 9. §12の決定を受けて再開（11-17 夕）

ユーザーの停止報告0edfe41f2への決定を受け、main `73b052b2c` の§12をmerge `ec6c226be` で取り込んだ（差分は指示書だけ）。§8の停止は解消。`formalization-plans/bhatt-scholze/drafts/` はビルド・監査しない設計の紙で、正式な参照採取と30ファイルの外部影響数から除外する。

CrystallineInputは**「移動の前から 19 エラー、追従は文字の置き換えのみ」**。§8.1の3箇所だけを元ソースSHAと置換前の文字に照合して、別の文字置換プレビューに用意した。型検査やv3bの成功扱いにはしない。draftsの古い名前全体の整理はBSの整理レーンの段0で扱う。

正式な採取候補は再び3,858本で、650本成功を引き継ぐ（過去の3,859本の分母から設計の紙1本を除いた）。公式Lake設定は3,682／3,858、元のCompatibility依存は30／51から継続する。Archiveを除く全import辺の移送確認には、別枠の文字置換後のdraft importも含める。適用のゲートは全正式採取・プレビューと他枝の再観測30本以内。開始前に一行知らせ、その後は静的→対象build→v3b未説明0→引用/タグ→root。rootが通ったら完了報告をコミットして停止し、正式全監査は調整役が行う。


### 9.1 ⑥の取り込み待ちと採取の継続

11-17夕の追加指示により、調整役の⑥（AlgebraicGeometry 291本）の取り込み完了連絡を待つ。mainのHEADが進んだことだけを完了の合図とはみなさない。適用のゲートは閉じたまま、原環境の採取と適用前プレビューだけを継続している。完了連絡後に `git merge main`、上流差分の照合、他枝の影響の再取得を行い、30本以下を確認して開始前に一行知らせる。

正式な参照/open採取は3,719／3,858本まで成功。直近の6並列の塊はメモリ上限32GBで停止し、失敗・未受領分を成功に数えず、並列数2で続行する。各塊は引き続き共有bulk鍵と280秒の外枠を守る。正式Lake設定3,858本と原Compatibility依存51本は完了した。構築子の省略記法、既存export経由のドット記法、名前空間の入れ子は、原native所有元・ソース・.ileanの定義位置に照合してプレビューの審査記録を作る。これらは移動後のビルド・v3bに代わる検査ではない。


20:30時点の受領記録では3,842／3,858本を確認し、その全3,842本の静的プレビューは保留ガード0件（変更3,000本、適用0）。メモリ停止時の進捗要約3,719本より受領記録が先行していたため、成功数はソース・採取物SHAを照合した受領記録を基準に明記する。残り16本の採取は2並列で共有bulk鍵待ち。本体候補3,840本すべてに原環境の自身の.oleanが存在することも確認した（存在確認であり、移動後のビルド成功ではない）。


### 9.2 ⑥の取り込み後（11-17夜）

main `1fb2c6dcc` をmerge `f43e76835` で取り込んだ。上流差分のLeanソース298本と正式採取候補3,858本の交差は0。追加291モジュールと既存AlgebraicGeometry集約ファイルは、移動対象の逆向き推移閉包の外にあり、採取候補の追加は不要。root・ツールチェーン・Lake設定・共有比較器の上流差分はない。凍結原環境のnative採取を維持し、静的な全体グラフを取り込み後のmainへ更新した。

他枝への影響は1本：`coord/br54-citation-registry` の `scripts/audit_citations.lean`（root経由、直接import変更0）。`math/inf-supply`・`math/scheme`・`research/cited-coverage` は0本。枝HEAD前後一致を確認。適用直前にも再取得する。

層の再検査は34,378モジュール・142,003辺。KL-W1の違反172→172、追加・消失0、禁止・実装判定とDGの直接規則の差分0。監査内の禁止prefix17箇所と、引用されたモジュール名・宣言名は、移動先でも同じ範囲となるよう適用前スクリプトで扱う。モジュール名と宣言名が重なる4例は、実際の監査の宣言存在要件を確認し、宣言側の正式改名を採用する。

原native所有元は比較候補3,840本へ拡張採取済み。残りの参照/open採取では `scripts/audit/bhatt_scholze.lean` が単独250秒でも時間切れ（255.87秒のbulk塊、最大RSS6.20GB）。型エラーや移動失敗ではなく、原環境の採取が時間内に終わらない状態。成功に数えず、短い枠で他の未採取ソースを確認する。短い枠に収まらない分は23時以降の枠で採取する。正式採取の全件完了と開始前の一行連絡より先に適用しない。


原native所有元の比較候補全件は3,840本・36,513宣言（private5,486）。v3bは変更されたソースだけでなく、未変更の推移的利用側も含む3,840本全件を対象とする。原環境の引用・タグ96件をnativeメタデータから採取済み（134.42秒）。件数と重複を保持し、移動後に実際の宣言名・所有moduleで照合する。


### 9.3 取り込み後の環境への照合と残り5本（22時台）

上流298ソースの本文変更まで含む依存閉包を照合した。ライブラリ3,840本とrootを読まない監査の依存先は不変。root・audit_axioms・audit_sorriesの3本だけは新しいAGを読むので、取り込み後のW環境で同じnative採取器・同期frontendを使って採り直し、全3本成功した。原rootの採取物は履歴へ保存した。環境の不変性の確認が遅れた点を、この全依存閉包の照合で補った。

準備のための通常の適用前rootビルドは79秒で通過。これはIC-1適用後の完了判定ではない。公式Lake設定もWで採取した。正式採取は3,853／3,858本。残るBS領域・BS stage2・derived infinity・infinity stable・localizing invariantsの監査ソース5本は、依存先の上流差分がないことを確認し、ウォーム済みのW環境でも再試行している。250秒で終わらない分は未完了として保持し、23時以降に最大1,700秒のbulk塊で採取する。採取器・数学ソース・監査の処理は省略しない。

独立成果物は1,034,176ファイルの準備を完了。before側のhardlink29,233本をCOWで分離してから権限を整え、after側も別inodeで保持した。不足キャッシュ523モジュール・7,783ファイルを、ソース・toolchain・manifest・略号表一致の条件でmainからCOW複製した。既存cacheの上書きやビルド成功の流用はしない。

監査の単一backtick Nameリテラル3,939箇所は、実native所有元または実module対応に照合した明示編集として扱う。二重backtickと通常の意味参照のガードは維持。受領済み3,847本の再プレビューは保留0。最終全件プレビューと実適用後の静的検査は引き続き必要である。


23:14ごろのMac全体のファイル数上限到達について調整役から追加指示を受けた。全体を読む採取は常に1本とし、残っていた最大6本の既定値も1本へ固定した。再試行・所有元採取・引用採取・v3b・全体ビルドの重複起動を共通ロックで拒否し、対象ビルドも1モジュールずつとする。v3bのbefore/afterは直列。OSの上限は変えない。確認時の自分の全体読込プロセスは1本だった。


## 10. IC-1を適用（2026-11-18未明、検査中）

main 02d3c7a66（追加は文書のみ）をmerge 937dd5a6cで取り込んだ。正式採取3,858本・最終プレビュー保留0、全体グラフの計画移送と層の同値性を確認。他枝への影響は1本（対応表の追従による他枝作業ファイルとの追加重なり0）を再確認し、適用開始の一行連絡後に実行した。

移動2,264本・26単位を適用、書込3,020パス。BS draftの指定3文字置換と、現行の対応表10本の参照名・パスだけも追従した。対応表は判定・理由を維持し、歴史的検査記録は変更しない。draftは「移動の前から 19 エラー、追従は文字の置き換えのみ」。

実適用後の静的検査PASS：34,378モジュール・142,003辺のグラフは計画どおり。循環・新しい未解決project importなし、旧パス削除2,264と書込SHA3,020を確認。Archive・Util/Citation.leanは不変。既存の非数学ソースの未解決183辺と層違反172件はこの移動による解消を主張しない。

保存比較の範囲を、明示参照の採取候補3,840ライブラリだけでなく、推移的利用側を含む4,314本へ広げた。追加474本の既存native索引には移動する宣言への明示参照・移動moduleの直接import・旧namespace文字列がなく、ソース書換えは不要。暗黙instance選択のdriftも比較するために対象へ追加した。4,314本の依存先には上流298ソースの変更がなく、原環境のkernelを基準にできる。原実所有元は41,197宣言で採取済み。

全体読込・対象ビルドを1本に固定し、4,314本の対象ビルドを依存順に実行中。移動適用一覧：済み26／全体26（うち追加0）。完成検査は未完了で、対象build→実after所有元とprivate対応→v3b未説明0→引用・タグ→rootの順に続ける。正式全監査は調整役が行う。


## 11-18 昼の補足採取の停止処理

全体を再読込するモジュール別補足表のジョブは3回、昼の時間枠に達して終了した。次の読み取り専用ジョブを11:54:57に手動停止した際、外側の鍵の返却後も子プロセスが残り、11:59:34に採取を完了した。41,490件の完全なnativeデータは再検証して保持するが、この回を時間枠・鍵運用のPASSとは数えない。他レーンとの実読込の重なりは計測できておらず、マシン全体の上限を維持したとは断定しない。

現在の読み手は一本。今後の手動停止は実際の読み手か更新済みの補助ガードを対象とし、子の終了を待ってから鍵を返す。鍵の親だけを停止しない。補助ガードにはSIGTERM/SIGINTの後始末を追加し、別セッションの子を残さないことをLeanなしのテストで確認した（`guard-signal-test/result.json`）。共有の鍵スクリプトは変更していない。nativeファイルを直接読む再開可能な代替採取器も準備したが、移動前の完全なデータが得られたため移動前側では実行せず、移動後の補足表で使う。


## 12. 11-18夕：frontend aliasと保存比較の読取器（ユーザーが正式採用を承認）

通常の対象ビルドは数学4,314本・文書4章が成功、所有元付きnative41,490件は前後対応済み。896本までのv3bがPASS・未説明0だった時点で、次の0014組において、次の3生成補題が「added」とされたため正式比較を停止した。

- `SerrePositivity.EInfinity.Operad.eraseFreeAlgebraIso_unit_assoc`
- `SerrePositivity.EInfinity.Operad.eraseFreeAlgebraIso_inv_unit_assoc`
- `SerrePositivity.EInfinity.eraseDifferential_map_braiding_delta_assoc`

3件とも実際のbefore/after native行に存在し、kind・type_hash・body_hash・axioms・attributes・parent・moduleはすべて一致する。`EraseFreeGenerators` と `EraseAlgebraAdjunction` のafterソースで、既存 `lean_source.py` が `with_weak_namespace … export …` を未対応として読み取りを打ち切り、beforeでは元のlemmaへまとめていたreassoc補題をafterでは独立項目へ分類することが原因。元のraw比較は297→300・FAIL・差分3のまま保持する。

### 12.1 具体的な診断と採用案

外部の `diagnose_frontend_export_projection.py` は、すでに元compilerのbinder・native所有元・受け手の移動で確認した17alias（5ファイル・14ブロック）の**完全一致する登録コマンドだけ**をソース表示で空白化する。改行・位置を保ち、native宣言・型/本体hash・公理・属性・所有元などの全データは変更しない。before/after各側で、ソース表示以外の全JSONのdigestが不変であることも必須にした。未確認ブロックや数学的宣言を含むweak namespaceは拒否する。数学のLeanソースは書き換えない。

同じnative snapshotと共有 `bulk_compare.py` を使う診断は297→297・PASS・差分0。本体ハッシュを意図的に1件変更した負例はFAILとなり、`with_weak_namespace` の下へ新たな数学的定義を入れた負例も投影を拒否した。根拠は外部 `preparation/v3b/0014/frontend-export-diagnostic/diagnostic-summary.json` と原/表示用snapshot・比較結果・負例。**この診断単独を正式PASSとは数えない。正式採用・再比較は§12.3、全範囲の完了は§13に記録する。**

採用案は、共有のsnapshot・比較器を変更せず、各組のraw判定を保存したうえで、この確認済みsource-view companionを正式な検査入力として用いるもの。ソース表示以外のnativeデータの不変、14既知ブロック以外の拒否、採取器/比較器SHA、raw/表示用入力SHAをreceiptで検査し、表示後にも差分があれば停止する。以前のPASS組はalias登録を含まないことを確認し、含む組は保存済みnative入力から再比較する。任意の差分を除外したり、数学的な本体・型・公理の不一致を許したりする案ではない。

正式経路への組込みは自動承認レビューに拒否された。理由は「raw比較を保持しても、v3bのslot driverが新しい投影後の判定を受け入れる変更は、実際のFAILを継続可能なPASSへ変えるおそれがあり、現在の承認は診断までで、正式経路の変更までは含まない」というもの。拒否されたexecは起動せず、拒否時点では正式driverの判定経路を変更しなかった。承認前に間接実行で回避せず、その後§12.3の明示承認で正式採用した。共有採取器・比較器は引き続き不変。

### 12.2 昼の時間枠の追加承認

ユーザーが11-18に「昼も最大30分までよい」と明示回答。§11の昼3〜5分だけをこの承認で更新し、⑦は昼も最大30分（補助guard1,700秒）まで使える。鍵はbulk一本・全体読込のプロセスも一本のまま。昼の共有キューの優先順位、容量が一枠へ戻る場合の待機、メモリ制約は維持する。夜を待たずに未完了の原参照採取を再試行できる。

### 12.3 正式採用の承認と反映

ユーザーが質問「確認済みalias登録だけのsource-view companionを正式v3b手順（slot driver）へ採用して続行してよいか」に対し、**「正式採用を承認して続行」**と回答。承認を `frontend-export-official-path-user-approval.json` に固定してから、補助を組み込む操作を再提出し、自動レビューを通過した。初回の拒否やraw比較を消していない。

正式補助 `compare_verified_frontend_exports.py` は最初に共有の比較器をraw入力へ実行し、その判定を保存する。14既知aliasブロックがある組だけ、診断済みの表示投影後にも同じ共有比較器を実行する。両側のnative検査データ全体のdigest不変、source-view/projection/採取器/比較器/承認のSHAをreceiptで検査する。型・本体・公理・属性・所有元を変えず、表示後にも差分があれば停止する。採用後の0014組の個別比較はPASS・差分0、raw結果はFAIL・差分3のまま保存された。以前のPASS結果はalias登録を含まない場合だけ保持し、含む場合は保存済みのnative入力から再比較する。

数学のソースを完全修飾呼出しへ直す代案も参照だけ調査したが、承認された補助手順を採用したため適用していない。共有のsnapshot・比較器に変更なし。数学4,314本と文書4章のビルド結果・native所有元表も変更なし。

### 12.4 移動前所有元データの再観測

以前の鍵外で完了した採取の実行記録はそのまま保持したうえで、独立した移動前nativeファイルを鍵の下で再度読み、全41,490件のmodule/kernel_name/name/private/kindが元データと一致した。`before-native-module-reobservation/comparison.json` と `runtime.json` が新しい再観測の証拠。元の実行を規則適合へ読み替えず、元データ・比較計画も差し替えていない。

### 正式比較再開後の補足（0015組）

0015組のraw比較でも `EInfinity.Operad.monoidalImageComp.eq_1` が生成補題の分類差でaddedとなった。移動前後のnativeエントリは実在し、型hash・本体欄・公理・属性・所有元・親・kindは同一。参照定数と参照moduleも正式改名で厳密に一致した。承認済み14ブロックのうち `OperadMonoidalImage` の3ブロックだけを同じ補助で処理すると、共有比較器はPASS・差分0。raw FAIL1件を保存した。0014組の3件と合わせ、rawの分類差は現在2組・4件で、任意の除外を追加していない。

原参照3,858本の検証は完了。新mainで再採取した340本と依存不変を証明した3,518本を区別し、更新対象345候補のうち5本、加えてその候補外の汎用2本を含む監査ソース7本は、元の採取物と実際の元コンテキストを保持した（`main3a-source-context-revalidation.json`・`main3a-generic-audit-reuse.json`）。残っていた監査ソース6本も実採取が成功した。この参照採取を正式な全監査の実行結果とは数えない。

## 13. IC-1完成結果（2026-11-18夜）

|検査|実結果|外部証拠（preparation/以下）|
|---|---|---|
|原参照・openの束縛|3,858本完了。新main再採取340本と依存不変3,518本を区別|reference-native-progress.json、main3a-source-context-revalidation.json|
|他枝の影響|枝1ファイル＋新main文書4ファイル＝保守的に5、上限30以内|branch-impact-native.json、branch-impact-metadata.json、main-blueprint-impact.json|
|静的import・衝突|全34,880モジュール・145,519辺の厳密な移送、循環0、全書込SHA・旧パス削除一致|applied-static-receipt.json|
|層|同条件581→581、違反の移送差分0。上流未登録395本は正式分類していない|main-blueprint-static-rebase.json、main3a-unregistered-tier-independence.json|
|通常対象ビルド|数学4,314本＋追従blueprint4章が成功|target-build/complete.json、main-blueprint-targets/complete.json|
|native名・所有元|global41,197件、定義元別41,490件が欠落・余分0。併合293証明の直接依存と宇宙束縛数も差分0|preservation/owner-pairing-summary.json、preservation/module-owned-pairing-summary.json、coalesced-proof-dependencies/comparison.json|
|保存比較v3b|全4,314本PASS、未説明0。承認済み補助は§12。raw分類差2組・4件は保持|v3b/progress.json、各組comparison.json・receipt、補助手順の組comparison.raw.json|
|引用・タグ|118→118件、追加0、欠落0、余分0。件数だけでなく各欄・重複数も一致|citation-comparison.json、citations-before-main3a/、citations-after/|
|通常root|`lake build SerrePositivity` 終了コード0、約127.22秒（34,559 jobs）|root-after/complete.json、root-after-slot-1794996930097218000.log|
|最終照合|検査記録・実ソースSHA・全移動の比較範囲包含・不変対象を照合してPASS|final-stop-point.json、final_verify_ic1.py|

全体rootの成功と、個々のファイルがroot閉包に入ることは区別する。root外の対象も通常対象ビルドとv3bに含め、B4のroot閉包を揃える適用はしていない。Archive・略号表・共有採取器/比較器・共有鍵の独自変更0。BS draftは「移動の前から 19 エラー、追従は文字の置き換えのみ」。

### 13.1 移動単位の結果とB4用の改名表

次の全単位の全モジュールが4,314本の保存比較範囲に含まれることを照合した。引用・rootは上表の共通検査結果で、単位別にrootを繰り返したものではない。

|単位ID|移動本数|nativeエントリ（private）|対象build・v3b|取り下げ|
|---|---:|---:|---|---:|
|IC1-AlexanderWhitney|28|449（145）|PASS・未説明0|0|
|IC1-BergerFresse|3|31（0）|PASS・未説明0|0|
|IC1-ComplexLimits|382|1766（184）|PASS・未説明0|0|
|IC1-CosimplicialNormalization|9|82（11）|PASS・未説明0|0|
|IC1-DGAlgebra|26|480（13）|PASS・未説明0|0|
|IC1-FrameRealizationLifting.lean|1|3（0）|PASS・未説明0|0|
|IC1-Hammock|354|2323（139）|PASS・未説明0|0|
|IC1-HomBiprodRestriction.lean|1|7（1）|PASS・未説明0|0|
|IC1-HomHomotopy.lean|1|18（7）|PASS・未説明0|0|
|IC1-HomRestriction.lean|1|2（0）|PASS・未説明0|0|
|IC1-HomologyZero|16|175（2）|PASS・未説明0|0|
|IC1-IntervalCuts|205|2175（571）|PASS・未説明0|0|
|IC1-NatTensor|5|117（22）|PASS・未説明0|0|
|IC1-NativeBinaryCoconeHom.lean|1|10（0）|PASS・未説明0|0|
|IC1-NegativeTensor|14|201（68）|PASS・未説明0|0|
|IC1-Operad|327|3604（747）|PASS・未説明0|0|
|IC1-OppositeFactorization.lean|1|10（0）|PASS・未説明0|0|
|IC1-ProjectiveCofibrantUnit.lean|1|5（1）|PASS・未説明0|0|
|IC1-ProjectiveCofibration.lean|1|1（0）|PASS・未説明0|0|
|IC1-ProjectiveHomotopyInverse.lean|1|10（3）|PASS・未説明0|0|
|IC1-ProjectiveModel.lean|1|34（7）|PASS・未説明0|0|
|IC1-Shuffle|45|433（172）|PASS・未説明0|0|
|IC1-SimplexCuts|426|3015（1073）|PASS・未説明0|0|
|IC1-StrictAdjunctionBar.lean|1|41（3）|PASS・未説明0|0|
|IC1-Surjection|202|1687（515）|PASS・未説明0|0|
|IC1-TableReduction|211|1793（651）|PASS・未説明0|0|

正式な旧→新パス・旧→新名・元/新kernel名・所有元・private・kindの一覧は外部 `preparation/b4-actual/declaration-name-map.csv`（18,472行、private4,335行）。26単位の集計は同 `summary.json`、全体41,490件の実対応は `preservation/actual-module-owned-pairs.json`。ソースだけの段0表 `research/infinity-consolidation-w1/source-name-hints.csv` を正式宣言表として使わない。

移動2,264本のうち3本（ComplexLimitsのExtendTruncationHom・ExtendTruncationHomNaturality・TruncationInclusionNaturality）は集約だけで所有宣言0件。宣言表の2,261定義元と混同せず、実native表で両側とも0件、全3本も通常ビルド・v3b対象に含まれることを確認した。最終照合の補助の初回には全ファイルに宣言行があると誤って要求したため失敗し、その誤った補助だけを修正して再照合した。正式検査の結果・native表・Leanソースは変更していない。

### 13.2 証拠と停止範囲

証拠の実体は `~/serre-evidence/ic-w1/ic-1/`。gitには [目録](../../../evidence/ic-w1/ic-1/manifest.json) だけを更新する。目録の `commit` はソースコミット `78dcc2c5263d80b2eb7f710c990f43f35289debe`。このコミットが移動・追従の本体で、報告と目録はその後の文書コミットに収める。適用・採取・限定修復・自動レビュー拒否と明示承認・鍵外で完了した旧採取と規則適合の再観測を履歴として保持する。

取り下げ・範囲追加0。BR55不明356件は据置。B1/B4の適用は別amendmentで、最初はB1が4本・400行、B4が1節・50本。正式な全監査・verify・mainへの取り込みは調整役。IC-2以降には進まず、完了報告と目録のコミットで停止する。

stage後の全差分の書式検査では、Hammock/FreeFirstColumn{Backward,Mixed,Reverse}HomWeakの30・41行、計6行の行末空白が検出された。新しい完全修飾名を元の短名へ戻すと、移動前mainの同じ行と改行・空白まで一致することを確認した（`post-stage-format-check.json`）。既存空白6件を保持し、新規0件。検査後のLean編集はしていない。CSVの既存CRLFも件数を保持した。


## IC-2 の段 0

作業木は `/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-ic`。作業枝 `refactor/infinity-consolidation` に `git merge main` で `1522321e5` を取り込み、そのソースから調べた。§13の指示に従い、作業はソースの静的調査とこの報告・表まで。Leanの編集・起動、ビルド、鍵の取得は0。§3の条件付き事前承認は使わず、IC-3・IC-4には進まない。

### 範囲と分類の照合

| 対象 | 旧表の一般∞候補 | 現行に存在 | 移動案 |
| --- | ---: | ---: | ---: |
| KST | 1,641 | 1,641 | 1,554 |
| HomotopicalAlgebra | 84 | 84 | 71 |
| Spectra（最上位） | 0 | 0 | 0 |
| 計 | 1,725 | 1,725 | 1,625 |

現存の1,725本は135,433行。KST内の `KST/Spectra/` はKST行に含む。三つの対象域に旧表以降増えた210パスは全てOE-W1またはIC-1の移動先と一致し、候補に加えていない。OE表で旧・新パスが同じ `DiagonalLeftAnodyne` は移動済みとは数えない。旧表の基準 `8c75c2ee8` から候補内で変わった5本は、既移動先への import・参照追従と `open` の修飾に限定され、行数は全1,725本で旧表と一致した。[既移動パス](../../../research/infinity-consolidation-w2/excluded-previous-moves.csv)

分類の所見は全100本を別表に記録した。通常圏・ホモトピー論の14本（Reedy図式、生成持上げ類、通常のČech複体など）、模型境界の25本（例：Ωスペクトルに固定した局所instanceやデータ）、S構成との混在56本（多重Sのcofinality 24本と、指定した単調K経路・合成などを型や宣言名で参照する32本）、再公開のみの互換入口5本。模型とS構成の欄は現段階の留保で、IC-3・IC-4の行先を決めていない。型の抜粋、局所instance、importを確認したが、別モジュールの略号を展開した分類やnative照合は適用の判断前に行う。一般部分と専用部をまたぐものはファイル全体を据え置く。[分類差の全件](../../../research/infinity-consolidation-w2/classification-differences.csv)

### 残す根と到達結果

tracked非ArchiveのLeanヘッダ34,883本・145,428辺から、明示 import をファイル単位でたどった。外部パッケージの辺は保持し、作業木外へはたどらない。Versoの本文を読まずヘッダだけを解析し、各ヘッダのimport集合を既存の静的読取器とも照合した。

| 条件 | 根 | 候補への到達 |
| --- | --- | ---: |
| (a) 主定理・root・各入口 | `SerrePositivity.lean`、`Entrypoints/` の54本、sorry監査の主定理と許容入力の4定義元、合計59本 | 1,465 |
| (b) 文献の対応表 | `research/*-coverage/review/` の対象CSVで own 709行・partial 1,356行・interface 25行から得た本体の1,341定義元。旧パスはOE-W1・IC-1表で照合。未解決の本体パス0 | 223 |
| (c) 動いている枝 | ③-a `math/inf-supply` のmainとの共通祖先からのLean差分75本と未追跡4本。作業木のimportから、当該枝と現行mainのグラフをたどった。⑥・③-bの現行refと作業木はなく、最終取り込みはmainで確認した | 24 |
| 三条件の和集合 | 同じファイルは1回 | 1,467 |
| 三条件のどれからも届かない | 22,623行 | 258 |

(a) の監査対象は `main_statement`、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`、`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` の定義元を根にした。root単独は1,464本。sorryの宣言依存はファイルのimport閉包で上から抑え、カーネルの定数閉包は計測していない。(b) はレビューの `status_new`・`declarations_new` があればそちらを優先し、Mathlibへの参照は本体の根から外した。(c) は枝固有の作業から評価し、共通祖先から無変更の全ファイルを一律の根にしていない。参照ファイル・監査の一覧と各候補への経路を保存した。[根一覧](../../../research/infinity-consolidation-w2/roots.json)・[全候補と経路](../../../research/infinity-consolidation-w2/inventory.csv)

258本は、正式監査108本・blueprint・設計draftの閉包と、その他のtracked Leanからの直接importも別に照合した。正式監査から253本・22,503行に届く。内訳は移動案224本・19,978行と、分類留保29本・2,525行。いずれも保持する。残る5本は24行ずつの互換入口。 `WordSegmentComparison` は非正式の `scripts/check_word_segment.lean` が使うため据置。 `SmallKanHomotopy`、`SmallTargetKernelQuotient`、`StarDiagramSmallQuotient`、`WeightedWordHom` は現行の非Archiveソースに直接import元がなく、再公開先に本体がある。旧パスの互換終了を承認する場合だけ Archive の候補とする。既存の互換台帳に旧名が残っているので、適用の判断時にそれと外部利用も確認する。削除の推奨は0本。[未到達と扱い](../../../research/infinity-consolidation-w2/unreached.csv)

### 移動・改名と置き場所

移動案1,625本・127,822行を28単位にまとめた。旧→新モジュールとimportを置き換え、既存公開宣言の名前空間は保つ案。明示名の静的候補7,194行の旧名→新名は同じ。private・生成宣言・モジュール名の値としての参照は後続でnative照合する。5つの配置先の同名衝突は、章の下で旧主題ごとに分ける案で回避した。名寄せ・統合はB1で別に判断する。[移動・改名表](../../../research/infinity-consolidation-w2/moves.csv)・[ソースの宣言名候補](../../../research/infinity-consolidation-w2/source-names.csv)

レビューに明示宣言がある配置は35本。Kerodonの節を優先し、HA 1.1は零対象・余ファイバー、安定部分圏、完全関手で分ける。ほかは主題の節（例：Kanのπ群はKerodon 3.2、単体的圏とcoherent nerveは2.4、BK図式は7.5）に置く。レビューの宣言番号を持たない補助は、旧表にある主題番号を参照して利用側の構成と同じ節の下に置く案であり、その番号への文献属性を追加する意味ではない。複数節で使われ、前の節から後の節への逆向き依存が生じるものは、共通基盤に独立させられるかを別確認する。置き場所の更新は17本（同じHA 1.1内の下位分類や同名回避は別）。例として `PointTerminalAdjunction` はレビューのKerodon 6.2.1.21を優先した。[全件の章節と根拠](../../../research/infinity-consolidation-w2/placement.csv)

### 層・他枝の影響と適用費用

- 全移動案はimportグラフの辺数を保ち、循環0。既存KL-W1検査を同じ診断条件で前後に掛けると543→880件。追加337件はすべてKerodonの逆向き節依存で、移動側→既存236辺、移動側→移動側101辺。例えば6.2の `AdjointLocalizationFactor` は6.3の `AdjointLocalization` を読む。旧実装境界・tier・既存例外を移送し、新たな例外は提案していない。上流未登録の395本には両側で一時的にConsumersを当て、移動端に接する辺0を確認した。既存543件の解消を意味しない。
- 逆向き辺の起点235本を元の位置に保留する **1,390本の静的代替案** も検査した。既存違反543件は前後で厳密に対応し、追加・消滅0。235本は、前節が要る補助を切り分ける、依存を持つ補助を後方の利用節に置く、あるいは保留する、の順に検討する。旧W1の禁止判定差0、W2a/W2bでは各1,566本がKST等の旧パスによる禁止判定から外れるが、その変更を受ける旧core閉包は0。旧層の直接規則差も0。この代替案は層の差分だけを確認したもの。実適用の承認にはならない。[層の差分](../../../research/infinity-consolidation-w2/layer-preview.json)・[235本の保留表](../../../research/infinity-consolidation-w2/layer-holds.csv)
- 1,625本案でmainの範囲外直接import元は1,105ファイル・2,763 import。本体1,090、blueprint12、scripts2、設計draft1。draftを外すと1,104ファイル。③-aの枝固有79本のうち直接追従は0本・0 import、移動案への推移的依存は74本。移動対象自体に③-aの編集はない。適用後に共有依存を更新し、その74本の再検査が要る。⑥は `72bc75e8b`、③-bは `49967c102` の最終取り込みを確認。現行の別枝の追従を0と記録し、両レーンの本体利用はmain側で既に数えている。⑧とBR54の観測済み枝もmainからのLean作業差分0。取り込み・リポジトリ移動後に再採取する。[mainの追従表](../../../research/infinity-consolidation-w2/import-followups.csv)・[枝と経路](../../../research/infinity-consolidation-w2/branch-impact.json)
- 1,625本案の逆閉包はtrackedソース15,634本で、ライブラリ15,211本、うちroot閉包内12,378本。正式監査108本中62本が依存する。これは再検査対象の規模で、実際のLake再ビルド本数の測定値ではない。指示書§13が示すIC-1取り込み検証の実測約6時間に対し、IC-2は移動本数が小さくても逆閉包が広い。待ち時間を除き、事前のnative参照・衝突採取3〜7時間、追従・静的適用2〜5時間、対象build6〜14時間、v3bと引用の前後比較5〜10時間、調整役のroot・全監査・verify5〜8時間で **合計21〜44時間** を暫定目安とする。層の保留235本の再設計・B1・キャッシュ冷却や他枝の取り込み待ちは別。1,390本案でも逆閉包の再計算を要する。[集計](../../../research/infinity-consolidation-w2/summary.json)

### B1 該当分と停止点

移動案のうち80行以下で同じ配置単位には直接import元がない小ファイルは437本・24,450行。全グラフで直接import元が0の該当ファイルは0本で、統合時には外部の利用側も追従する。試しの候補はKerodon 7.5の `FrameBousfieldKanReindexingComposition`（71行）と `FrameBousfieldKanReindexingFrames`（46行）。同じ名前空間・共通の添字変更定義・同じ2つの直接利用元を持つため、単位・合成則とframe族の自然性を1つの章内ファイルにまとめる候補になる。初回は4本・400行以内。別のamendmentで import を和にする影響、open・変数・局所属性、private・生成宣言を確認し、保存比較v3bで崩れた群は取り下げる。[B1の候補と利用元](../../../research/infinity-consolidation-w2/b1-leaves.csv)

一覧は調査 **済み1,725／全体1,725（うち旧表外の追加0）**、移動案 **28単位・1,625本**、適用 **0／全体28単位**。ここで段0の報告として停止する。Archive候補の扱い、層の配置、適用時期を決めるのはユーザー・調整役。[調査資料と再集計手順](../../../research/infinity-consolidation-w2/README.md)


## IC-2 適用 第1組

ユーザーの明示承認で現在の作業木を使用し、main `e6b608c4f` を merge `6680433e4` で取り込んだ。採用済みの1,390本案から、統合直後に逆閉包の小さい4単位を選んだ。第1組の逆閉包は合計214ソースで、うちライブラリ205本を対象とした。別枝の現行作業の本体差分および対象パスへの参照は0件。

| 単位ID | 移動本数 | 単位の逆閉包 | 結果 |
| --- | ---: | ---: | --- |
| `IC2-HA-Section4_1_2` | 1 | 10 | 完了 |
| `IC2-Kerodon-LimitsAndColimits-Cofinality` | 1 | 15 | 完了 |
| `IC2-Kerodon-TheHomotopyTheoryOfInfinityCategories-LeftAndRightFibrations` | 1 | 137 | 完了 |
| `IC2-Kerodon-FibrationsOfInfinityCategories-CartesianFibrations` | 4 | 166 | 完了 |

**一覧：済み4／全体28（うち追加0）**。28単位のうち3単位は全本数が235本の保留に含まれる。移動を伴う25単位のうち4単位、全1,390本のうち7本を適用した。第1組の取り下げ0件。互換入口4本は配置監査が旧パスの存在を求めているため据え置き。削除0。

| 検査 | 結果 |
| --- | --- |
| 静的 import・衝突 | 34,958モジュール・145,841辺の移送と実ソースが一致。循環・衝突0 |
| 層 | 同じ診断条件で548→548件。違反の追加・消滅0。一時的な未登録層の補完は検査時だけ使用 |
| 通常の対象ビルド | 移動前後とも205本を対象に終了コード0。依存先込みで移動前約7.0分、移動後約15.3分 |
| v3b | 64・64・64・13本の4組すべてPASS、未説明差分0。native採取は前後合わせて約24.4分。宣言は7,438→7,438件、うちprivateは355→355件 |
| 引用・タグ | 3→3件、欠落0・余分0。宣言名・所有モジュール・文献番号・関係・版・注記を、重複込みで照合 |

移動前の引用採取は初回のみ旧入口で失敗した。現行の `CitationRegistry` を明示して再試行し、前後とも成功。初回のログを保存した。比較器や本体の型・証明は、修復のための変更を加えていない。移動・追従で23パスを書き、旧7パスを除いた。追従には既存の監査スクリプト2本のモジュール名と対応表のパスを含む。root・正式全監査・sorry閉包は調整役の取り込み時に確認する。

[証拠目録](../../../evidence/ic-w1/ic-2-g01/manifest.json) の `commit` は移動前の基準 `6680433e40f564070d7a49740abaa8c3dc5dd5f4`。移動後のファイルSHAと全比較の結果は目録中の `final-result.json` に記録した。第1組のコミットで停止し、調整役の取り込みと連絡を待つ。
