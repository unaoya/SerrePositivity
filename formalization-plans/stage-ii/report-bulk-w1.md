# 一括レーン B1：文献属性と配置の設計（停止点0）

2026-11-12。指示書は [citation-attributes.md §1〜§7](citation-attributes.md)。本報告は**承認前の案**であり、属性・移動・削除は実施していない。Lean・既存の道具・対応表は変更せず、ビルド・採取・共有鍵の取得も行っていない。

基準は main **`e61b3f534d9bd2b8e9483d5f13d5eb9aa97bf9ab`**。最新の対応表、module docstring、コメントを除いた import 行を静的に調べた。`public import`・通常の import・`import all` を依存として扱う。import 到達性は宣言の実使用や型の正しさを証明しない。対応表の行数・候補数も、属性の付与済み件数ではない。

## 0. 停止点0で決める案

1. 非Tag文献は `@[cite KEY "番号"]` と、四種の partial を表す追加構文を採る。原典・版・番号・partial・宣言所有元を別々に記録する。187件の未解決を黙って省かず、後述の保留台帳を付与計画と一緒に管理する。
2. `Project` の文献に対応する51ファイルのうち、HTT・HAによる41本を文献の節へ、K系の10本を当面 `Project` の話題別の場所へ置く（付表A）。Kerodonについて、今回の機械的な突合せから追加のProject移動を確定できる候補は0本。未確定のpartialから行き先を推定しない。
3. `DerivedCategories` の直下2,322本を七つの話題へ分ける。③-bの **`Project/DerivedCategories/DiagramComparison/` は維持**する。ここを今後のstrict図式とD(A)の比較の置き場所にしてよい、という承認を最初に求める。
4. BSは論文全体に沿って既存の大分類を保ち、`Prismatic` をSite・Envelopes・CechAlexander・Crystalline・HodgeTateに分ける。Construction 6.1、Example 7.9、§10の越境群も同じ一晩に整理する。
5. ModelCategory SSetを仮定するKST降下54本はArchiveへ。ただし現役からArchiveへの依存を残さないため、逆向きの閉包で追加される13本も同時に扱う案を採る。ScalarTensorViewはCommutativeAlgebraへ移し、外部利用の旧名を互換名として残す。Diagnosticsの4本は削除せずArchiveに保存する。

以下では、対応表に直接根拠がある候補と、補助ファイルの主題による分類案を分ける。B2で宣言の型・所属・分割境界・完全なファイル割り当て表を確定し、B3の凍結の一晩に実行する。

## 1. 文献属性の設計

### 1.1 Mathlibを手本にする範囲

指定された `.lake/packages/mathlib/Mathlib/Tactic/StacksAttribute.lean` は、現行版では `Mathlib.Tactic.CrossRefAttribute` をpublic importする非推奨の入口だった。実装の手本は **`CrossRefAttribute.lean` の `Tag`・`tagExt`・`addCrossRefDoc`・`registerBuiltinAttribute`・`traceCrossRefs`** とする。Tagを永続環境拡張に記録し、docstringに引用を追加し、`applicationTime := .beforeElaboration` で非同期elaboration開始前にdocstringを処理している。

Mathlibの `Database` は閉じた列挙型なので、HTT等をその型へ追加するためにMathlibを改変しない。プロジェクト側の独立した永続環境拡張を `SerrePositivity/Util/Citation.lean`（新設案）に置く。型理論や数学の層から独立したmetaの道具とし、既存の `@[kerodon]`・`@[stacks]` はMathlibの実装を使い続ける。

### 1.2 構文と意味

| 用途 | 構文案 | 意味 |
| --- | --- | --- |
| 一致する定義・結果 | `@[cite HTT "5.5.2.9"]` | 指定版の指定項目との完全対応。自動推論でpartialを完全対応へ格上げしない |
| 特別な場合 | `@[cite HA "1.3.5.8" (partial := special) "可換環上のD(A)の場合"]` | 原文の対象・圏・次元等を特殊化 |
| 一方向 | `@[cite KEY "番号" (partial := direction) "(2)から(1)のみ"]` | iffや同値の片側 |
| 強い仮定 | `@[cite KEY "番号" (partial := stronger-hyp) "filteredを仮定"]` | 原文より強い仮定の下での結論 |
| 成分だけ | `@[cite BS19 "Prop 7.10" (partial := component) "有限包絡の構成部分"]` | 結論・構成の一部が宣言から直接得られる |

`partial` の値はこの四つだけとし、partialの理由は必須の文字列にする。一つの主たる種類と具体的な不足を記録し、複数の不足があるときは理由にも書く。単なる関連補題・比較射の存在だけではpartialにしない（Kerodon確認§8.1の基準）。同じ宣言に複数の引用を付けてよい。同じ文献番号に複数の宣言が対応してもよい。

保存する一件は `(KEY, number, declaration, relation, comment)`。`relation` は `exact` または四種のpartialで、declNameは名前解決後の完全名にする。文献KEYはLeanの定数名の解決と独立した登録済み識別子。番号は文字列とし、見出し種別も含めて正規化する（HTT・HAは `5.5.2.9`、BSは `Prop 7.10` 等）。対応表の `kind` から既知の短縮形へ変換し、元の表記とrow IDは付与計画に残す。`§3.1 | 3.4（∞版）` のようなまとめを一つの項目番号として登録しない。個別番号へ分け、説明をcommentへ移す。

属性はglobalでのみ使う。未知のKEY、空番号、未定義のpartial種別、同一KEY・番号・宣言で矛盾するrelationはエラーにする。完全に同じ一件の重複は出力で重複させず、再実行でdocstringにも同じ引用を増殖させない。明示属性と後置の `attribute [cite …] 完全名` の双方を使える設計にし、後者では生成メンバーの実在と所有元も検査する。属性自体は数学的対応の証明ではなく、照合済みの結果を記録する仕組みである。

Kerodon・Stacksの完全対応は従来どおり `@[kerodon TAG]`・`@[stacks TAG]`。partialにもネイティブ属性を使う場合の案は、既存のoptional commentに **`"partial:special; 理由"`** 等の予約接頭辞を置き、照会・地図では必ずpartialとして表示する方式。MathlibのTag構文は変更しない。ただしKerodonのpartial831行は全章一括見直しが別途残っているため、**B3で無審査に追加しない**。まず既存のown・bothの672組を維持する。partialへのTag追加を行う段階では、照合・監査の側もfullとpartialを別集計する。この予約形式を採るか、partialは対応表だけに保持するかを停止点0で決める。

### 1.3 記録・照会・略号表

- `#cite_tags KEY`：番号、relation、完全宣言名、所有モジュール、ソースパス、宣言範囲の開始行、理由を表示する。`#cite_tags! KEY` は型も表示する。順序は正規化番号・完全宣言名で固定する。
- HTT等は独自拡張、Kerodon・StacksはMathlib拡張から読み、同じ出力形にする。docstringを逆解析して地図を作らない。importされたモジュールも含め、同じ宣言を集約入口の数だけ重複させない。
- 所有モジュールは `Environment.getModuleIdxFor?` とheader、行は `findDeclarationRanges?` で引く。範囲が得られない生成宣言は `line = null` と理由を出す。古いCSVの行を現在の行として補わない。定義元がMathlibなら、プロジェクトのファイルへ属性を挿入しない。
- 機械出力は将来のexport道具から同じスキーマのJSON/CSVへ。地図には元の表のstatement・不足理由・goal・routeも結合する。属性がないnoneの項目も索引から消さず、全項目の目次は別に保持する。
- 略号と版の正本は **`research/bibliography.json`（新設案）**。KEY、著者・表題、版、番号規則、ローカルPDFまたは原典の場所を置く。実行時のKEY一覧はここから生成し、READMEの **Conventions / References** は同じ正本から出す。版を属性ごとに繰り返さず、異なる版を同じKEYで混在させない。

| KEY | 文献・指定版 | 版の根拠 |
| --- | --- | --- |
| BS19 | Bhatt–Scholze, Prisms and prismatic cohomology、著者版 | `paper/refs/BS-prisms-author.pdf`、指示書§3 |
| BS17 | Projectivity of the Witt vector affine Grassmannian、arXiv:1507.06490 | 指示書§3（v番号はB2で所蔵版と照合） |
| HTT | Higher Topos Theory、2017-04-09 | 指示書§3 |
| HA | Higher Algebra、2017-09-18 | 指示書§3 |
| Kerodon / Stacks | Tag | Mathlibネイティブ属性 |
| LT | On the K-theory of pullbacks、arXiv:1808.05559v3 | `research/k-coverage/maps/land-tamme/toc.md` |
| KST | Algebraic K-theory and descent for blow-ups、arXiv:1611.08466v4 | 同 `kst/toc.md` |
| BGT | A universal characterization of higher algebraic K-theory、arXiv:1001.2282v4 | 同 `bgt/toc.md` |
| TT | Thomason–Trobaugh、1990刊行版、Grothendieck Festschrift III | 同 `others.csv` |
| BST13 | Bhatt–Schnell–Scholze、arXiv:1307.3763 | 指示書§3（v番号はB2で確認） |
| Rydh | Submersions and effective descent、arXiv:0710.2488 | 指示書§3（同上） |

今回のK地図には上の12略号だけでは足りない。`Tamme`（1703.03331v3）、`Paper`（`maps/paper/toc.md` の指定PDF・上流コミット）、`Drinfeld`、`KL`（Kuznetsov–Lunts）、`AGH`（地図の「9人論文」）、`BalmerSchlichting`、`Waldhausen`、`Thomason` 等を登録候補に足す。版は `maps/others.csv` のedition/source_urlを引き継ぐ。BSのArc群が引用する `BM18` も必要だが、今回のBS19表から番号・版を推定して付けない。所蔵資料と既存設計で版を固定してから登録する。未登録の文献を無名のKEYや別文献の番号へ押し込まない。

### 1.4 対応表からの付与手順と規模

HTT・HAは `items.csv` の旧い集計ではなく、**完了した `review/ch*.csv` を判定の正本**にする。Kerodonは全章再確認後のitemsとreviewを番号で突合せ、partialの未確定状態を保持する。BSは `research/bs-coverage/items.csv` の現行statusを使う。Kは五文献の `maps/*/items.csv` と `maps/others.csv` の計688行を使い、旧 `research/k-coverage/items.csv` 208行はcrosswalkとして参照し、二重付与しない。

| 入力 | 現行の判定 | 本体への候補参照数／異なるファイル数 |
| --- | --- | ---: |
| HTTレビュー1,730行 | own192、partial291、mathlib50、none1,197 | 846 / 417 |
| HAレビュー2,866行 | own38、partial465、mathlib39、none2,324 | 481 / 254 |
| BS19表211行 | proved34、proved_special42、parts_in_body14、e3_input7、drafts12、design_only4、none98 | 241 / 109 |
| KST・LT・Tamme・BGT・Paper | own・partialを候補、interfaceは自動付与しない | 88 / 40、65 / 37、46 / 26、37 / 28、29 / 11 |

表の右欄は `名前 @ SerrePositivity/…:行` を抽出・KL改名表で正規化した延べの宣言対応数で、検証完了数ではない。補助文献も含む重複除去後は **1,860対応・868ファイル**（うちStacksネイティブ1対応）。BSのdraftsのパスは含めていない。Kerodonの既存672組はこの1,860対応には加算していない。

B2以降の処理は次の順にする。

1. 表の版・ハッシュ・行IDを固定し、`KEY, number, status, partial_kind, name, path, reason` の付与計画を作る。区切りの `|`、`/`、一つの場所に並ぶ複数名、名前の後の説明を分解し、曖昧なら保留する。
2. KLの宣言所有元付き改名表で完全名とモジュールを正規化し、**元のimport環境のLeanで**定数・型・生成メンバー・非推奨alias・宣言範囲を確認する。namespace文字列やファイル名から定数名を合成しない。collectのLake設定を引き継ぐ。今回のB1では実行していない。
3. own/ provedは照合済みの完全対応、partial/ proved_specialは四種を必須にする。BSのparts_in_bodyはcomponent候補だが、型から原文の該当成分を直接得られる宣言だけに付ける。HTT・HAのpartial_kindは全行にある。KST・LTのpartial参照147件にはこの列がないため、理由を読み直して種類を決めるまで保留する。
4. `e3_input`・`drafts`・`design_only`・`interface`・`none`・mathlibは本体への自動付与対象外。sorryや引用公理に依存する「own」候補、満たせない `[ModelCategory SSet]` を持つ宣言も完成した対応に数えない。入力構造の定義は、その定義に原典との対応があるかを別に判断し、入力の主張が証明済みであるかのように属性を付けない。
5. 古いaliasには重複付与せず、原則として現役の定義元へ付ける。文献側へ動かすファイルと属性の挿入を同じ計画で生成し、移動前後のKEY・番号・relation・所有元の集合を照合する。型・本文・既存属性の保存比較と、新設引用によるdocstring差を分けて検査する。
6. B3後、環境から抽出した属性で地図の名前・場所・行を生成し直す。既存の表は付与根拠の履歴として残す。新規ファイルを作るレーンにも属性の規則を配布する。

### 1.5 場所の書き直しで残った187件

`7d8ae8623` とcoordination§3の **3,905件解決・187件未解決** を引き継ぐ。187件を「証明のない187定理」と読み替えない。元の記述・出典行・旧名・場所を保った台帳を作り、解決と「属性を付けない理由」の両方を一件ずつ記録する。今回の静的な正規化で抽出できた本体参照3,985件はすべて既存パスになったが、**これは187件の宣言解決を済ませたという意味ではない**。集計の入力範囲も異なる。

| 未解決の形 | 扱い |
| --- | --- |
| `a / b`、`obj / pre / post`、本文中の説明や記法 | 個別の完全名を実環境で確認。説明はcommentへ。定数でない記法・節見出しはrecord-onlyとして地図に保持 |
| 省略名・相対名・namespaceを宣言として書いたもの | 元モジュールの環境で一意に解決する。一意でなければ保留し、文字列の末尾一致で決めない |
| deprecated alias・移動先が複数の元モジュール | aliasの型・本文と所有元から現役の定義元を選ぶ。namespace/mapの接頭辞だけで判定しない |
| 生成instance・constructor・projection・export | 実在する完全名に後置属性を付けられるか確認。親の定義に自動で付け替えない |
| Mathlibの宣言・非本体・設計だけの参照 | 外部/record-onlyとして保持し、本体への属性挿入から除く。draftsは実行対象にしない |
| 宣言が存在しない、対応が数学的に違う、型に実現不能な仮定 | 未解決または対応表の再判定として残す。似た補題をpartialに格上げして穴埋めしない |

B2の保留台帳は `(元行ID, original, resolved?, action, reason)` を持ち、187件がすべて残っていることを検査する。B3の付与結果は「付与成功＋理由付きrecord-only＋未解決」の保存式で報告する。未解決の個別付与は止め、一覧を提出する。187件全件を解決したと主張したり、無言で母数から落としたりしない。

## 2. InfinityCategories/Projectの13ディレクトリ

現在 **5,794本**。下表の「文献候補」は対応表でown・both・partialを持つ宣言を含む異なるファイル数であり、ファイル全体が原典の項目そのものであるという意味ではない。全51本の根拠と行き先案は付表Aに示す。提案先の51パスは相互に重複せず、現在の別ファイルとも衝突しないことを静的に確認した。HTT・HAの主題が中心でKerodon部分だけがある場合は、KL-W1§9と同様に素直な境界だけ分割し、難しければ主題の側へ置いて個別属性を付ける。無理な分割はしない。

| 現ディレクトリ | 全体／直下 | 文献候補 | 残りの配置案 |
| --- | ---: | ---: | --- |
| Compatibility | 59 / 59 | 0 | 同位置を保持。旧外部名の互換入口として分離。利用0を理由に今回削除しない |
| DerivedCategories | 3,687 / 2,322 | 29 | 下記の七話題＋DiagramComparison。HAによる19本を文献側へ、K系10本を話題側へ（付表A） |
| Entrypoints | 53 / 53 | 0 | 同位置を保持し、各importを新配置へ。集約の宣言所有元をここへ変更しない |
| FibrationAuxiliaries | 268 / 11 | 3 | 既存Categories・FunctorCategories・Pullbacks・Simplicialを保持、CoreFlag・Scaffoldを下位補助として整理 |
| FilteredExchange | 296 / 296 | 3 | `FilteredExchange/{CoconeComparison,FiniteLimits,KanReplacement,GrothendieckConstruction}/`。filtered交換の同じ主定理の部品を近接 |
| HomotopyDiagramComparison | 683 / 675 | 5 | `{KanExtensions,WeightedCones,SpecifiedCocones,SliceTransport,GrothendieckConstruction,Homotopies,CatInfinity,CosimplicialHom}/`。指定錐・端点輸送の多数の補助を主構成の群ごとに分ける |
| KanComplexAuxiliaries | 156 / 156 | 0 | `{Anodyne,Products,Pullbacks,Subdivision,UniverseLift}/`。名前だけでKerodonへ移さず、対応表を追加確認できたものだけ文献へ |
| LocalizationAndKanExtensionAuxiliaries | 179 / 21 | 6 | 既存Roof・Diagrams・Homotopy・FunctorCategories・Quasicategory・NerveComparisonを基本に保持。文献候補だけ外へ |
| ModelCategoryComparison | 140 / 129 | 1 | `{Frames,MappingSpaces,Localizations,Replacements,R72,Inputs}/`。実在する一般モデル圏の仮定とSSet固有の未実現仮定を区別 |
| PointedSpaces | 26 / 26 | 0 | 同位置を保持（必要ならSuspension・LoopSpace）。対応根拠のない単なる小分けはしない |
| QuasicategoryAuxiliaries | 105 / 89 | 4 | 既存Roof・Quasicategory＋`{MappingSpaces,SliceComparison,VertexTransport}/`。零対象の群はHAへ |
| SetWeightedTensors | 32 / 32 | 0 | 同位置を保持。集合で重み付けしたtensorの補助であることをREADMEに明示 |
| SimplicialCombinatorics | 110 / 110 | 0 | `{Chains,FaceDegeneracy,Cubes,Subdivision}/`。Mathlib相当の初等部品は文献の高度な定理と同一視しない |

「文献候補0」は原典との関連がないという判定ではない。現行表の宣言対応から直接拾えた移動候補がないという結果である。新しい対応を名前やdocstringだけでownに増やす作業はこの配置替えと分ける。

### 2.1 DerivedCategoriesの配置

直下2,322本を以下の話題へ入れる。数はB1の網羅性を確認するための**一次仕分け**（ファイル名とmodule docstringを手掛かりにした重複なしの仮置き）で、確定の移動表ではない。先に付表Aの文献候補を取り出すため、最終の話題別本数はこの数より減る。既存の下位ディレクトリは別計数。

| 話題 | 直下からの一次仕分け | 主な対象・細分 |
| --- | ---: | --- |
| MappingAndStability | 1,425 | dg加群・kernel・射の作用・fiber/cofiber・三角・Hom比較。下記のようにさらに分け、1,425本を一つの平らな場所へ集めない |
| LocalizationAndRoofs | 178 | 実roof、分母の精密化、Ore・擬同型の逆転。既存Localization12本をここへ統合する案 |
| Verdier | 177 | dg商、商の錐・roof、Verdier列。既存Verdier131本を維持し、Tammeの二本もその中の話題として保持 |
| Gluing | 5 | 既存Gluing1,073本・Lax28本と同じ話題。K文献の8〜10本だけを別文献ディレクトリへ動かすために巨大な閉包を引き連れない |
| CompactnessAndPresentability | 123 | κ表示・perfect・compact・presentable・Morita・冪等。既存KappaCovers32・KappaPerfect6・Presentable1・PiCriterion35・ClosureFunctoriality34を相互関係が分かる下位に置く |
| Tensor | 109 | tensor・係数制限/拡大・代数・monoidalな比較。既存Tensor1本と整合 |
| KanModels | 305 | nerve、coherent・pinched・span・over単体の模型。既存KanModels2・Quasicategory6と統合する案 |
| DiagramComparison | mainでは0、③-b枝で4本確認 | strict図式とD(A)のnativeな錐の比較。**現パスを保持する** |

一次仕分けの合計は2,322。1425本の大群は少なくとも `MappingAndStability/{DGModules,KernelComparisons,FunctorComparisons,FiberCofiber,Triangles,HomSpaces,Homotopies}/` に分ける。DGModule接頭辞はその中の387本あり、`DGModules/{Bar,Resolutions,Fibers,Actions,Triangles}/` へ。DGKernel接頭辞106本はkernelの作用比較として一群にし、実際にtensorそのものが中心のファイルはTensorへ出す。ホーン・comma構成が中心の補助はKanModelsへ戻す。これらの補助境界はB2でimportの連結した主定理群とdocstringを読み、機械的な接頭辞分類を修正する。

既存Gluing1,073本も平らなまま再生産せず、`{Objects,HomSpaces,StableStructure,ExactSequences,Comparison,Functoriality}/` を候補とする。名前だけで分けず、Objects・CanonicalStableStructure・NativeSemiorthogonal等の主構成の前提群を各下位に置く。

③-bの `math/inf-supply-b`、`328fa2e29` で読み取れた4本は `SemifreePointComparison`・`SmallShapeColimits`・`StrictSemifreeDiagram`・`StrictSemifreeColimitFamily`。いずれもD(A)とstrict半自由図式の比較という同じ束で、module docstringのHTT 4.2.4.1・HA 1.2.4への引用だけを理由に4本全部を文献側へ移さない。一般の∞圏の主張が独立したときはKerodon §7.5等への対応を確認してその部分だけを分離する。4本はmainの5,794本にはまだ含めていない。B3前の取り込みで再集計する。

## 3. BhattScholzeの節ごとの配置

現行 **604本**：Delta56、Prism39、Prismatic320、Semiperfectoid76、Andre57、Perfectoidization38、Almost9、PerfectoidIdeal7、Perfectoid1、Inputs1。節の番号だけをトップレベルの新しい大分類にせず、すでに節と対応する名前は残し、混在している部分に節・話題の下位を作る。

| 場所 | 原典の中心 | 行き先案 |
| --- | --- | --- |
| Delta | §2 | 現在の下位分類を保持。Prismatic/RelativeCompleteRegularityは2.42なので `Delta/CompleteRegularity/` へ |
| Prism | §3 | Basic・Perfectoid等を保持。Example3.4のUniversalOriented/Frobeniusは§3に残す。Construction6.1の群だけ後述の§6へ |
| Prismatic/Site | Cor3.12・Definition4.1 | PrismOver・FlatSite*・FlatCover*・FlatCech*・FiniteCechDescent。サイト・被覆・構造層を一群にする |
| Prismatic/Envelopes | §3のprismatic envelope、§4のČech前提 | Envelope・VariableEnvelope*・CompletedFreeDelta*。実際の主題がδ環そのものの補題はDelta側も候補とし、利用先だけで移さない |
| Prismatic/CechAlexander | §4.3、4.17〜4.19 | Affine/Big/CechAlexanderの枠、包の選択、射、ホモトピー、複体化。`{Frames,Envelopes,Comparison,Complexes}/` に細分 |
| Prismatic/Crystalline | §5、Notation5.1・5.2・5.4等 | CrystallineSiteBasic、CrystallinePDModel・Bridge*、PD/de Rham、FrobeniusCechComparison。`{Site,Envelopes,PDDeRham,Poincare,Comparison}/` へ |
| Prismatic/HodgeTate/Affine | §4.2、4.9〜4.11 | HodgeTate*・Bockstein・Cartierのaffine構成。5.5も含むHodgeTateCartierAssemblyは主題の側に一つだけ置き、5.5の引用も付ける |
| Prismatic/HodgeTate/Comparison | §6、Construction6.1・Theorem6.4 | 結晶被覆、検出・反映、Witt/普遍係数の比較。`{CrystallineCover,Coefficients,Witt,BaseChange}/` に細分 |
| Semiperfectoid | §7 | `Lci/`（Example7.9の19本）・`FiniteEnvelopes/`（7.3・7.10）・`RootFamilies/`・`Cotangent/` 等。lciの補助を§7の外へ動かさない |
| Andre | §7のAndréの経路 | 既存57本の下位分類を保持。δ環の一般部品の所在と§7の主張への引用を分ける |
| Perfectoidization | §8 | `Construction/`・`Arc/`・`Descent/`・`Comparison/`。§10の整代数群を外へ出す |
| Almost・PerfectoidIdeal | §10 | `Almost/`、`PerfectoidIdeal/`は保持。新設 `IntegralPerfectoidization/` に10.9〜10.11の整代数の近似・完備化を置く |
| Perfectoid・Inputs | 基本接口・E3入力 | 所属の意味を明記して保持。Inputs1本はE3を証明済みとして属性付与しない |

Prismatic直下320本の一次仕分けは次のとおり。ここも最終割り当てではなく、対応表の個別根拠とmodule docstringを使ってB2で境界を修正する。特に§5の結晶模型と§6.4で使う同じ模型の係数比較を、prefixだけで分離しない。

| 仮の主題 | 本数 |
| --- | ---: |
| Crystalline | 204 |
| CechAlexander | 39 |
| HodgeTate/Comparison | 37 |
| HodgeTate/Affine | 16 |
| Site | 13 |
| Envelopes | 7 |
| §7へ：FiniteEnvelopeDiagram・RawColimit・Completion | 3 |
| §2へ：RelativeCompleteRegularity | 1 |
| 合計 | 320 |

### 3.1 越境している群の具体案

- **Prism/BasicのConstruction6.1**：`Construction61Frobenius` と `CrystallineCover{,Reduction,Regularity,Factorization,CochainTor,PairTor,CompleteTor}` の8本を `Prismatic/HodgeTate/Comparison/CrystallineCover/` へ。`UniversalOriented`・`UniversalOrientedFrobenius`・`OrientedPrism`・`Rigidity` の4本はExample3.4等の§3に残す。対応表6.1には前者のFrobeniusとCompleteTor、およびPrismaticのDetection/Reflectionが明記されている。
- **Semiperfectoidのlci**：LciEnvelopeから始まる19本を `Semiperfectoid/Lci/` へ。表7.9にはExistence・Initial・Discrete・Conormal・InvertPGeneratorsが明記され、module docstringも全19本でExample7.9を主題としている。3.13の一般envelopeと、7.9のsemiperfectoid lciの場合を混同しない。
- **Prismaticの有限envelope**：`FiniteEnvelopeDiagram`・`FiniteEnvelopeRawColimit`・`FiniteEnvelopeCompletion` はmodule docstringが7.10・7.3。`Semiperfectoid/FiniteEnvelopes/` へ移す。Prismaticという元の名前に引きずられない。
- **Perfectoidization/Derivedの§10**：`IntegralApproximation`・`IntegralClosureApproximation`・`PerfectoidFilteredColimit`・`IntegralClosureCompletion`・`IntegralExistence`・`FiniteEtalePerfectoid` の6本は `IntegralPerfectoidization/{Approximation,Completion,Existence,FiniteEtale}/` へ。表10.9・10.11の根拠がある前4本と、後2本のmodule docstringを区別して記録する。IntegralClosureCompletionはCor8.12の入力も使うが主題は10.9/10.11なのでファイルは一つに保つ。
- 同Derived内のArcSite・ArcValuation*・ArcPerfect*・ArcCech*・ArcMilnor*・ArcIntervalOverlap・ArcCardinality等は `Perfectoidization/Arc/{Site,Valuations,Milnor,Descent}/` へ。BS8.7〜8.12、BS17、BM18の複数の引用を属性で表し、すべてをBS19 §10へ移さない。`RootAdjunction` は§8の構成、`Interface`・`Excision` はE3を受ける界面/比較として§8側に保持する。これらは§10の定理が証明済みであることを意味しない。

対応表だけで具体的な移動根拠を得た例：3.12のFlatSite/FlatCech4本、4.1のPrismOver等3本、4.17のCechAlexander等5本、4.18のBigCech2本、4.19のAffine2本、5.1のCrystallineSiteBasic、5.2のCrystallineBridge・BridgePushout・PDModel、5.4のFrobeniusCechComparison、6.4のUniversalWittComparison・WittCrystallinePrism。これは「全320本の型を今回照合した」という主張ではない。

## 4. 片付け

### 4.1 ModelCategory SSetの54本

対象の54本は **KST/Descent** の補助降下（[k-restart-draft.md §2・§5](../k-restart-draft.md) の決定）。InfinityCategories内の一般モデル圏の全ファイルや、文字列検索で出る全リポジトリのファイルを54本と呼ばない。コメントを除いて `[ModelCategory SSet…]` を書くKST/Descentの54本が実際に一致した（付表B）。静的なroot import閉包には54本とも入っていない。

54本だけをArchiveへ移すと、次の現役ファイルがそれらをimportする。逆向きに末端まで閉じると **67本＝54＋12の補助＋Auxiliary集約1** となった。67本ともrootからは到達しないことをB2でも再確認する。提案先は `SerrePositivity/Archive/KST/DescentConditional/`。現役側にはArchiveへpublic importする互換入口を残さず、Auxiliaryとその監査はArchive専用として管理する。宣言名はまず保持し、主経路の定義を巻き込む一括namespace改名はしない。

追加13本：`Auxiliary`、`CechBaseChangeSpaces`、`CechFibrantDiagrams`、`CechReindexAugmentation`、`CechWeightAugmentationFubini`、`DisjointFamilyCechGeometry`、`FamilyCechDiagonalComparison`、`FamilyCechFunctorComparison`、`FamilyCechPresheafComparison`、`FiniteFamilyCech`、`FiniteFamilyCechFunctor`、`MixedCechSpaceSwap`、`SplitCechExtension`（いずれも `KST/Descent/`）。54本以外を勝手に削除する案ではなく、現役→Archiveの辺を防ぐための追加移動の承認事項である。

`scripts/audit_kst_descent.lean` はAuxiliaryをimportするため、正式監査から外し、Archive用の明示的検査に移す案。`audit_kst_descent_main.lean` は主経路を守る監査なので**維持**し、旧56モジュールの禁止表を新旧の補助67本の意味に合わせて更新する。補助を正式監査から外したことで監査対象の消失が隠れないよう、監査台帳・verify側の対象差を報告する。K地図の補助に対する参照もArchiveと満たせない仮定を明記して保持し、完全対応の属性へ取り込まない。

### 4.2 ScalarTensorView

`KST/DerivedBlowup/ScalarTensorView.lean` → **`CommutativeAlgebra/Module/ScalarTensorView.lean`** を提案。内容はModuleCatの係数拡大/制限と通常のtensorの表示比較で、importはMathlibのChangeOfRingsとTensorProduct.Towerだけ。`SerrePositivity.KST.DerivedBlowup` から `SerrePositivity.CommutativeAlgebra` の宣言名へ改める案とする。

直接の利用側は `BhattScholze/Delta/DividedPower/RegularSequencePDUniversalTor.lean` と `KST/DerivedBlowup/PolynomialPushoutBaseChange.lean` の2本。利用側のimportと定数参照を所有元付きの採取で変更し、旧外部利用名にはdeprecated aliasを残す。旧モジュールは新モジュールだけをimportする互換入口にする。BS主定理の閉包がこのMathlibだけの一般部品のためにKSTの実体へ届かないことを確認する（互換入口を本体利用側のimport先には残さない）。規模は実体1本＋互換入口＋利用側2本。

### 4.3 利用者のない試作と互換入口

`Project/DerivedCategories/Diagnostics/` の4本は、現役SerrePositivity内の直接import利用者が各0、rootからの到達も0だった。C2のREADMEも試作保存用と明記している。提案先は **`SerrePositivity/Archive/InfinityCategories/DGKappaDiagnostics/`**。数学の証明は削除せず、元のREADMEと診断用の検査の扱いも更新する。名前・本文を保って移動し、Archiveを正式入口や本体の監査へ自動登録しない。

4本は `DGKappaPresentedFreeNativeFunctor`、`DGKappaPresentedSourceNativeAction`、`DGKappaPresentedSourceNativeFunctor`、`DGKappaPresentedSourceShiftAction`。これらが依存する表示の内部部品まで、根拠なく一緒にarchiveしない。

Project全体で直接のLean import利用者0のファイルは37本あり、その多くはEntrypointsやCompatibilityだった。これは利用者なしの試作の数ではない。外部枝・監査・文字列で選択される入口を含めて調べるまでは、この4本以外を自動archive/削除しない。Compatibility59本は既存のdeprecated alias廃止の別工程（L1）と分け、今回保持する。

## 5. 規模と凍結の一晩

### 5.1 規模の見方

| 単位 | B1で確認した規模 |
| --- | ---: |
| Project全体 | 5,794本（DerivedCategories3,687本を含む） |
| Projectの文献根拠あり | 51本＝HTT/HA41本＋K系10本。ほかの話題分類と重複するので移動総数へ別加算しない |
| 平らな大群 | DerivedCategories2,322、HomotopyDiagramComparison675、FilteredExchange296、ほか。Derived/Gluing下にも1,073本 |
| BS全体 | 604本、うちPrismatic直下320本。越境するBasic8本・lci19本・Derivedの§10群6本等も含めて割り当てる |
| その他 | KST補助54本（閉包なら67）、Diagnostics4本、ScalarTensorView実体1本 |
| 属性 | 本体への1,860対応候補・868ファイル。187未解決台帳、KST/LTのpartial種類147参照等は別途ゲート |

移動を設計する母集団はProject＋BSで **6,398本**。その全てを移す必要はない。最低でも平らな二群の2,642本が新しい下位へ入る案で、他の大群も細分するため、最終の移動本数はB2の完全な割り当て表で確定する。属性と移動の編集ファイルは重なる。全体のビルド時間を本数の足し算から断定しない。移動の依存・下流、既存監査、aliasの保存比較が時間を支配する。

B1は紙だけ。B2は属性・照会・マップ・移動プレビュー・187台帳と全ファイルの根拠付け、B3は移動と付与の一晩、B4は各レーンの追従、という区切りを提案する。実装を一晩に初めて試す計画にはせず、B2の承認された範囲で隔離プレビューと検証・キャッシュを先に用意し、凍結夜は当日差分の取り込みと最終検証に充てる。

### 5.2 凍結の手順

1. **昼まで**：本報告の行き先、とくに③-bのDiagramComparison維持を承認。KEY/版、partial構文、187のrecord-only基準、67本のArchive化も決める。各レーンへ新規ファイルの置き場所を伝え、⑤∞はB3後まで開かない。
2. **B2準備**：元パス→新パスと、所有元付き旧名→新名の全表を作る。移動先衝突・循環・5段の層を静的検査。補助を利用する外部レーン、互換名、openの個別環境、import allを確認する。タグを付ける宣言・付けない宣言・保留の全件が分かるプレビューを提出する。既存KLマップからの二段の改名も合成して検査する。
3. **夕方の取り込み**：各レーンの検証済みコミットを調整役がmainへ取り込む。残る作業木は所有レーンが保存し、一括レーンは直接触らない。凍結の基準HEADと各レーンの取り込み済み境界を記録する。夜は各レーンにコミットを控えてもらう（下書きは保持）。
4. **夜の開始**：mainを一括枝へ取り込み、当日増分を再採取してプレビューへ反映。元ソースとcaptureのハッシュ不一致は作り直す。割り当て・属性・互換名の計画を凍結し、移動・改名・属性付与・利用側更新を同じ束として適用する。
5. **夜の検査順**：静的import/層/衝突 → 移動先と前提のビルド → 型・本文・既存属性の保存比較 → 新設属性の集合照合と地図生成 → root → 正式監査 → verify。Archiveへ移したものの除外と、主経路監査を残したことを明示する。共有鍵・並列度・メモリは**実行時のcoordination§2**に従い、以前のKL-W1の鍵免除を流用しない。
6. **朝の引き渡し**：保存比較の未説明0、属性の欠落・余分0、root/監査/verify成功、保留台帳と除外の説明が揃った束だけを提出。未完なら量・失敗・基準HEADを報告し、未検証の移動をmainへ出さない。調整役が取り込み、各レーンは配布する二つの改名表と `klw1_namespace.py collect/rewrite` でB4の追従を行う。

B4にはレーン別の変更ファイル一覧・マップ・一行のrewriteコマンドと、名前空間を推定してopenを増やさない注意を配る。main取り込み前に各レーンの未コミット作業を一括枝から上書きしない。凍結の一晩で重い検証まで終わるかはB2の実測で判断し、予算を超える見通しなら夕方の凍結前に調整役へ報告する。

## 付表A. Projectの文献根拠と行き先案

以下の元パスは `SerrePositivity/InfinityCategories/Project/` 相対。行き先は `SerrePositivity/InfinityCategories/` 相対。`Section…` は節番号を取り違えないための仮称で、B2で原典の節名・既存配置と合わせる。根拠はHTT/HAの `review/ch*.csv`、Kの `maps/*/items.csv`・`maps/others.csv`。ファイル全体の主題が複数の番号にまたがる場合は主題側を一つ選び、残りの引用は属性で残す。K系は新しい文献トップレベルを今回増やさず話題側に保持する案。

| 元パス | 対応表の根拠 | 行き先案 |
| --- | --- | --- |
| `DerivedCategories/ChainMapHomotopyReflection.lean` | HA 1.3.2.2 [partial] | `HA/DerivedCategoryModels/ChainComplexes/ChainMapHomotopyReflection.lean` |
| `DerivedCategories/CofiberPushout.lean` | HA 1.3.2.17 [partial] | `HA/DerivedCategoryModels/ChainComplexes/CofiberPushout.lean` |
| `DerivedCategories/ComplexEdgeCalculus.lean` | HA 1.3.2.2 [partial] | `HA/DerivedCategoryModels/ChainComplexes/ComplexEdgeCalculus.lean` |
| `DerivedCategories/DGAlgebraDerivedInfinity.lean` | HA 7.1.1.4 [partial]; HA 7.1.1.5 [partial]; HA 7.1.4.2 [partial] | `HA/Section7_1_1/DGAlgebraDerivedInfinity.lean` |
| `DerivedCategories/DGAlgebraPerfectMoritaInfinity.lean` | LT 1.10 [partial] | `Project/DerivedCategories/CompactnessAndPresentability/Morita/DGAlgebraPerfectMoritaInfinity.lean` |
| `DerivedCategories/DGIdempotentCompleteGeneral.lean` | HA 1.2.4.6 [partial] | `HA/Section1_2_4/DGIdempotentCompleteGeneral.lean` |
| `DerivedCategories/DGModuleResolutionLocalization.lean` | HA 1.3.5.13 [partial] | `HA/DerivedCategoryModels/DerivedCategories/DGModuleResolutionLocalization.lean` |
| `DerivedCategories/DGPretriangulatedStability.lean` | HA 1.1.0.2 [partial] | `HA/StableInfinityCategories/Pretriangulated/DGPretriangulatedStability.lean` |
| `DerivedCategories/DGQuasiEquivalenceNerve.lean` | HA 1.3.1.20 [partial] | `HA/DerivedCategoryModels/DifferentialGradedCategories/DGQuasiEquivalenceNerve.lean` |
| `DerivedCategories/DGQuotientExactFunctorEquivalence.lean` | 9 人論文 A.1.5–A.1.7 [partial]; Drinfeld §3.1 \| 3.4（∞ 版） [own] | `Project/DerivedCategories/Verdier/DGQuotients/DGQuotientExactFunctorEquivalence.lean` |
| `DerivedCategories/DGQuotientLocalization.lean` | Drinfeld §3.1 \| 3.4（∞ 版） [own] | `Project/DerivedCategories/Verdier/DGQuotients/DGQuotientLocalization.lean` |
| `DerivedCategories/DGQuotientVerdierSequence.lean` | Drinfeld §3.1 \| 3.4（∞ 版） [own] | `Project/DerivedCategories/Verdier/DGQuotients/DGQuotientVerdierSequence.lean` |
| `DerivedCategories/DiscreteCharacterization.lean` | HA 1.2.1.12 [partial]; HA 1.3.2.19 [partial]; HA 1.3.5.19 [partial] | `HA/DerivedCategoryModels/ChainComplexes/DiscreteCharacterization.lean` |
| `DerivedCategories/Gluing/CanonicalStableStructure.lean` | Kuznetsov–Lunts 4.3 \| 4.6 [partial]; Kuznetsov–Lunts §4.1 [own]; LT (5) [partial]; LT (6) [partial] | `Project/DerivedCategories/Gluing/CanonicalStableStructure.lean` |
| `DerivedCategories/Gluing/NativeSemiorthogonal.lean` | LT (7) [partial]; LT 1.9 [partial] | `Project/DerivedCategories/Gluing/NativeSemiorthogonal.lean` |
| `DerivedCategories/Gluing/Objects.lean` | Kuznetsov–Lunts §4.1 [own] | `Project/DerivedCategories/Gluing/Objects.lean` |
| `DerivedCategories/HeartFullyFaithful.lean` | HA 1.3.2.19 [partial]; HA 1.3.2.21 [partial]; HA 1.3.5.19 [partial] | `HA/DerivedCategoryModels/ChainComplexes/HeartFullyFaithful.lean` |
| `DerivedCategories/InfinityCategory.lean` | HA 1.3.5.8 [partial] | `HA/DerivedCategoryModels/DerivedCategories/InfinityCategory.lean` |
| `DerivedCategories/MappingExt.lean` | HA 1.1.2.17 [partial]; HA 1.3.2.21 [partial]; HA 7.1.1.11 [partial] | `HA/DerivedCategoryModels/DerivedCategories/MappingExt.lean` |
| `DerivedCategories/MappingHomotopyGroups.lean` | HA 1.2.3.14 [partial] | `HA/Section1_2_3/MappingHomotopyGroups.lean` |
| `DerivedCategories/NerveInclusion.lean` | HA 1.3.1.9 [partial] | `HA/DerivedCategoryModels/DifferentialGradedCategories/NerveInclusion.lean` |
| `DerivedCategories/Presentable/DerivedCategory.lean` | HA 1.3.5.21 [partial] | `HA/DerivedCategoryModels/DerivedCategories/DerivedCategory.lean` |
| `DerivedCategories/ResolvedDGQuotientStability.lean` | 9 人論文 A.1.5 [partial] | `Project/DerivedCategories/Verdier/DGQuotients/ResolvedDGQuotientStability.lean` |
| `DerivedCategories/ScalarRestrictionNerve.lean` | HA 1.3.1.3 [own] | `HA/DerivedCategoryModels/DifferentialGradedCategories/ScalarRestrictionNerve.lean` |
| `DerivedCategories/Stability.lean` | HA 1.1.1.12 [partial]; HA 1.3.5.9 [partial] | `HA/DerivedCategoryModels/DerivedCategories/Stability.lean` |
| `DerivedCategories/StableHomotopyComparison.lean` | HA 1.1.1.12 [partial]; HA 1.3.5.24 [partial]; HA 1.3.5.8 [partial] | `HA/DerivedCategoryModels/DerivedCategories/StableHomotopyComparison.lean` |
| `DerivedCategories/StandardCofiberSquare.lean` | HA 1.3.2.17 [partial] | `HA/DerivedCategoryModels/ChainComplexes/StandardCofiberSquare.lean` |
| `DerivedCategories/Verdier/Fractions/TammeFiberSequence.lean` | Tamme (13) [partial] | `Project/DerivedCategories/Verdier/Fractions/TammeFiberSequence.lean` |
| `DerivedCategories/Verdier/Fractions/TammeSplitting.lean` | Tamme (14) [partial] | `Project/DerivedCategories/Verdier/Fractions/TammeSplitting.lean` |
| `FibrationAuxiliaries/Categories/CoreEquivalence.lean` | HTT 3.1.3.2 [own] | `HTT/Section3_1_3/CoreEquivalence.lean` |
| `FibrationAuxiliaries/FunctorCategories/EmptyRelativeFunctorHom.lean` | HA 4.1.4.4 [own] | `HA/Section4_1_4/EmptyRelativeFunctorHom.lean` |
| `FibrationAuxiliaries/SquareDuality.lean` | HA 6.1.1.16 [partial] | `HA/Section6_1_1/SquareDuality.lean` |
| `FilteredExchange/CoherentTotalCocone.lean` | HTT 3.3.4.6 [partial] | `HTT/Section3_3_4/CoherentTotalCocone.lean` |
| `FilteredExchange/CoherentTotalObject.lean` | HTT 3.3.4.6 [partial] | `HTT/Section3_3_4/CoherentTotalObject.lean` |
| `FilteredExchange/KanIntervalPullbackNative.lean` | HA 5.5.6.17 [partial] | `HA/Section5_5_6/KanIntervalPullbackNative.lean` |
| `HomotopyDiagramComparison/CartesianComparisonBoundary.lean` | HTT 2.4.1.6 [own] | `HTT/Section2_4_1/CartesianComparisonBoundary.lean` |
| `HomotopyDiagramComparison/CatInfinity/FunctorColimitConeExistence.lean` | HTT 5.1.2.2 [partial]; HTT 5.1.2.3 [own] | `HTT/Section5_1_2/FunctorColimitConeExistence.lean` |
| `HomotopyDiagramComparison/ClassifiedConeLimit.lean` | HA 5.2.2.39 [partial] | `HA/Section5_2_2/ClassifiedConeLimit.lean` |
| `HomotopyDiagramComparison/FunctorColimitEvaluation.lean` | HTT 5.1.2.2 [partial]; HTT 5.1.2.3 [own] | `HTT/Section5_1_2/FunctorColimitEvaluation.lean` |
| `HomotopyDiagramComparison/StronglySaturatedHom.lean` | HTT 5.5.4.6 [partial] | `HTT/Section5_5_4/StronglySaturatedHom.lean` |
| `LocalizationAndKanExtensionAuxiliaries/FunctorCategories/FunctorIsoExtension.lean` | HTT 5.1.4.8 [own] | `HTT/Section5_1_4/FunctorIsoExtension.lean` |
| `LocalizationAndKanExtensionAuxiliaries/Homotopy/WeakContractibility.lean` | HTT 2.1.3.5 [partial] | `HTT/Section2_1_3/WeakContractibility.lean` |
| `LocalizationAndKanExtensionAuxiliaries/Homotopy/WeakContractibleOpposite.lean` | HTT 5.1.4.5 [own] | `HTT/Section5_1_4/WeakContractibleOpposite.lean` |
| `LocalizationAndKanExtensionAuxiliaries/NerveComparison/Adjunction.lean` | HTT 5.2.5.1 [partial]; HTT 5.2.5.2 [partial]; HTT 6.5.3.1 [partial] | `HTT/Section5_2_5/Adjunction.lean` |
| `LocalizationAndKanExtensionAuxiliaries/NerveComparison/OppositeIso.lean` | HTT 6.1.2.2 [partial]; HTT 6.1.2.3 [own]; HTT 6.5.3.1 [partial] | `HTT/Section6_1_2/OppositeIso.lean` |
| `LocalizationAndKanExtensionAuxiliaries/NerveComparison/OverIso.lean` | HTT 1.2.9.1 [partial]; HTT 1.2.9.6 [own]; HTT 5.2.5.1 [partial]; HTT 5.2.5.2 [partial] | `HTT/Section1_2_9/OverIso.lean` |
| `ModelCategoryComparison/ModelCofibrantRelative.lean` | HA 1.3.4.17 [own] | `HA/ModelCategoryComparison/ModelCofibrantRelative.lean` |
| `QuasicategoryAuxiliaries/Pointed.lean` | HA 1.1.1.1 [own]; HA 1.1.1.4 [own]; HA 1.1.1.5 [own]; HA 1.1.1.6 [own]; HTT 7.2.2.7 [own] | `HA/StableInfinityCategories/ZeroObjects/Pointed.lean` |
| `QuasicategoryAuxiliaries/Quasicategory/SquareZeroMultiplication.lean` | HA 7.3.4.16 [partial] | `HA/Section7_3_4/SquareZeroMultiplication.lean` |
| `QuasicategoryAuxiliaries/SquareHomotopyCategory.lean` | HA 1.1.1.3 [own]; HA 1.1.1.5 [own] | `HA/StableInfinityCategories/ZeroObjects/SquareHomotopyCategory.lean` |
| `QuasicategoryAuxiliaries/VertexFiberOpposite.lean` | HTT 2.1.3.4 [own] | `HTT/Section2_1_3/VertexFiberOpposite.lean` |

付表Aのうち `Pointed.lean` はHA §1.1.1を中心とし、HTT 7.2.2.7も同じ定義への引用として保持する。`OverIso`・`Adjunction`・`OppositeIso` のHTT 6.5.3.1等、後の章で使われる同じ部品の引用は、ファイルを重複して置く理由にしない。部分対応だけのファイルも配置候補には含めるが、対応表の不足を完全対応へ変更しない。

## 付表B. Archive候補54本の一覧

すべて `SerrePositivity/KST/Descent/` 相対、拡張子は `.lean`。全54本にコメント以外の `[ModelCategory SSet…]` があり、rootのimport閉包からは到達しない。移動先の共通接頭辞案は `SerrePositivity/Archive/KST/DescentConditional/`。追加13本は§4.1のとおり。

| 1 | 2 | 3 |
| --- | --- | --- |
| `AugmentedCechRows` | `AugmentedCechSpaces` | `AugmentedCechWeightChange` |
| `AugmentedDerivedCechFubini` | `BottomSimplex` | `CechAdjointReindex` |
| `CechBaseLocality` | `CechDescentComparison` | `CechDescentRetract` |
| `CechFiniteProducts` | `CechLocalRanks` | `CechMapLocality` |
| `CechProductRestriction` | `CechRefinementDescent` | `CechReindexDescent` |
| `CechReindexLocalization` | `CechReindexWeights` | `CechWeakTransfer` |
| `ConstantCechDescent` | `DerivedCechFubini` | `DisjointFamilyCechWeak` |
| `DoubleAugmentedCechSpaces` | `DoubleCechDescent` | `DoubleCechDescentReflection` |
| `EmptyZariskiDescent` | `FamilyCechLocalRanks` | `FamilyCechMapLocality` |
| `FamilyCechOver` | `FamilyCechOverRanks` | `FiniteFreeChartFamilyRanks` |
| `FiniteFreeChartLocalRanks` | `InitialCechDescent` | `InitialCechWeights` |
| `IteratedCechHomotopyCones` | `MixedCechSpaces` | `OverRankCharts` |
| `PresheafCechSpaces` | `PresheafWeakTransfer` | `SplitCechDescent` |
| `SplitCechSpaceExtension` | `TerminalCechDescent` | `TransferBaseChangeDescent` |
| `TransferCechDescent` | `TransferRankChartBaseChangeDescent` | `TransferRankChartDescent` |
| `TransferRankRefinementDescent` | `TransferWeakCechDescent` | `WeightedCechAugmentation` |
| `WeightedCechCofibrancy` | `WeightedCechDerivedComparison` | `WeightedCechDerivedConeCompatibility` |
| `WeightedCechDerivedFubini` | `ZariskiCechLaw` | `ZariskiCoproductDescent` |

## 停止点0の提出

検討の入力はHTT/HAの全review章、Kerodon/BSのitems、Kの文献別itemsとothers。これらのCSV 26ファイルのパス別SHA-256をソートしたJSONの集約SHA-256は `f9e88c506153f7dc9abe9106f63bfe05767c3e0bae120d2f28c70438312f9237`。調査用の静的集計と仮仕分けは `/tmp/bulk-w1-paper/` にある。集計コードは作業用の一時ファイルで、リポジトリの道具として追加していない。

ここで**停止点0**。属性の実装、対応表の変更、移動・分割・Archive化、ビルドはまだ始めない。行き先、partialの構文/Tag方針、187件の扱い、54本に追加する13本の扱いを調整役・ユーザーの確認に回す。

## B2 準備記録（進行中）

B1 の承認（citation-attributes.md §8）を受けて着手した。これは停止点の提出ではない。入力の本体は `0e8c85420`（main を取り込んだ一括枝）に固定し、本体の移動は `/tmp/bulk-w1-b2/preview/` でだけ試す。main と一括枝の既存 Lean 本体は動かしていない。

新設の `SerrePositivity/Util/Citation.lean` は、独立した永続環境拡張で `@[cite KEY "番号"]`、理由必須の四種類の partial、`#cite_tags KEY` を実装した。Mathlib の Kerodon/Stacks 属性は変更しない。ネイティブ属性の関係は `native` として出し、comment から exact/partial を推定しない。版の正本は `research/bibliography.json`、生成部分との一致検査は `python3 scripts/refactor/bulk_citation_registry.py --check`。25 略号を登録した。others.csv の Thomason・Neeman には複数の文献・版が混在するため、最終行で上書きせず、原著を既定とし、出典が違う対応は属性計画で保留する。AGH は B1 で九人論文に提案した旧ラベルであり、著者の頭文字ではないことを明記した。

属性の検査は、四種の partial、理由の不足、未知の略号、空番号、重複の冪等性と矛盾、import 後の保持、module モードでの後置の属性付与を含む10ケースを通した。読み取り用の `#cite_check` は実際の定義元・宣言範囲・型・型内の定数・公理依存・明示的な ModelCategory SSet 仮定を返す。普通の定義と、実在する ModelCategory SSet 仮定付き補題の照会でも検査した。再解釈は元の Lake 設定（maxSynthPendingDepth=3 等）を引き継ぐ。

元の未解決台帳は main `fd50804df` の `research/coverage-location-refresh/2026-11-12-ledger.json` を正本にした。元の187件は延べ187件・異なる名前とパスの組141件である。当初の再構成187候補は異なる組187件だったため、同じ集合ではなかった。共通124組、元の台帳だけ17組、再構成だけ63組。以後の全件表と検査は正本の187行を保持して行う。当初の候補抽出は原判定の再現ではなかったため、その差分を正本の不足とは扱わない。付属の `refresh_locations.py` を取り込み前の表（`7d8ae8623^`）へ読取り専用でかけ直し、未解決187件・解決3,905件について、各行の全内容と順序も正本と一致することを確認した（付表 `location-refresh-replay-check.json`）。

[付表](bulk-w1-b2/README.md) に元の187行の台帳と照合の差分、正本26表の全9,048行・2,387宣言参照のプレビューを保存した。本体候補1,860件の実在・型・所有元の確認を終え、現時点の案は付与1,835、除外537、保留15。元の台帳のうち宣言解決が必要だった29件も全件解決した。Kerodon partial831行は維持して新しいTagを付けない。これは付与計画の確定であり、移動後の全体検証の完了ではない。

共有鍵は `--wait 3600 --class bulk`、一回580秒の打ち切りで取得する。移動先・前提のビルドと保存比較、属性全件のプレビューは継続中。B2 の停止点で、確定した件数・未説明差分・実測と凍結の所要時間をまとめる。

### B2 の配置・改名の案（静的部分）

元の本体は `0e8c85420` に固定した。主対象6,466本（Project 5,794、BhattScholze 604、KST 68）の全割当を作り、5,301本を移す。ディレクトリの主題分けだけの移動では既存の数学的な名前空間を保つ。文献の節へ入る41本とScalarTensorViewの1本に限り、公開515名の名前空間を変える。所有モジュール付きの表を使い、private 15束縛は別に検査する。これにより、ディレクトリ分けに伴う不要な全面改名を避ける。

DerivedCategories は承認済みの主題をさらに分け、移動先で最大の直下ファイル数は FilteredExchange/KanReplacement の194本。③-b の DiagramComparison は現パスを保持する方針とする。固定したmainにはまだ0本なので、凍結前の差分の取り込みでその4本と後続を追加する。移動表はファイルごとに指定する。Prismatic は承認した節・構成を基に細分し、節をまたぐ引用は同じ宣言への複数引用として保持する。ファイルを複製しない。ModelCategory SSet 付き54本は、逆依存閉包を含む67本を Archive/KST/DescentConditional へ置く。DG診断4本もArchiveへ置く。ScalarTensorViewはCommutativeAlgebra/Moduleへ移す。

旧パスの互換モジュールは20本・90名に限る。InfinityCategoriesでは外から使われる86名だけにし、ScalarTensorViewは4名の公開APIを保つ。instance/simpの二重登録はしない。新しくArchiveへ置く条件付き67本には旧パスの互換モジュールを置かない。既存の無関係なArchive 291本は移植対象に広げない。既存Kerodonタグを持つArchiveの1本だけは照合対象なので、そのimportを更新し検証対象に含める。

5段の設定はファイル単位を維持する。mainから来た新規5本にも層を割り当てた。元のmainにある§7.4 RightFibrationMappingOverNaturalityから§9.3 PointSlicePostcompIsoへの1辺は、新規例外の案として別表に出す。利用するのは端点スライスの後合成と同型計算で、Ind固有の仮定は使わない。文献への配置を保つ理由はあるが、調整役の承認済み例外と混ぜない。

属性の付与計画は文献25略号を正本にし、全9,048行・2,387宣言参照を採否別に保持する。付与1,835件の関係は exact 618、special 408、direction 91、stronger-hyp 198、component 520。付与先は856ファイル。除外537件には外部・本体でない記述等527件と、明示的ModelCategory SSet付き10件がある。保留15件はprivate宣言1、Thomasonの文献・版が不整合の1、複数番号を一つに束ねた記述12、Stacks partialの扱い未決1である。Kerodon partial831行は別に維持し、追加のTagは付けない。表示名の古さ等8件は、元の場所の宣言範囲と実在する完全名で確認して補正した。

監査の移動追従も隔離側で準備した。38ファイルのimport・実際に変わる定数名・所有モジュールの表を区別して書き換え、禁止する旧モジュール名は残す。KSTの条件付き監査はarchive側へ分け、通常の監査にはArchive/KST/DescentConditional全体への依存を禁ずる条件を足す。root全体・全監査・verifyはB3の凍結時の工程であり、B2の完了件数に含めない。

検証済みの適用道具は `scripts/refactor/bulk_apply_preview.py`（既定は読取りのみ）、安全性の検査は `test_bulk_apply_preview.py`。Citation の検査は `test_bulk_citation.py --root <作業木> --output <一時ディレクトリ>`。新しいファイルとして追加し、既存の共用採取器・既存スクリプトは変更しない。隔離プレビューの移動後ビルド・全体保存比較は引き続き実行中。

隔離側では、追加で `scripts/audit/bhatt_scholze.lean` と任意の `check_cleanup_c2.lean` のimport・所有元表も追従させた。後者は正式監査に登録しない。InfinityCategories・BhattScholzeの配置の説明とDiagnosticsのREADMEも適用データへ含めた。付表 `layout/preview-edits.json.gz` は実際の隔離側8,678出力を再現するが、全体検証中なのでB2停止点の完了データとは区別する。
