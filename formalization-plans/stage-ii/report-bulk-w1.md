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
| BST13 | Bhatt–Schwede–Takagi, The weak ordinarity conjecture and F-singularities、arXiv:1307.3763v3 | [原典の著者・題目・v3](https://arxiv.org/abs/1307.3763v3)（11-13 訂正） |
| Rydh | Submersions and effective descent of étale morphisms、arXiv:0710.2488v3 | [原典の著者・題目・v3](https://arxiv.org/abs/0710.2488v3) |

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

移動後ビルドの最初の不具合は `ZeroHomotopy` の `IsZeroVertex.isZeroHo` だった。Pointedで移した型の略記と、別ファイルに残す拡張メソッドとの名前空間の差によるもの。元の宣言名・証明を保ち、実際の移動先の型の名前空間へ弱いexportを加えた。構造体だけを対象にしていた拡張の調査を、改名する公開515名すべてへ広げ、別ファイルにある13メンバーを洗った。手書き6メソッドのうち5つは既に処置済みで、この1つを追加した。残り7つはコンパイラが生成した補助。修正対象のビルドは7.46秒で成功し、先行する1,920本も修正後のソースで再確認した。全体の保存比較はこれからである（付表 `layout/build-corrections.json`、`field-fix-build.json`）。

続く `HA/StableInfinityCategories/ZeroTriangleHoMap` の不具合は、既存HAメソッドの弱いexportの受け手が旧Project型に残っていたためだった。メソッドの宣言名を移す問題ではなく、通常の定数参照索引に載らない名前空間の指定の問題である。実際の宣言の改名表に基づき、全ソースの既存exportを調べ、22ファイル・51コマンドの受け手を新しい型へ更新した。無関係な3ファイルの整形は元に戻し、22本すべてが既定の9,514本の保存比較の範囲内であることを確かめた。失敗したZeroHomotopyとZeroTriangleHoMapの優先ビルドは合わせて6.41秒で成功した。公開515名の宣言の改名は増やしていない。弱い名前の対応は `layout/weak-export-corrections.json` に宣言の実際の格納先と分けて記録した。

`VertexFiberOpposite` では、移動後の定理は計画した完全名で存在するのに、直後のexportがその格納先の名前空間を見つけられなかった。Lake設定を引き継ぐ一時コピーで実際の宣言を列挙し、同じ完全名への `#check` が通ることを確認した。Lean 4.35.0-rc4の名前空間拡張は非同期枝でlocalに扱われるため、新しい格納先を定理の非同期処理より先にpublicな空のnamespaceコマンドで登録した。同じ形の5メソッド・4ファイルへ適用し、先の2回帰対象を含む6ファイルのビルドが68.77秒で成功した。宣言名の割当は変更していない。記録は `layout/namespace-registration-corrections.json` と `field-fix-build-v3.json`。

### 11-12 夜：§10 の追加範囲と最新の BS 対応表

B2 の停止点に向けて検証を継続している。B3 は始めていない。夕方以降の台帳の B3 指定を追加し、追加の全ファイル配置案116件は衝突0件。19元モジュールについて108宣言を下の依存へ切り出す案を隔離側へ反映した。private は公開に変えず、必要な元モジュールで `public import` と `import all` を別々に置く。

新しい共有基盤19対象の推移閉包274モジュールを静的に調べ、BSへの依存・∞圏への依存はともに0件。`HomologicalAlgebra.FlatBaseChange` は任意の可換環の平坦な基底変更を扱う4宣言である。既存の実装側prefixからSharedFoundationへ分類し直す案を別表にした。productionの層設定は変更しておらず、停止点で調整役に確認を依頼する。

元の表を固定していた間にmainのBS対応表も更新されたため、現在の表で計画を引き直した。参照の追加59件のうち本体の56件を元のimport環境とLake設定のLeanで照会し、失敗0件。最新計画は全9,048行・2,436参照、付与1,884行（異なる属性1,883組）、除外538、保留14。以前の1,835組は旧入力の数であり、この節の数で更新する。元187件の台帳の29解決・82Kerodon partial維持・76記録のみは変わらない。

ノートを引く22ファイルは、現在の原典対応表とPaper Theorem 2.5の式(2.4)への利用を根拠に、23箇所のコメントだけの置換を準備し隔離側へ適用した。工程ラベル全体と残りの古いdocstringの処置は継続中。BR50の`cochainHomotopy`は実際にはPD脈体固有の型であり、汎用化には別の界面の判断が要る。既存型は保ち、`algebraModule`と添字補題だけを基盤へ移し、PD固有の包みはその側に残す案とした。

追加前の4,352/9,534対象のビルド後、追加範囲を入れるため再投入を一旦止めた。新しい対象は9,550本。再検証で元環境9,514本を30.98秒、既出の回帰対象6本を79.52秒で確認した。最初の追加後ビルドはimport allの構文と不要な局所変数で止まり、ソースを修正して再ビルド待ち。まだ全体保存比較・全件の宣言所有元表・凍結所要時間の確定には達していない。

[夜間の追加付表](bulk-w1-b2/evening/manifest.json)は進行中の全配置表・分割所有元・属性表・依存と衝突の根拠を保存する。隔離プレビューの変更はmainや一括枝の既存Leanに適用していない。BR48の公開32名は衝突0件で、元ファイルと利用側15本の追加採取を進めている。

### 11-13 未明：隔離プレビューの追加検証（B2 継続中）

B2 の停止点にはまだ達していない。R5-3(e) の確認は旧集計241本・63本に限らず、元のBS全604ファイルの名前空間を付表に列挙した。BR48 の公開32名・private3名は、元環境で採取した15ファイルの意味的参照158箇所を書き換え、保留0件。CrysOver・PDCechNerve・PDRawPolynomialSubstitution・WittFiniteBridgeなど複数ファイルで共有する数学的な名前空間は保持する。ディレクトリ名を理由にこれらを平らにする改名は行わない。

追加範囲36元モジュール・58移動先の対象ビルドは275.53秒、前後のスナップショットは26.25秒・16.99秒。後置のcite属性・local notation・quotedな生成名によって、従来のソース宣言判定だけが非対称になっていた61差分を調査した。新しい`bulk_compare.py`はソースの宣言判定用の投影だけを補い、式のハッシュ・公理・kernel属性は変更しない。同じスナップショットを1,079対1,079宣言で比較してPASS、未説明0件。型・本体・公理・属性の人工的な差を全て検出し、明示的に定義したquoted生成名も除外しないことを検査した。このサンプルは最終のRelativeCompleteRegularity配置修正前のもので、使用した割り当て表を一緒に保存する。最終配置は全体比較で改めて検証する。

最終の静的import解析は9,551根・28,581ローカルモジュール・110,219辺で、欠落import・循環・5段の層の違反は0件。ただし層の0件は、FlatBaseChangeをSharedFoundationにする案と既出の§7.4→§9.3の例外案を含むプレビュー設定での結果であり、productionの承認済み設定の結果と混同しない。旧FlatBaseChangeへの実装境界例外は分類変更により不要になるため廃止する案。BSの論文の節の順序は別に検査し、Deltaから後の節への辺0件、BS全体の節の逆向きの辺34件を、実際の元コンパイラ参照と理由付きで列挙した。

全移動先の所有元6,488件で衝突・予定外の上書き0件。再適用の束は8,822出力・5,323旧パス削除を含み、元ソースのハッシュを先に検査してから各出力を復元する。現在の最終プレビューとの全出力一致を照合中。元環境のprivateソース宣言11,674件をkernel名と利用者側の名前で採取し、同一モジュール内の正規化名の衝突0件。保存比較で通常のprivate宣言も照合するための検証専用の採取器を準備し、元の式のハッシュ計算を変えずに採取対象の除外だけを外す。共有の採取器・既存Leanは変更しない。

BR8・BR44は28,565ビルド済みモジュールの元コンパイラ索引から調査した。BSの公開ソース宣言7,022件中、外部のコンパイル済み利用者が見つからないもの4,273件を台帳に残す。drafts・未ビルドの将来入力を含む全利用者の不存在を意味しないため、削除は一切提案しない。R83の二つのSpectrum入口を移す案は103前提・573公開名・9,636行に達するので、二本だけの移動とは扱わず保守へ残す。

数学の固定基準は0e8c85420。最新main ef524d83dとの差分192ファイル（追加187・変更5）を付表にした。新しいDiagramComparisonの7本とEntrypointsの2本は現在の承認済みディレクトリを維持する。この192本は固定したB2ビルド・意味の比較の対象に含めたという主張ではなく、B3前のmain更新・書き換え・差分検証の対象である。BS本体にはこの差分はない。全体の対象ビルド・全件保存比較・属性の再照合・新しい所有元付き全名表・再適用とキャッシュ再利用の実測を引き続き進める。root全体・全監査・verifyはB3の範囲としてまだ実行していない。

### 11-13 未明・続き：採取と private の所有元、凍結に向けた計測

B2 は継続中。共有の `klw1_namespace.py`・`klw1_collect_refs.lean`・`compare_snapshots.py`・`decl_snapshot.lean` は変更していない。新しい Python 補助は別ファイルとして保存し、検証済みのものだけを置く。

`open CategoryTheory Bicategory MonoidalClosed SSet` のような一つの open の各引数は、Lean の `Elab/Open.lean` のとおり先行引数を開いた後で解決する。元の採取では `Bicategory` と未解決の `MonoidalClosed` が記録されていたが、実際には `Bicategory` と `CategoryTheory.Bicategory` の両方、次に `CategoryTheory.MonoidalClosed` を開く。隔離した補助はこの逐次解決を再現し、実ファイル Adjunction の宣言参照994行が元の採取と完全一致することと、通常・局所の三段の open のフィクスチャを20.96秒で検査した。書き換え補助は、名前空間の行き先を変えない plain open に限って元の全候補を同じ順序の完全名で保つ。行き先の変更や削除を含む曖昧な open は従来どおり保留し、5件のガード検査を通した。新しい入口は `bulk_namespace.py collect` / `rewrite`（引数は元の道具と同じ）。

このファイルの無名の local instance は、移動後に自動名の末尾 `_2` が落ちていた。元のkernel名と承認した改名表の対応を保つため、同じ instance にその末尾を含む名前を明示した。引数・型・値・可視性・優先度は変えず、現在のコンパイラ索引に予定した完全名が現れることを確認した。宣言の型を示す `Category` のトークンを instance 名に置き換えることはしない。

通常のprivate宣言も比較に入れるだけでは、別モジュールの同じ利用者向けの名前を区別できない。検証専用の採取器は raw な kernel 名と private の印も保存し、private参照を「予定した／実際の定義元モジュール＋名前」で正規化する。Expr DAG の混合、証明無視、公理の到達検査、kernel属性の検査は維持する。これは従来の指紋と同一と称するモードではなく、出力のアルゴリズム名も所有元付きのモードとして区別する。型・本体・公理・属性の差を検出する検査と所有元別のprivate宣言名の検査の7件、既存の親・補助グループの8件を通した。

同じ `Shared.secret` をprivateに定義したA・Bから参照先だけを替えるkernelの反例も用意した。同じ利用者向けの名前だけの比較はPASSとなるが、所有元付きでは本体の差としてFAILになることを10.09秒で確認した。`bulk_snapshot.py` はこの実際にコンパイルした検証専用のLeanを生成する新しいPythonの道具で、project worktree内には生成しない。既存のLeanの採取器の正本SHAは5d466e25…のまま、検証用ソースSHAは00463c9b…である。scratchで最初に時間切れになった原因は、lean-toolchainのない場所でのsysroot探索がelanの既定版の探索を待っていたためで、検証の環境に `LEAN_SYSROOT` を明示して解消した。原因の解消後に対象ビルドを再開し、鍵は各回10分以内で返却している。

現時点の元環境の確認は監査4本を含む9,518本、30.57秒。最終のopenとinstance名を含む束を別のworktreeへ適用する時間は6.18秒で、ライブラリの32,255 Leanファイルが隔離プレビューと一致した。キャッシュの別作業木での再利用の全対象計測は、対象ビルドがそろった後に行う。

R21は、既存の四項目の語句を変えず改行だけを整える9,913ブロック・4,912ファイルの案を用意した（繰り返し・順序が曖昧な3ブロックは保留）。これは未適用の書式案であり、全既存docstringの数学の説明を自動生成する案ではない。READMEの「全ての既存宣言が新しい規約を満たすという主張ではない」という規約も保持する。全体の字句的な不足の台帳には節コメント・参照用の短文も含まれるので、全てに四項目の追記が必要という意味にはしない。凍結前にR21の追記の範囲を決める点を残す。

その計算への影響を小さな実験で測った。CompletelyFlat.Identity の既存docstringに改行を入れ、利用側の Site.FlatCover とともにビルドし、元へ戻して再ビルドした。基準4.57秒、変更3.51秒、復元3.44秒で全て成功。公開 `.olean` は同一、private・server用の成果物だけが変わった。原ソースと成果物を復元してから通常の対象ビルドを続けている。この二本の実測を全4,912本の完了時間としては扱わず、凍結の見積りで区別する。

### 11-13 早朝：全対象ビルドの継続記録

B2 の停止点には未到達。現在の最終ソースで 8192/9,550 対象が成功し、残りを通常の bulk 整理券で続けている。各回の上限は580秒、内側548秒で、鍵を返してから次に並ぶ。CPU10・物理64 GBと現在の使用量を確認し、隔離側の対象ビルドだけ次の枠から3並列を4並列にした。保存比較や本番の検証設定を変えたものではない。

最終ソースの束は `evening/final-source-preview-edits.json.gz`（SHA256 5d402907e295ee4d514b8fc3e32f4f4af28be9706ac1d6cb813eef4ac004da64）。この束を別の作業木へ6.18秒で適用し、ライブラリ32,255ファイルが隔離プレビューと一致することを確認した。以前の `layout/preview-edits.json.gz` は追加範囲を入れる前の経過データなので、最終の再現には使わない。キャッシュの別作業木での全対象再利用・全体保存比較はまだ完了扱いにしない。

凍結見積り用に以前のKL-W1の測定も別表へ抽出した。以前の103監査の実行時間の単純合計は6,037.06秒、6ジョブ・44 GBのfull verifyは2,226.619秒、root確認は20.50秒。これはB2やB3の今回の実行結果ではなく、通常の4ジョブ・32 GBや今後の監査数にそのまま置き換えない。今回の完了後に実測との区別を付けて見積りをまとめる。B3は始めていない。

### 11-13 朝：全対象ビルドと属性照合の完了（保存比較は継続）

最終ソースの対象ビルドは9,550/9,550成功。別作業木での再利用も9,550/9,550成功し、APFSの独立inodeでの成果物複製113.76秒、19組の再利用確認238.72秒、適用6.18秒を記録した。root・全監査・verifyはこの結果に含めない。

Kerodonタグは前後各672組で欠落・余分0。引用属性は1,883組で欠落・余分・内容差・場所の不整合0。最初の読取りではCategoryTheory名前空間の本体2組を落としていた。元のLean照会のJSON出力に両方が存在することを確認し、宣言名の先頭ではなく実際の定義元モジュールでプロジェクトの宣言を判定して全14組の記録を読み直した。Leanや属性の付与先は変更していない。

11-13の昼の規則に合わせ、以後の鍵の取得後にJSTを判定し、8〜23時は外側280秒・worker予算250秒、一束ごとに返して再申請する。7:50以降もこの短い枠にして8時をまたぐ長い枠を避ける。夜は従来の580秒枠を維持する（最新の夜30分以内の上限より短い）。次は互換名・移動した監査4本・通常のprivate宣言を含む全保存比較を進める。B2停止点はまだ未到達。

### 11-13：全25略号の原典での書誌照合

BST13をBhatt–Schwede–Takagi, *The weak ordinarity conjecture and F-singularities*, arXiv:1307.3763v3へ訂正した。mainの§11を含む指示書だけを枝へ反映し、保存比較の数学の基準は維持した。[全25件の照合台帳](bulk-w1-b2/bibliography-primary-check.json) に、原典URL・題目・全著者の姓・版・訂正前の値・確認範囲を保存した。12件の版付きarXivページと、著者公開PDF、原論文のスキャン、刊行元・公的書庫・公式サイトで照合し、bibliography.jsonの題目を完全な題目、著者を独立したauthors欄へ統一した。既存の25のedition文字列は全て維持する。BST13も既にv3だったため、今回の著者・題目の訂正によるLeanのregistryや属性1883組の版の変更はない。

HTTは著者PDF表紙の2017-04-09を確認し、同題目のarXiv v4（2008）と区別する。BS19は著者版のPDFの題目・著者とハッシュを確認し、同題目のarXiv版の番号へ替えない。Schlichtingは既存の公開稿の同一性として保持し、刊行年を推定しない。TTは1990年の原版と2013年の再刊、Waldhausenは1985年と電子化2006年を区別する。Thomasonの旧DigiZeit URLは404だったため、同じ原論文の刊行元DOIへ正本のリンクを直した。未解決の番号対応をこの書誌照合だけで解決扱いにはしない。

### 11-13 午前：18時の停止点に向けた保存比較（継続中）

18時をB2停止点の提出期限として進める。B3は検収と凍結の確定を待つ。昼の鍵は取得後に時間帯を判定し、外側280秒・worker250秒で返却して並び直す。

対象9,550本のビルドと別作業木での再利用に加え、互換90名・20モジュール、scriptsへ移した監査4本の個別検査が成功した。保存比較に含める外部利用側を照合し、既定の対象根に入っていなかった `KST.DerivedBlowup.UniversalRegularSequence` を追加の前提として隔離側9.53秒・再適用側3.63秒でビルドした。ソースの追加変更はない。監査を含めた最終静的閉包は9,561根・28,587ローカルモジュール・110,230辺で、欠落・循環・5段の層の違反0件（前述の層の二案を条件とする）。

privateのソース位置付き11,677件は、局所記法の生成補助9,263件と通常のprivate宣言2,414件に区別した。移動後の11,687件との差10件は、分割に伴い同じ局所記法を両側へ置いたものとして元のソースコマンド付きで列挙した。通常のprivateの名前・所有元と、550利用モジュールの参照回数は欠落・差0件。自動instance二つの新しい利用者向けの名前を実際のLean索引で補正した。手書きのprivate名を一律に改名してはいない。

全体比較の準備中、コンパイラのprivateな `Lean.ParserDescr` の本体に自身のkernel名が文字通り入ることを確認した。検証専用バイナリに追加のハッシュを持たせ、型が実際にParserDescrで、ソース範囲が局所記法のコマンドに当たるものに限り、その自己名だけを固定名へ置換する。元の本体ハッシュは保存する。元の所有モジュールごとに、型・自己名補正後の本体・公理・kernel属性の全ての異なる内容が一致することを要求する。分割で生じた同一内容の複製は件数と元ソースを残し、順番で宣言の対応を作らない。明示的なParserDescr宣言や別の所有元の宣言には適用しない。実際の記法の優先順位を変えるLeanの反例、型・内容・公理・属性を変える反例はFAIL、自己名だけの変更はPASSとなることを検査した。11件の比較器検査が成功した。

これは保存すべき数学の差を免除する処置ではなく、コンパイラがソースの移動により生成する識別子を区別する補助比較である。共有の `decl_snapshot.lean` と `compare_snapshots.py` は変更しない。検証用のコンパイルはLakeと同じ `-rdynamic` を使い、読み取りの指紋計算だけmaxHeartbeats=0とし、プロセスの時間上限を保つ。全体保存比較はこの最終版で再開し、現在900/9,518元モジュールで成功、未説明0件。全件が済むまでB2完了とはしない。

### 11-13 18時の判断前の状況（2026-11-13T17:50:23、B2未到達）

18時の判断のための途中報告であり、B2停止点の提出ではない。移動先・前提のビルドと別作業木での再利用は9,550/9,550成功。全体保存比較は9,471/9,518元モジュールで成功し、残り47本。未説明0は完了分についての結果である。残りの一覧と検査済みの根拠を [期限前の付表](bulk-w1-b2/deadline-2026-11-13/status.json) に保存した。全名表は全体比較がそろってから確定するので、この時点では凍結の条件を満たしたとはしない。B3は始めていない。

Kerodonタグ前後672組・引用属性1,883組、互換90名、移した監査4本は検査済み。BR25の14 module docstringも別作業木でビルドと保存比較が成功し、元のVとの公開.oleanは14/14一致した。最後の59本は既存の互換モジュール等で、型・本体の検査に時間を要するため、短い枠へ分けて継続している。BST13の訂正と全25略号の原典照合は83e3c2485で保存済み。

昼の枠は外側280秒で返して再申請している。ただし途中にOSの休止が入り、壁時計の保持時間にはその時間を含む。休止の記録と元の保持時間を別々に残し、長い壁時計の保持を5分以内とは記載しない。復帰後の計算中だけ一時的にアイドル休止を抑止した。比較を継続し、全件と全名表がそろい次第、B2停止点の報告を別コミットで提出する。

### 11-13 18時の判断用の状況（2026-11-13T18:01:21、B2未到達）

18時までのB2停止点の提出には間に合わなかった。この時点の途中報告であり、B2停止点の提出ではない。移動先・前提のビルドと別作業木での再利用は9,550/9,550成功。全体保存比較は9,491/9,518元モジュールで成功し、残り27本。未説明0は完了分についての結果である。残りの一覧と検査済みの根拠を [期限前の付表](bulk-w1-b2/deadline-2026-11-13/status.json) に保存した。全名表は全体比較がそろってから確定するので、この時点では凍結の条件を満たしたとはしない。B3は始めていない。

Kerodonタグ前後672組・引用属性1,883組、互換90名、移した監査4本は検査済み。BR25の14 module docstringも別作業木でビルドと保存比較が成功し、元のVとの公開.oleanは14/14一致した。最後の59本は既存の互換モジュール等で、型・本体の検査に時間を要するため、短い枠へ分けて継続している。BST13の訂正と全25略号の原典照合は83e3c2485で保存済み。

昼の枠は外側280秒で返して再申請している。ただし途中にOSの休止が入り、壁時計の保持時間にはその時間を含む。休止の記録と元の保持時間を別々に残し、長い壁時計の保持を5分以内とは記載しない。復帰後の計算中だけ一時的にアイドル休止を抑止した。比較を継続し、全件と全名表がそろい次第、B2停止点の報告を別コミットで提出する。

## B2 停止点（11-13 22:23、18時には未達）

B2の準備を完了した。既存のLean本体の移動・改名・属性付与は隔離作業木だけで行った。この枝の既存Leanは固定基準と同一で、新設した `Util/Citation.lean` だけを追加した。B3は始めず、凍結の日取りと下記の案の検収を待つ。この節と [最終付表](bulk-w1-b2/final/README.md) を最新の数の正本とし、前の経過記録の旧件数を更新する。

| 検査 | 最終結果 |
| --- | --- |
| パスの全表 | 元6,466本、分割先を含む6,488出力。衝突・予定外の上書き0 |
| 移動先と前提のビルド | 9,550/9,550成功。別作業木でも9,550/9,550再利用成功 |
| 比較用の追加前提 | UniversalRegularSequenceの両作業木のビルド成功 |
| 全体保存比較 | 9,518/9,518元モジュールで成功、未説明0。互換群ではproof引数も消さない項の構造の比較を使用 |
| 所有元付きの全名表 | 前134,701・後134,719索引、実名で対応65,683。不明な手書き宣言0。compiler-only 69,018を別記 |
| privateのソース束縛 | 前11,677・後11,687。記法の分割による10複製を記録。通常のprivateと550利用モジュールの束縛の欠落・参照回数の差0 |
| 引用属性 | 1,883組。欠落・余分・内容差・場所の不整合0 |
| 既存Kerodonタグ | 前後各672組。欠落・余分0 |
| 互換 | 90名・20モジュールの検査成功。instance/simpの二重登録なし |
| 移した監査 | scriptsの4本が成功。ライブラリからの再import0 |
| 静的import解析 | 9,561根・28,587ローカルモジュール・110,230辺。欠落・循環・層の違反0（下の案を条件とする） |
| BR25の14 module docstring | 14/14ビルド、64対64の比較成功・未説明0。公開.olean 14/14同一 |

数学の比較の固定基準は `0e8c854208151bc054e15ba3ba183a931b630b1c`。保存比較はv3bの型・本体・公理・kernel属性の検査を保ち、通常のprivateも含めた。局所記法の生成補助は実際のソースコマンドで確認し、ParserDescrの自己名だけの変化を別フィールドで検査する。明示的な宣言や別の所有元の変更は免除しない。型・本体・公理・属性・記法の優先順位の変更を検出する反例も成功した。最終付表は現在の署名に合う成功記録だけを含め、古い失敗記録や分割前の記録を完了件数へ数えない。

### 全表・属性・範囲

最終付表に、全パス、宣言の実際の旧名と新名・定義元、privateのraw kernel名、通常の配布用の改名表、保存比較専用の所有元付きの表を分けて置いた。名前が同じだけのprivateは同一視しない。コンパイラが共有する補助を順番で対応させず、前後の完全な索引と内容の群を残す。通常のB2改名表と、KL前から合成した配布案（15,275モジュール・58,400名前行）も同梱した。移動した型に対する拡張メソッド6名は、実際のkernel名を元の名前空間に保ち、新しい型へweak exportする。全名表の抽出ではこの二つを区別して補正し、前後の実際の宣言の型・本体・公理・属性の一致を確認した。保存比較の入力は変えていない。監査へ移した4本を通常のimportの行き先にしていない。

対応表は全26表・9,048行・2,436宣言参照を保持した。付与1,884行（異なる属性1,883組）、除外538、保留14で、採否と理由を全件表にした。元環境のLean照会は1,979件と追加56件の計2,035件で失敗0、LakeのmaxSynthPendingDepth=3等を維持した。明示的ModelCategory SSet付き10参照には付与しない。Kerodon partial831行は新しいTagを付けず維持する。Thomasonの版・複数番号の束などの保留を、書誌の確認だけで解決扱いにはしない。

元の未解決187行はmain fd50804dfの台帳と全内容・順序が一致する。29解決、82 Kerodon partial維持、76記録のみ。初期に再構成した187候補との違いも保存し、正本の不足と混同しない。BST13はBhatt–Schwede–Takagi、arXiv:1307.3763v3へ訂正済み。25略号全ての題目・著者・版を原典で照合し、全件の原典URLと確認範囲を [書誌台帳](bulk-w1-b2/bibliography-primary-check.json) に残した。

夜の追加範囲は116全ファイル案と、19元モジュールから108宣言・41出力への分割として検証した。新しい共有基盤19根の閉包274モジュールはBS・∞圏への依存0。BSの名前空間は全604本を列挙し、BR48の公開32名・private3名を追加した。数学的に複数のファイルで共有する名前空間を、ディレクトリに合わせるだけの理由では改名しない。ModelCategory SSetの54本と逆依存13本、DG Diagnostics4本のarchive、ScalarTensorViewの移動を含む。利用者が見つからないBS宣言4,273件はコンパイル済みの索引の範囲だけの調査結果であり、削除はしない。

移した監査4本は `scripts/audit/bs_power_root_envelope/` の下へ置く。既存のverifyの発見が一階層だけだったため、隔離プレビュー側だけ再帰的な発見へ補正し、BS段階IIの監査もmanifestへ登録した。実際の発見106本とmanifest106本が一致し、取りこぼし0をPythonで確認した。このscriptsだけの第三の適用束も同梱し、本体の数学の保存比較とは分ける。共有の既存verifyはこの枝では変更せず、root・full verifyをB2で実行したとはしない。

### 検収で判断する案

1. FlatBaseChangeの汎用の4宣言をSharedFoundationにし、旧実装境界の例外を廃止する。新しい共有基盤の閉包にBS・∞圏がないことを検査済み。
2. Kerodon §7.4 RightFibrationMappingOverNaturality → §9.3 PointSlicePostcompIsoの1辺は、端点スライスの後合成の同型の計算として残す案。production設定はまだ変えていない。
3. BSの論文の節の逆向き34辺は、31本の直接参照と3本のimportの可視性に分け、実際の利用宣言と各辺の理由を列挙した。Deltaから後の節への辺は0。これは五段の層の違反とは別の一覧であり、節順序の全てが前向きになったとは主張しない。
4. BR50のcochainHomotopyは現行の型がPDの係数に依存するため、新しい一般化・型の変更は行わない。algebraModuleと添字補題は基盤へ分割し、PD固有の包みはBSに保つ。Spectrumの二入口の移動は103前提・573公開名・9,636行へ及ぶためR83の保守へ残す。
5. R21の既存全体の説明の追記の範囲。四項目の語句を変えない改行案は9,913ブロック・4,912ファイル、曖昧3ブロックを保留とした。節コメントや短い参照の字句的な不足を、全て新しい数学の説明が必要という意味にしない。BR25の具体的な14 module docstringの補完とは分けた。この広いR21案は未適用で、今回の完了済みの移動プレビューへ含めない。

### 実測と凍結の段取り

B2は11-12午後に着手し、この停止点まで約1日強。道具の修正・元環境の照会・整理券待ちも含む。18時には未到達だったことを0307c19f1で報告し、その後に全件を完了した。

適用6.18秒、独立したAPFS複製113.76秒、9,550対象の再利用確認238.72秒。最終ソースの成功75組の実行時間合計は9,508.32秒で、今回のキャッシュを用いた検証の記録である。クリーンビルドの時間ではない。

全体保存比較の壁時計は10.08時間、OS休止を除くと約5.19時間。OSの実際の睡眠・復帰の履歴から休止17,574秒を分けた。通常枠は280秒だが、休止中は単調時計のタイマーも止まるため、壁時計で長くなった保持を5分以内とは記載しない。元の履歴も付表に残した。復帰後は計算中だけ一時的にアイドル休止を抑止し、最終提出時には解除を確認した。

互換群は証明引数を消去せず、より厳しい型・本体の項の構造を同じ改名表で前後比較した。公理・kernel属性の検査も保つ。入力署名のstrict_term_structureで方式を分け、異なる片側採取を混ぜない。この方式のために数学の宣言の対象を減らしていない。生成補助は前述の内容群と前後の完全な索引で扱う。

検証済みキャッシュが再利用できる前提なら、二晩に分ける方が確実で、一晩（23〜8時の9時間）での完了は確約できない。ただし18時の判断には間に合わなかったため、今夜の凍結を開始したとはしない。適用とキャッシュの核は約6分という実測で、全体比較の休止を除く鍵保持は約3.38時間という実測で、昼の整理券待ちを含めた経過とは分ける。main増分の検証に1〜2時間、root・全監査・verifyに3〜4時間、再実行の余裕に1時間を別枠で見込む。未実行の枠は予算であり、今回の実測値とは呼ばない。キャッシュと監査の並列性に依存するため、合計8〜11時間を仮の範囲とする。前半をmain差分・適用・対象と全体比較、後半をroot・全監査・verifyへ分ける二晩案を推奨する。

以前のKL-W1では103監査の単純な実行時間合計6,037.06秒、6ジョブ・44GBのverifyが2,226.619秒だった。B3の通常の4ジョブ・32GBと大きい監査の排他実行では、その37分をそのまま所要時間としない。固定プレビューは106監査で、最新mainの追加分も取り込む。

main 6f380ca7aとの差分は本体605ファイル（追加599・変更6）とscriptsの別表にした。この増分は固定基準のB2成功件数には含めない。大きいキャッシュ失効、増分の検証、広いR21案の追加が必要なら、一晩を確約せず二晩への切替と再見積りを前提にする。

B3では夕方のmainを取り込み、増分の元環境で参照を採取し、表・束を作り直して差分を検証する。固定基準の束を新しいmainへ強制適用しない。次に移動・引用属性・承認済み層設定を適用し、対象とrootのビルド、タグ・引用の再照合、全体保存比較、全監査、verifyの順に進める。通常のbulk鍵を使い、昼は3〜5分以内、夜は30分以内ごとに返して並び直す。verifyは通常の4ジョブ・32 GBを前提とし、大きい監査を同時に二本流さない。今回のB2ではroot全体・全監査・verifyは実行していない。

B4用の元環境でのcollectと改名の一行コマンドは最終付表のREADMEに記載した。元openの可視性を保ち、移った定数だけを実際の新しい完全名へ書き換える。draftsをLeanのcollectへ入れない。

## B3 一晩目：基準の取り込みと初回適用（11-13 23時台、進行中）

基準main c5c4436c0と文書コミットa9dc71e46を一括枝へ取り込み、e381f7546で固定した。main・他レーンの作業木には書き込まず、元環境は/tmp/bulk-w1-b3/beforeに独立したソースと成果物を保存した。B2基準からの増分689ファイル（Lean686本）のうち、元環境のライブラリ681対象のビルドが成功。共有鍵は使っていない。

B2の元入力のハッシュを確認してから、凍結mainの変更を三者比較で合成し、束を作り直した。監査一つのimportブロックの衝突は、双方のimportを残し既知のモジュール改名だけを施して解決した。元mainの追加を消していない。新しいmainファイルと移動先の衝突0。初回適用は8,821出力・5,322旧パス削除。IntegralExistenceの移動は承認済みの指定により除外し、元の場所へ保ち、層・地図の参照も合わせた。これは失敗による取り下げではない。B3′の追加の移動・改名と広いR21は入れていない。

元環境のLean参照採取を4プロセス・各1スレッドで進め、採取と処理済み増分の書き換えは84/686ファイル、保留0。一時ディレクトリの後始末で最初の採取プロセスが終了したため、終了を確認して後始末を修正し、成功済み84ファイルを再利用して再開した。数学の変更や比較の緩和はない。採取・ビルド全体のRSSを監視し32GBで停止、朝8時には4ジョブの処理を停止する。昼は2ジョブまでとし、verify・全体監査は流さない。

現在の実行記録と再開情報は/tmp/bulk-w1-b3/。before-pipeline-2.log、watch-pipeline-2.log、rewrite-driver.logに進捗を保存する。元環境の採取が終わったら、増分全件の書き換え・静的検査・対象ビルド・タグと引用の再照合・全体保存比較へ進む。初回適用後の対象ビルド・保存比較・root・全監査・verifyはまだ成功扱いにしない。朝8時の報告を追記し、その後もB3を継続する。

### B3 採取器の実行分離と増分の参照（11-13 23:50）

通常ビルドが成功する増分で同期採取の200,000 heartbeats上限に達したため、採取用の外部一時helperだけをmaxHeartbeats=0とした。LakeのmaxSynthPendingDepthなどの設定は保持し、採取JSONにhelperのSHAと変更した検査用資源設定を記録する。1ファイル900秒・全子プロセス合計32GiB・同時4プロセスの上限で管理する。共有の採取器は変更しない。Pythonの採取設定の共有を避けるため各ファイルを独立したプロセスにし、完了manifestの一時ファイルもスレッドごとに分けた。成功済み採取は元ソースの全バイトの一致を確認して再利用する。

現時点の増分の書き換えは264/686本、保留0件。制限付きopenは、元環境で解決した全メンバーが同じ実名前空間へ同じ末尾名のまま移る場合だけ、その名前空間へ向ける。通常のopenは元の束縛を保ち、移った項の参照を完全名にする。移動先モジュール名を名前空間に推定しない。

対象ビルド案は10,227本、前提を含む29,776本。全体保存比較案は元10,195モジュールとし、B2の9,518本に凍結main増分を加える。まだ新基準での対象ビルド・比較の成功件数には数えない。

層の設定では凍結mainの新規237ファイルの分類を準備中。節の逆向き15辺を新規に検出したが、15/15とも凍結mainに既に存在し、両端はB3で移動していないことを元ソースで確認した。新しい免除は追加せず、厳密検査の残件と既存債務の一覧を保持してB3由来の辺と区別する。外部の枝の影響はgit参照だけで一次採取し、基準から枝にだけあるコミットが触ったファイルで、移動前の完全名・モジュール名が一致するものを③-a 2本・③-b 6本・⑤a 0本・⑥ 0本と数えた。これは完全名の文字列による暫定一覧であり、非修飾名の束縛を確定した結果ではない。

### B3 夜間の検証手順の準備（11-14 0時台）

増分の採取・書き換えは516/686本、保留0件。新規237ファイルの明示層はPortable 32・Comparison 95・Consumers 110とし、数学的に独立した前提28ファイルをSharedFoundationに分類する案を作った。DGなどの実装や入口を使うものをConsumersへ置き、Comparisonからの免除を増やさない。既存の明示層は変更していない。途中の検査で層の順序・実装境界の違反0。全件の書き換えが済んだ実ソースで再検査してから設定を適用する。

比較元の10,195モジュールでprivate索引を調べ、成果物が不足する83本を検出した。元環境でその83本と照会用Citationをビルドし、実在するkernel名から所有元付き比較表を作り直す。B2の古いprivate索引を新しいmainの成功根拠にしない。

採取後の処理を、元成果物の補完、対象と移した監査のビルド、タグ・引用・互換名、全体保存比較の順に用意した。保存比較が成功した時点でソースをチェックポイントとしてコミットし、root・正式な全監査・full verifyを続ける。監査はまず全件を逐次実行し、verifyは4ジョブ・32GiB、既存の大監査の排他群を保持する。未実行の検査は成功扱いにしない。独立した子プロセス全体の32GiB監視と朝8時の停止を各重い処理に設けた。

### B3 増分採取・書き換え完了（11-14 00:30）

増分686/686本の元環境での採取が成功（採取失敗0）。書き換え686/686本、保留0、実際の変更75本。並行採取の総RSSのピークは23,600,594,944バイト（約21.98GiB）、上限32GiB以内。最後の監査の再解釈に約506秒を要したが、900秒以内で完了した。

導来∞圏監査の三者合成で残った9組は、#print axiomsと二つのQuasicategoryの例の完全名の_root_.SerrePositivity接頭辞だけの差だった。接頭辞を除く全バイトの一致を検査して採取側を採用し、最初に合成した双方のimportを保持した。数学の変更や監査の項目の削除はない。解決後に全686本を再照合して保留0を確認した。

比較元で不足した83本とUtil/Citationの84対象が成功し、実在するprivate索引は11,690行、欠落・同一所有元内の名の衝突0。前提を含む29,776本の対象ビルドを開始した。タグ・引用・保存比較・root・全監査・verifyはまだ新基準での成功を報告しない。

全パス表は32,902元ソース、単純移動5,333本・分割18本、出力の欠落0・複数元が同じ出力へ書く衝突0。新規237ファイルの層はPortable 32・Comparison 95・Consumers 110、独立した新しい前提のSharedFoundationは最終27本。実ソースの再検査で層の順序・実装境界・欠落import・循環0。移した監査のライブラリからの逆importも0。厳密な節の逆向き15辺はすべて凍結main由来で、免除を加えず残件として保持する。

### B3 対象ビルド継続（11-14 00:40台）

対象ビルド106/298組が成功、失敗0。前提込み10600/29,776本、うち予定対象2959/10,227本。資源監視は子孫プロセスのRSSに加え、重いLean/snapshotプロセス数を記録し、4を超えたときも停止する。導入後の観測最大4。対象ビルドの最終照合では、全組が現在のソースの署名と同じで、各組の対象リスト・全体の和集合・予定対象の包含も一致することを検査する。

B4のgit参照を更新し、非修飾名を見落とさないよう、完全名の一致による修正候補に加えて、基準後のコミットが変更したビルド対象Leanを全て採取するfiles.jsonを作った。原環境採取の候補は③-a 9本・③-b 192本・⑤a 22本・⑥ 146本で、draftsは除外。完全名・旧モジュール名の文字列の一致は順に2・6・0・0本。後者だけを確定した修正必要数とはしない。元HEADを各表に記録し、最後にもう一度更新する。

### B3 全Lean作業木の照合とBSの依存（11-14 01時台）

比較元e381f7546と基準c5c4436c0のライブラリ差分を再確認し、追加は承認済みUtil/Citation.leanだけ。数学本体は基準mainと同一である。元の追跡対象Lean 33,408本へ、署名検査済みの再構成束と増分686本の書き換え結果を反映した期待値を作り、現在のLean 33,450本と比較した。欠落・余分・不一致0。draftsを含む非ビルドのLeanも元のままで、対象外のLeanへ未記録の編集がないことを確認した。これは別に実行する数学的保存比較の代用にはしない。

最終チェックポイントには、現在の作業木を期待値の材料に使わず、凍結before・承認済み束・採取索引・改名表だけから686本を再構成する照合を追加した。対象ビルド後に単独で実行し、成功した入力と出力の署名が一致する場合だけ再利用する。新main増分の宣言で、旧改名規則の名前の前方一致が意図せず効く候補は0件だった。

BSの配置を実ソースから再集計し、586本、紙の節の逆向き34辺、Deltaから後の節への辺0。IntegralExistenceは指定どおりPerfectoidization/Derivedに保ち、module docstringの主題Theorem 10.11に基づいて節の一覧では§10と記す。これは層の免除ではない。34辺の実際の宣言参照は、対象ビルド後の索引で更新する。

この時点の対象ビルドは269/298組、前提込み26,900本、予定対象9,255/10,227本まで成功し、失敗0。全組の完了と後続の照合は引き続き実行中である。

### B3 対象ビルド全件完了（11-14 01:30）

298/298組、予定対象10,227/10,227本、前提込み29,776/29,776本が成功した。現在の全ソースの署名と各組の成功記録の署名・対象リストを照合し、重複なしの全体集合と予定対象の包含を確認した。ビルドのピークRSSは13,234,946,048バイト（約12.33GiB）、観測した重いLean/snapshotプロセス数は最大4。共有鍵は使用していない。

移した監査4本も、Lakeの設定を保持して全件成功。before側の元11,690 privateに対し、afterは11,700で、所有元付き対応の欠落0。増分686本を、現在の作業木から期待値を取らず、凍結before・承認済み束・採取索引・改名表から独立に再構成した。9組の明示root接頭辞だけの綴りの解決を除き通常の合成で一致し、最終出力と実作業木の不一致0。これは数学的保存比較の代用にはせず、その準備の入力の同一性の検査である。

現在はKerodonタグ・引用属性の実照会へ進んでいる。全体保存比較・root・全監査・verifyはまだ完了していない。

### B3 タグ・引用属性の再照合（11-14 01:37）

凍結beforeと最終配置afterの実環境でKerodonタグを照会し、前後各672組、欠落・余分0。引用属性は880所有元モジュールを14組で実照会し、1,883組で期待値と一致、欠落・余分・内容・版・実ソース位置の不整合0。元の付与計画1,884行にある同一属性1組の重複は、異なる属性1,883組として集計している。ModelCategory SSet等の除外と保留はB2計画を維持し、勝手に付与していない。

BSの逆向き34辺を対象ビルド後の実際の.ilean索引で調べ、直接の宣言参照31辺、importの見せ直しだけ3辺と分類した。承認済みB2の34辺と実ソースの辺集合は一致しており、辺の除去や層の免除は追加していない。現在は互換名90件の検査を進めている。全体保存比較・root・全監査・verifyは未完了であり、完了扱いにしない。

### B3 互換名完了・保存比較開始（11-14 01:42）

互換90名・20モジュールが全件成功した。既存のKLチェッカーを変えず、日付の旧期待値だけの診断を区別し、別の実メタデータ照会で2026-11-12を確認した。instance/simpの二重登録も検査している。

元10,195モジュールの全体保存比較を開始した。前後は独立した成果物ディレクトリを使い、実在するprivate kernel名と所有元付き規則を適用する。互換群ではproof引数も消さない項構造の比較を維持する。最初の移動監査3モジュールでPASS・差分0を確認したが、全体は実行中であり未説明0の完了報告には数えない。正式監査の発見106本とmanifest106本も一致し、未登録・欠落0を確認した。

### B3 保存比較継続・完了判定の準備（11-14 01:55）

保存比較1,412/10,195元モジュールがPASS、比較済みの差分0。単一採取の実測最大は約5.5GiBで、前後2採取の並列実行を維持して全体RSS上限32GiBを監視する。現在の実行を観測の時間切れで再起動せず、同じ実行ハンドルの進行を確認している。

完了判定の検査を24要件に分けた。現時点では15要件のみ証明済みで、宣言名の全表・全体保存比較・root・全監査・正式verify・検証済みソースのコミット・B4の最終全表が未完了として残る。verifyでは対象制限・独自baseline・sorry閉包の変更・キャッシュを使わず、実行集合106本、実際の4ジョブ・32GiB設定と大監査の排他も実行記録から照合する。完了マーカーがあるだけで合格にせず、現在のソースと実行結果が揃うまで目標を完了扱いにしない。

### B3 保存比較の第一束（11-14 02:09）

元2,948モジュールがPASS・差分0で第一束を終えた。実行時間約1,640秒、子孫RSSピーク13,294,747,648バイト（約12.38GiB）、重い採取プロセスの同時最大2。最後の短い残り時間に収まらなかった未完の採取は成功へ数えず、署名の合う完了済みの片側だけを保持して次の束へ継続した。失敗を無視したり対象を落としたりしていない。第二束は同じ保存比較・所有元付きprivate・互換群の厳しい項構造の条件で進行中である。

### B3 保存比較の中間点（11-14 02:28）

元5188/10,195モジュールがPASS、失敗した比較の記録0、比較済みの差分0。全体の半分を越えた。大きい組の前後約19MBのsnapshotも正常に完了し、242対242宣言・差分0を確認した。時間が長いという観測だけで失敗と見なしたり、比較対象を小さくして合格扱いにしたりしていない。残りの比較と後続ゲートは引き続き実行する。

### B3 保存比較の第二束（11-14 02:38）

第二束は2,752元モジュールを追加して成功し、累計5,700本・差分0。実行時間約1,640秒、子孫RSSピーク12,818,694,144バイト（約11.94GiB）、同時採取最大2。第三束が開始し、5,892本までPASS・差分0を確認した。長めの組でも218対218宣言の比較が成功している。比較の条件・範囲・免除は変更していない。

### B3 保存比較の第三束（11-14 03:10）

第三束で3,072元モジュールが追加でPASS、累計8,772本・差分0。実行時間約1,641秒、子孫RSSピーク14,508,457,984バイト（約13.51GiB）、同時採取最大2。次の束へ引き継ぎ、現在8,964/10,195本までPASS・差分0を確認した。64モジュールの組の処理が数分かかる場合も、同じ実行を監視し、正常な完了を確認している。全体保存比較と後続のゲートはまだ完了扱いにしない。

### B3 全体保存比較完了・凍結mainの変更による停止（11-14 03:57）

全10,195元モジュールの保存比較が成功し、未説明0。対象10,227本・前提込み29,776本の成功記録と現在のソース署名を再照合し一致した。全Lean作業木33,450本について、凍結before・承認済み束・採取済み増分からの期待値に対する欠落・余分・不一致0。Kerodonタグ前後672組、引用属性1,883組は欠落・余分0で、内容・版・場所の不整合0。互換90名・20包み、移した監査4本も成功済み。

宣言名の全表は元モジュール10,195本を対象とし、ソース著者宣言の未対応0。compiler生成宣言は順番で対応を捏造せず、前後の実名の全在庫と比較群を別に保持する。件数は declaration-table-summary.json、実名は declaration-names.jsonl.gz と両側inventoryに保存した。

後続のroot開始前の確認で、mainが凍結a9dc71e46から40faa3892へ進んだことを検出した。差分は formalization-plans/bhatt-scholze/bhatt-scholze-codex-w16.md の文書6行だけで、本体の変更はない。bulk-b3-goal.md §5(b) の停止条件に従い、基準を黙って更新せず、root・正式106監査・full verifyは開始していない。差分と検出時刻は frozen-main-change.json に保存した。保存比較の成功と後続ゲートの成功を混同しない。このコミットは完了報告ではない。

承認済み範囲の移動の追加取り下げはない。IntegralExistenceは指定の元パスを維持。BSの逆向き34辺（直接参照31・import見せ直し3）を記録し、整理はB3′。厳密な節順序検査の15辺は凍結mainから存在し、両端ともB3で移動していない。免除を増やさず残件を明記した。層順序・実装境界・未解決import・循環0。

B4資料はgit参照だけから更新した。下の「完全名一致」は静的な下限で、非修飾名の確定には原環境で全候補のcollectが必要。draftsを除外し、元HEAD・対象一覧・改名表と一行コマンドを添付した。

| 枝 | 採取候補ファイル | 旧モジュール・完全名一致ファイル |
|---|---:|---:|
| math/inf-supply | 11 | 2 |
| math/inf-supply-b | 206 | 6 |
| math/bs-impl | 30 | 0 |
| math/scheme | 155 | 0 |

夜間処理の残りはroot・106正式監査・full verify。再開が認められた場合も32GiB・4ジョブ、全監査直列、verifyの大監査排他を保持する。共有鍵は使用していない。朝8時に残る重い処理を止める規則も維持する。

### B3 停止後の完了要件照合（11-14 04時）

現時点の全24要件を再照合し、18要件が証明済み、6要件は未証明。未証明は凍結mainの同一性、root、正式全監査、full verifyの成功・実設定・全監査集合の一致である。停止チェックポイントd6c95abccが実在し現HEADの祖先であること、そのコミット以後の本体・scripts・research差分0と作業木差分0を照合し、保存比較済みソースがコミットされたことを確認した。数学本体と道具について、凍結mainと現mainの差分0も再確認した。文書更新の許容については照会済みで、停止規則は変更していない。完了ではない。

### B3 対象と全体保存比較のチェックポイント（11-14 07:11）

凍結基準の増分686本の採取・書き換えが完了し、保留0。対象ビルドと前提29776本が成功。元10195モジュールの全体保存比較が成功し、未説明0。既存Kerodonタグは前後各672組で欠落・余分0、引用属性1883組で欠落・余分・内容・場所の不整合0。互換90名と移した監査4本も成功した。これはroot・全監査・full verifyの完了報告ではない。

新しいファイルの5段の層を依存順に確定した。既存の明示的な層・免除は変更していない。DGなどの実装や入口を消費する新規ファイルはConsumers、独立した基盤の新規前提はSharedFoundationとし、Comparisonから実装への例外を増やさない。層の順序・実装境界の違反0。節の逆向きは凍結main由来の15辺を厳密検査の残件として保持し、0件と呼ばない。両端はB3で移動しておらず、B3′での確認対象として付表を残した。

ここから、同じ枝でroot、全監査、VERIFY_JOBS=4・VERIFY_MEMORY_GB=32のfull verifyへ進む。大きい監査は同時に二本流さず、朝8時に重い処理を終了する。共有鍵は使用しない。

### B3 文書更新を許容して再開（11-14 07時台）

調整役の回答により、formalization-plans/・research/ の文書だけでmainが進むことは許容し、数学基準c5c4436c0を維持して再開した。現在main 602fe450fの増分は通常のMarkdown文書3本だけであり、本体・道具・設定の変更0。その判定を各重い処理と正式監査の前に繰り返す。現時点の実装は明白な通常Markdownだけを自動許容し、その他の入力変更は停止する。mainの取り込みはしていない。

対象ビルドの署名・全Lean作業木・増分の独立再構成・BS34辺・凍結由来の節順序15辺・宣言表を再照合して成功。再検査のチェックポイントは1fb4a34bd。元の保存比較10,195本の成功と未説明0は保持されている。rootビルドを開始した。正式全監査とfull verifyは引き続き未完了。朝8時に重い処理を終了する。

### B3 rootビルド成功（11-14 07:23）

lake build SerrePositivity が31,251ジョブで成功した。実行時間689.25秒、子孫RSSピーク10,586,439,680バイト（約9.86GiB）、重いLeanプロセス同時最大4。現在の数学ソースは対象ビルド・保存比較済みチェックポイントから変更していない。rootの終了コード0を確認した後、正式監査106本の前提ビルドへ進んだ。全監査とfull verifyは未完了。

### B3 一晩目の報告（11-14 08:01）

基準c5c4436c0の数学を保持し、増分686本の採取・再構成・参照書き換え、承認済み移動・属性・層の設定を適用した。対象10,227本と前提込み29,776本のビルドが成功。保存比較10,195元モジュール、未説明0。タグ672組、引用属性1,883組で欠落・余分0、引用の内容・版・場所も一致。互換90名・20包み、移した監査4本が成功。元宣言140,687記録の全表と前後実名の在庫を保存し、著者宣言の未対応0。

root: 成功（実行時間689.3秒、ピークRSS 10586439680バイト）。正式監査: 32/106本が成功、実エラー0本、昼境界による中断0本。full verify: 未完了。個別の成功・失敗・中断は付表に分け、昼境界の中断を成功へ数えていない。

追加の移動取り下げは0。IntegralExistenceの元パス維持など承認済みの狭い範囲を守った。BS逆向き34辺（直接31・見せ直し3）と、B3で両端を動かしていない凍結由来の節順序15辺は一覧に残し、B3′で確認する。層の順序・実装境界・未解決import・循環0。

main文書更新を検出して一時停止したが、調整役の回答を受け、文書のみの更新を許容して07時台に再開した。本体・道具・設定の変更は許容しない。共有鍵は使用せず、32GB・4ジョブ、監査直列の制限で実行した。朝8時以降は軽い処理2ジョブまでとし、全監査・verifyは停止する。

二晩目の残りは正式監査74本とfull verify。未実行分の時間はまだ実測できないため、完了見込みの時間は確約しない。夜23時から、実行対象とソース署名を照合して残るゲートへ進む。数学・比較の条件を変えて通すことはしない。

B4の改名表・一行コマンド・4枝の影響一覧を最新git参照だけから更新した。草稿は採取候補に含めず、完全名の文字列一致を非修飾名まで含む確定件数と見なしていない。取り込みは調整役が行う。

### B3 保存比較の証拠と二晩目の待機（11-14 08:05）

178組・元10,195モジュールの成功receipt、比較結果、採取の署名、実行資源をpreservation-evidence.tar.gzに保存した。前後356個の実snapshotのSHA-256を採取記録と全件照合して一致した。完全なsnapshot本体は独立before/after作業領域に残し、そのハッシュを保存した。新しいLean実行はしていない。

JST11-14の23時に一回だけ再開する待機プロセスPID13368の生存を確認した。昼は待機するだけで、ビルド・監査・verifyを起動しない。夜の開始前にmainの変更範囲、対象ビルドの署名、全ソース、増分の独立再構成、全保存比較receiptを再照合する。その後、rootと全106監査を新たに実行し、VERIFY_JOBS=4・VERIFY_MEMORY_GB=32・VERIFY_CACHE=0のfull verifyへ進む。成功済み32本を含め全監査を再実行するため、結果のキャッシュや対象の削減は使わない。朝8時で重い処理を終了し、実結果を報告へコミットする。共有鍵は使わない。

資源の照合はverify_runner.pyのGB定義（10進）に合わせ、32,000,000,000バイトとしている。既に完了した重い処理の実測ピークはいずれもこの値以下。次回のguardと自レーン全体の監視も同じ値を使う。実測RSSをランナーの資源見積もりへ反映するが、検査成功のキャッシュは使わない。実測10GB以上の監査は既存の排他群に追加する。これは資源の制御だけで、数学・比較・検査対象を変更しない。

### B3 日中の継続を開始（11-14 08時台、調整役・ユーザーの指示）

この回は日中も正式監査を一本ずつ続け、full verifyはVERIFY_JOBS=3・VERIFY_MEMORY_GB=24・VERIFY_CACHE=0で実行する。23時以降に開始する場合だけ4・32へ戻せる。共有の鍵は使わない。夜23時まで待つPID13368を終了し、旧プロセスの終了コード143を確認した。夜待ちの二重実行はない。

本体・scripts・research・Lake設定・toolchainが保存比較済みチェックポイントから変わっていないことを検査した。朝の32監査の各receiptと生ログを保存済みアーカイブに全件照合し、全バイト一致・全件成功を確認した。この実際の成功32本を保持して残る74本を直列に実行する。正式な106本の対象を減らしておらず、full verifyの監査は全てキャッシュなしで新たに実行する。各監査の直前にmainの変更範囲も確認する。検査の内容やbaselineを変更せず、資源設定だけを新しい指示に合わせた。

### B3 承認済み例外の注記を更新（11-14 08:39）

Kerodon §7.4→§9.3の承認済み1辺に、B2当時の「検収待ち」という理由文が残っていたため、bulk-b3-goal.md §2(2)で承認済みと明記した。変更はscripts/refactor/layers.jsonの当該reasonだけ。JSONを戻して比較し、その他の全フィールドが同一であること、本体・Lean・実行スクリプト・設定の他の変更0を確認した。検査規則・例外の辺・層は一切増減していない。静的解析を再実行し、逆向き15辺の全フィールドの集合が同一、他の違反0。順序が不定な出力は辺集合と件数の両方で照合した。監査が読むLean入力は変更していない。archive67本・Diagnostics4本・ScalarTensorViewの互換4名・FlatBaseChange4宣言・PD包みの維持・Spectrum二入口の保留・BST13訂正も実物で確認した。

### B3 E∞監査の宣言名2件の補正（11-14 08:54、再実行待ち）

最初のE∞正式監査が、必須宣言リストのWeakThreeArrowを見つけられず失敗した。構造を調べると、WeakThreeArrowとSpecialHammockの二つで、ファイルをReplacements/へ移したパスがLean.Nameの必須宣言名にも入っていた。実際の宣言はModelCategoryComparison名前空間に保たれている。元の凍結監査の引用名・前後の所有元付き実名表・現在の定義を照合し、当該Array Lean.Nameの二引用だけを実際の宣言名へ戻した。env.containsで調べる宣言リストと、他の監査がenv.getModuleIdxFor?から調べるモジュールリストを区別し、モジュール選択の引用は変えていない。共通のcollect/rewriteはimport行だけをモジュール地図で変えており、今回の混同はB2適用束の監査データ側にあった。

必要宣言の検査数・公理の許可集合・全監査の対象は不変。最初の失敗ログと資源記録を保存した。補正は凍結元の引用名と実名表から独立に作る二トークンの機械的変換として台帳化し、元の束は改変していない。元の束・採取済み増分・当該補正から全33,450 Leanファイルを再構成し、欠落・余分・不一致0。対象10,227本と前提29,776本の成功署名も不変なので、数学本体やビルド済み宣言には変更がない。E∞監査自体は他の直列監査の後に最初から再実行し、成功するまで完了扱いにしない。

### B3 配置の案内を最終条件に合わせる（11-14 09:16）

InfinityCategoriesのREADMEから今回のB4資料へリンクし、KL-W1時点の表と区別した。BSのREADMEにはIntegralExistenceの元パス維持を明記した。B4資料にはモジュール選択用と必須宣言検査用のLean.Nameの区別を追記した。変更は文書だけで、Lean・実行コード・設定の変更0。監査は継続中で、E∞監査の再実行とfull verifyはまだ完了していない。

### B3 正式監査106本が全件成功（11-14 09:31、full verify実行中）

初回は105成功・E∞1失敗。引用名2件を訂正したE∞正式監査を最初から実行し、26,491宣言・標準三公理のみで成功した（187.55秒、ピークRSS7,706,050,560バイト）。初回の失敗を隠さず別に保存し、成功した再実行のsource SHAとログを対応づけた。最終の正式監査は対象106/106、成功106、未解決の失敗0。段階II BSは18,156宣言、AlgebraicGeometryはaudit_kst_scheme_lemmasで8,615宣言が標準三公理のみ。全監査の実行は直列である。

9:33にHEAD4547afc5eでfull verifyを開始した。実設定は3ジョブ・24GB、VERIFY_CACHE=0、対象制限・独自baseline・sorry対象の変更なし。大きい監査の既存排他群へ実測10GB以上を加えた（KST S-constructionを含む）。主定理監査は既存ランナーどおり並列プールの後に単独実行する。全ソースの独立照合・対象ビルド署名を開始直前に再確認して成功した。full verifyはまだ完了していない。

## B3 完了報告（11-14 10:26）

数学基準はc5c4436c0、検証対象のLean・実行スクリプトはfull verify開始時の4547afc5eから同一。B2検収済み範囲と増分686本の再構成を完了した。未承認の数学の主張・証明・界面の変更はない。[検収用資料](bulk-w1-b3/README.md)を結果の索引とする。

| 検査 | 完了結果 |
|---|---|
| 対象ビルド | 10,227/10,227、前提込み29,776/29,776成功 |
| root | 31,251ジョブ成功、verify内の再ビルドも成功 |
| 正式全監査 | 106/106成功。BS段階II18,156宣言・AlgebraicGeometry8,615宣言を含む |
| full verify | PASS・gate=true、監査106本・失敗0・既知失敗0・監査結果キャッシュ0 |
| 全体保存比較 | 元10,195モジュール、未説明0。通常のprivateと互換の厳しい項構造比較を維持 |
| 引用・タグ | 引用1,883組、既存Kerodon672組。欠落・余分・内容・版・場所の不整合0 |
| 互換・移動監査 | 90名・20包み、移した監査4本が成功 |

正式verifyの実設定は3ジョブ・24GB、VERIFY_CACHE=0。全監査集合とsorry閉包を制限せず実行した。実行時間2966.944秒、全子孫RSSピーク31010799616バイト。大監査の排他も実行記録から確認した。共有の鍵は使用していない。E∞監査の初回失敗はモジュール名と宣言名の混同2件であり、実名へ訂正して監査を最初から再実行し成功した。初回の失敗と成功した再実行の両方を保存し、検査項目や公理の条件を減らしていない。

追加取り下げは0。IntegralExistenceは指定の元パスに残し、PD固有のcochainHomotopyもBSに残した。Spectrum二入口は承認どおりR83へ。広いR21・B3′の追加範囲・未使用宣言の削除は入れていない。BSの逆向き34辺と凍結由来の未移動15辺は[維持・保留の一覧](bulk-w1-b3/retained-and-deferred.json)へ記録した。層・実装境界・欠落import・循環0、節順序の全てを前向きにしたとは主張しない。

B4用のimport表・所有元付き実名表・一行rewriteコマンド・各枝の影響一覧を更新した。下表の一致数は完全名・旧モジュール名の静的な下限であり、非修飾名は全採取候補の原環境collectで確定する。draftsは除外。他レーンの作業木は変更していない。

| 枝 | 観測HEAD | 採取候補 | 文字列一致ファイル |
|---|---|---:|---:|
| math/inf-supply | b0f67ea78 | 25 | 4 |
| math/inf-supply-b | 1472ec719 | 276 | 7 |
| math/bs-impl | 46bd6230f | 95 | 0 |
| math/scheme | 029f0e8f3 | 284 | 0 |

資源設定の注意：VERIFY_MEMORY_GB=24はランナーの見積り予算であり、物理RSSの強制上限ではない。今回は1件（F1）の見積りが予算を超え、既存ランナーのoversize_aloneで単独実行された。F1単体の実測最大RSSは30,218,108,928バイト、自レーン全体の監視ピークは31079546880バイト（約31.1GB）。全体の32,000,000,000バイト強制上限内で完了し、監査の省略や大監査二本の同時実行はない。

B4の具体的な一行コマンドと展開するJSONは[B4手順](bulk-w1-b3/B4-README.md)に記載した。全パス・実名・静的検査・原典の書誌確認と187件台帳の履歴も保存している。mainへの取り込みは調整役に委ねる。


## 5∞-0 段 0：型つき一覧（11-14、枝 bulk/5inf-0）

main `efa846fe8` から専用 worktree の枝を切った。主題は `bulk-5inf0.md` §2 の A01〜A07・B01〜B07 の14項目で固定する。B4の問い合わせを優先する。⑤aのShared/EInfinityPowerOperation・A4のP⁰、EInfinity/・InfinityCategories/・AlgebraicGeometry/には変更を入れない。ビルドは共有鍵 `--class bulk --wait 3600` を使い、昼は一束280秒以下、夜は30分以内。

一覧：済み 0／全体 14（うち追加 0）。これは段0の計画で、型検査・削除・実装の完了報告ではない。

### A：対象と宣言の扱い

[全ソース台帳](bulk-5inf0/draft-source-inventory.json)には各宣言の場所・型のソース・sorry数・本体の同名候補を保存した。[集計](bulk-5inf0/draft-inventory-summary.json)の基準はA0〜A9直下40本、10,819行、コード中のsorry 705箇所。コメント・文字列を除外した静的採取で、Leanによる型照合の代わりではない。117件の同名候補は候補として記録し、型・仮定が異なるものを同一の定理として消さない。新しい結果の証明で穴を埋める作業は加えない。

| ID | 対象（drafts/ 以下）と変更 | 消す宣言の計画 | 見込み行数 |
| --- | --- | --- | --- |
| A01 | A0全5本・A1全5本。古典的site、Čech、結晶・PD模型を現在の本体へ。一般のRΓ・CAlg・HT比較は未来の宣言として保持 | 同名76件の本体への置換を照合。内訳A0:24、CrystallineInput:11、CrystallineSite:18、DeRhamComparisonPoly:22、HodgeTateComparison:1。型が異なるものは削除から外し、古典的な芯だけを呼ぶ | 900–1,300 |
| A02 | A3/DiscreteCase・LciAndQuasiregular。EInfinityTheoryを明示しD71〜73に追従。A1末尾のprismaticCohomology_lci_universalをA3へ移す | initial_of_retraction_idempotent・prismOver_isIdempotentCompleteの2件は本体の圏論へ。残る約26sorryの古典的な芯は既存のDiscreteDelta・DiscretePrism・LciEnvelope・RootRelationを使う。Δとの同定を消さない | 350–600 |
| A03 | A2/AnimatedAlgebra（利用側A1・A7も確認）。本体CechAlexander/Comparison/PolynomialCategoryのPolyをimport | PolyとそのSmallCategory instanceの2宣言。polyNerveなど未来の構成は保持 | 30–70 |
| A04 | A4全3・A5全6・A6全5・A7全4・A9全1。Theory界面・CAlg版・nonempty_e3_of_cAlg・ComparisonのIsDiscreteに追従。Not8.1はexists_boundedPerfectPrismPresentationを使用 | A7/isPCompleteVertexの1件をB07へ。ほかは一致を確認した古典的証明だけ差し替え、同名だけを根拠に削除しない。P⁰部分の変更0を検査 | 1,000–1,600 |
| A05 | A8全4本。本体のAlmost・Perfectoidization/Derivedをimportし、未来のProp10.9・Thm10.11などを残す | 現在の台帳で同名39件。以前の「40件」との1件差は台帳の名前・local宣言も照合して確定。same-nameの39件も型検査前は削除確定ではない | 300–500 |
| A06 | A0/BaseChange・A1/HodgeTateComparison、参照側A3。本体HasCochainCompleteTorAmplitudeへ | HasFiniteCompleteTorAmplitudeの2定義。係数とFin列・上界cを明示して呼ぶ。∞忘却関手との新しい比較定理を加えない | 130–220 |
| A07 | 上記40本の冒頭・READMEの古い基準。保護されたファイル・P⁰は変更しない | 数学宣言の削除0。基準efa846fe8と今回の検査方法を明記。共有draft依存の検査結果も分ける | 60–100 |

削除候補を実際に除く際は、元の型と本体の型・残存する参照先を確認する。新しい仮定を足して同じ定理と呼んだり、未来の未証明部分を単なる本体へのリンクに置き換えたりしない。draftの型検査は一時的なモジュール配置で本体とdraft間の実importを解決し、元のLake設定を引き継ぐ。共有draftに追加の構成が必要なら範囲外として止める。

### B：追加する型と配置案

以下は予定の型（名前解決・宇宙を含む最終のLean検査前）。`p` は素数、`P : OrientedPrism p A`、`Q : OrientedPrism p B`、`R` は `A ⧸ P.ideal` 代数、`κ : Cardinal.{u}` とする。

- **B01（120–200行）**：`Prism/Basic/Category.lean` に `OrientedPrismCat p`（台 `CommRingCat.{u}` と `OrientedPrism p carrier`）を置き、`Category (OrientedPrismCat p)` のHomを既存 `OrientedPrism.Hom` にする。現在の本体と同じ向き付きprismの圏であり、一般の非単項Cartierイデアルのprismを作ったとは呼ばない。`Hom.IsFlat (f : Hom P Q) : Prop := letI := f.toRingHom.toAlgebra; IsCompletelyFlat (Ideal.span {(p : A), P.generator}) B`、`Hom.IsFaithfullyFlat` も同じイデアルの `IsCompletelyFaithfullyFlat`。siteの述語は `f.toHom.IsFaithfullyFlat` の略記へ。通常の平坦性へ取り替えない。
- **B02（50–100行）**：`isBoundedPrism_of_perfect (hP : P.deltaStructure.IsPerfect) : IsBoundedPrism P`。既存の `distinguished_quotient_p_pow_torsion_killed_by_p` により上界1。任意の生成元について `isDistinguished_of_span_eq {d : A} (hd : Ideal.span {d} = P.ideal) : P.deltaStructure.IsDistinguished d`（既存の正則な生成元との単元倍の比較を用いる）。選択生成元については既存 `P.isDistinguished_generator` が完全性なしで証明済み。`ofDiscreteDelta P D η hη hreg hp hd : OrientedPrism p C` の向きは `η : A →+* C`、生成元は `η P.generator` で指示どおり。重複構成子を加えない。
- **B03（250–450行）**：`Prismatic/Site/PrismOverSmall.lean` に `PrismOver.essentiallySmall : EssentiallySmall.{u} (PrismOver P R κ)` とinstance。cutoffの下限は本質的小ささ自体には不要（結晶siteと同じ）。`κ.out`の部分集合上に環・δ・prism・二つの脚を移し、誘導圏から本質的全射な充満忠実関手を作る。移送・その同型と法則は既存構成の法則としてこの項目に含む。CechAlexanderSmall・AffineCechSiteNerveの明示的なEssentiallySmall仮定を除く。
- **B04（70–130行）**：`PerfectPrismOver := ObjectProperty.FullSubcategory (fun X : PrismOver P R κ => X.Q.deltaStructure.IsPerfect)`、`PerfectPrismaticSite := PerfectPrismOverᵒᵖ`。包含のop `ι : PerfectPrismaticSite ⥤ (PrismOver P R κ)ᵒᵖ` による `ι.inducedTopology (PrismOver.flatTopology hκ)`。Rem4.6の定義だけで、比較定理は加えない。
- **B05（70–130行）**：`HasBoundedPTorsion (p : ℕ) (S : Type u) [CommRing S] : Prop := ∃ N : ℕ, ∀ n x, (p : S)^n*x=0 → (p : S)^N*x=0` を可換環論へ。`IsSemiperfectoid (p : ℕ) [Fact p.Prime] (S : Type u) [CommRing S] : Prop := IsModuleComplete S (p : S) (ModuleCat.of S S) ∧ ∃ (T : CommRingCat.{u}) (q : T →+* S), IsIntegralPerfectoid T p ∧ Function.Surjective q` をSemiperfectoid/Basicへ。使わない基底Rを引数にしない。基本補題はこれらの構成・射影と `IsBoundedPrism P ↔ HasBoundedPTorsion p (A ⧸ P.ideal)`。本体全体の展開形置換は行わない。
- **B06（0行、5∞-3aへ）**：一般の結晶prismのProp6.2(b)・Cor5.5を含む `hodgeTate_iso_crystalline` と `deRhamComparison` の系は、一般の `hodgeTate_iso` 自身がA1/HodgeTateComparisonのsorryであり、本体の多項式結晶基底の特殊場合からは出ない。§2B6の明示的な延期を適用し、draftの一般形を維持する。本体で一般の比較を仮定した定理を完成品として追加しない。
- **B07（70–150行）**：許可された一般の場所 `HomologicalAlgebra/DerivedInfinity/VertexPredicates.lean` を候補とし、`SerrePositivity.DerivedInfinity.IsConnectiveAt (R) (n : ℤ) (X : (derivedInfinityCategory R) _⦋0⦌) : Prop := ∀ i, n<i → Subsingleton (derivedInfinityHomology R i X)` と `IsPComplete (p) (R) (M) : Prop := DerivedCompletion.IsComplete R (p : R) ((derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩)` に実定義を移す。BS側の利用とdraftをこれに寄せ、衝突するdraft/DerivedGeneral/Truncation側の再定義も除く。禁止ディレクトリの参照は静的検索0件。変更前後の述語は同じ定義式であり数学的強化なし。実装境界・層の静的検査で配置も確認する。

### 見込みと検査

[行数予算](bulk-5inf0/stage0-estimate.json)は **3,400–5,550行**。Leanの追加行＋削除行で測り、draftsの書き換え・削除、宣言のdocstringを含める。非Leanの報告・台帳は別計数。本体だけの見込みではない。上端5,550≤6,000なので指示§3の条件付き承認で実装へ進む。外枠は **11,100行**。約2,775行に達した時点で実績と残りを報告し、外枠に届く前、または新しい構成・範囲外の数学が必要になれば止める。

対象ビルドは小分けにし、Bの新規宣言を列挙した `assert_no_sorry` の小監査を別に用意する。BS段階II監査には新モジュールと明示的な必須名の登録案を報告する。draftsの既存sorryは本体の新規宣言の監査とは分離し、数の前後差と型検査の対象・未実行分を明記する。今回まだLeanの変更・ビルド・監査は0。


### 5∞-0 実装経過（11-14昼、型検査継続中）

一覧：済み 0／全体 14（うち追加 0）。実装の完成ではない。

Lean差分は追加1080・削除1486、合計2566行（半分の目安2,775行、外枠11,100行）。A0〜A9のコード中のsorryは705→585箇所。前後のファイル別計数と未実行の検査は[経過台帳](bulk-5inf0/implementation-checkpoint.json)に分けた。残りは主にdraft依存を解決した型検査と、その診断に基づく修正で、行数は未実測。上端の予算5,550行と外枠を維持して監視する。

本体7モジュールの追加と直接利用側の修正を書いた。最初の対象ビルドでは有界p冪ねじれ・semiperfectoidの2モジュールが成功。Categoryは既存APIの宇宙条件、PerfectBoundedは定義の展開で失敗した。前者を同じ宇宙に揃え、後者ではP.idealを明示展開して再検査を並べている。[初回の生ログ](bulk-5inf0/initial-target-build.log.gz)を保持し、失敗を成功へ数えない。対象ビルド・小監査・draftsの型検査の全件成功はまだない。

B07の実定義はDerivedInfinityの一般ファイルへ移し、既存の二つの公開名は同じ本体ファイルの互換略記として保持した。draftsでの二重の宣言は外した。旧名を使う別枝を不用意に壊す変更にはしない。B04の大きいsiteは `PerfectPrismaticSiteLarge` と呼び、draftが使う小さい模型 `PerfectPrismaticSite` と区別した。数学の条件は変えていない。

A3は明示的なEInfinityTheory引数へ追従し、局所データの旧変数Eを先に改名した。一般のΔとの同定はdraftに保持し、通常のδテンソル・包絡同型からのδ構造・A_infの古典的な芯を本体へ寄せた。Notation8.1のA_infは本体のTheorem3.10に基づく構成を参照する。Tor振幅の二重定義は除き、本体のHasCochainCompleteTorAmplitudeを使う。A8の40件は39件の完全修飾名の一致と、同じ定義式で名前空間だけが異なるFiniteEtaleAwayの1件。局所instanceの登録も保持した。これらの書き換えは、draftsのLean検査が通るまで完了に数えない。

本体とdraftsの68 importをB3のモジュール表で更新し、A0〜A9のimport先の欠落0を静的に確認した。基準台帳の生成器を別rootでも実行できるようにし、読み取りだけのmainから再生成した2表が保存済みの表と全件一致した。本体の層の静的検査は基準・変更側とも同じ15辺で、新しい違反・除外0（[差分](bulk-5inf0/initial-layer-comparison.json)）。最終状態で再検査する。禁止3ディレクトリ・Shared/EInfinityPowerOperationの変更0、A4のLemma8.4の保護節は基準と一致。正式BS監査の登録案は[7モジュールの表](bulk-5inf0/stage2-audit-registration-proposal.json)に置いた。
