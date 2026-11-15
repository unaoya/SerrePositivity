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


### 5∞-0 本体の小項目と A03 の検査完了（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。内訳はB01〜B05・B07の6件、A03の1件、指示§2B6で許可されたB06の移管1件。B06の一般の結晶比較を証明したという意味ではない。[項目別状態](bulk-5inf0/item-status.json)の残りA01・A02・A04・A05・A06・A07を続ける。5∞-0全体の完成ではない。

本体の新規7モジュールと直接の利用側・Notation8.1の前提、13対象の `lake build` が4,821ジョブで成功。小監査は7モジュールに定義された全99宣言・必須11名を調べ、標準三公理のみで成功した。カウンタの型注釈を直す前の監査スクリプトの失敗も保存した。監査対象を減らしていない。[本体の検査結果とソース・olean署名](bulk-5inf0/core-validation.json)を根拠とする。本体の新規Leanにsorryを追加していない。

A2/AnimatedAlgebraはファイル全体の型検査が成功し、同じソースから隔離したモジュールのoleanも生成できた。draftの既存の未証明部分は残る。Notation8.1の切り出しも現在の本体をimportして成功した。基盤SheafConditionは、古い名前への参照を順に直している段階で、成功に含めていない。型検査はLakeの実設定（maxSynthPendingDepth=3など）をJSONから引き継ぎ、本体やdraftsの検査条件を緩めていない。

B03ではPrismOver.essentiallySmallを濃度の下限なしに証明し、二つの利用側のEssentiallySmall仮定を外した。環同型の移送・有界性の移送と圏同値は同じ小監査で確認した。B02の有界性は、既存のprism上のねじれ評価を直接使う。B01の平坦性は既存の完全平坦性APIに合わせ同じ宇宙で定義し、siteの述語は略記になった。B04の大きい完全siteと誘導位相、B05の二述語、B07の二述語と旧名の互換略記も同じ検査に入っている。5段の層の新しい違反0、基準から存在する節順序15辺は全く同じ集合（[比較](bulk-5inf0/core-layer-comparison.json)）。既存の例外は増やしていない。

中間の行数は追加1,198・削除1,569、合計2,767行（段0の上端5,550行の半分付近）。残りはdraft依存の整理とAPI追従の型検査で、修正量は暫定2,000〜4,000行。累計が当初上端を越える可能性はあるが、外枠11,100行を変更しない。新しい数学の構成や範囲外の作業が必要になった場合は止めて報告する。

A07の冒頭の更新はA0〜A9の40本だけに限定せず、保護対象を除く全56本のdraftを対象にした。Shared/EInfinityPowerOperationの全体とA4の保護節は維持している。基盤を含むimport先の欠落は静的に0件。ここでコミットするLeanは検査済みの本体・利用側・A2と小監査で、未検査のdraftsの修正は引き続き作業木で検査する。


### 共有鍵の待機ループの競合修正（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。S1の次の検査は鍵の取得前に待機ループの例外で止まり、Leanは未実行だった。期限の判定とsleepの引数計算の間に時刻が進むと負の待機時間になっていた。待機時間を0以上に制限するだけの修正とし、整理券の順序・鍵の規則は変更していない。実際のループを境界時刻で動かす回帰テストは旧版で1件失敗、修正後は4件成功。`zsh -n`も成功。修正は独立コミットにし、他レーンへの配布は調整役に委ねる。


### 5∞-0 の静的追従と検査順（11-14昼、検査継続）

一覧：済み 8／全体 14（うち追加 0）。[厳密な宣言名の追従台帳](bulk-5inf0/qualified-reference-refresh.json)は19本80箇所。所有元つきの対応表にある宣言名だけを使い、曖昧な名前・open・文字列・宣言の見出しは自動変更していない。保護節とShared/EInfinityPowerOperationは変更していない。A8の削除済みStratificationへの記述と直接importも本体に揃えた。

[A0〜A9の静的集計](bulk-5inf0/current-draft-inventory-summary.json)は40本、sorry 584（基準705）、本体と完全修飾名が重なる候補0（基準117）。型の同一性や全件のLean成功をこの集計だけで主張しない。現在のLean差分は追加1285・削除1650、合計2935行。外枠11,100行と、残り2,000〜4,000行の暫定見込みは変更しない。

[隔離配置の依存案](bulk-5inf0/draft-staging-plan.json)は57本231辺、循環0。冒頭の依存コメントとREADMEの順序を根拠とする案で、型検査中に不足があれば修正する。保護された1本と変更しない補助ファイルも前提の点として含む。型検査は元のソースを一時ライブラリに複製し、指定したdraftのpublic importだけを足す。本体のrootにdraftを追加しない。ソースと依存の署名を保持する再現用スクリプトを用意し、次の束で実行検証する。現在は鍵の取得前で、S1の再検査はまだ未実行。


### 5∞-0 のdraft検査・第7束（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。通常のbulk整理券で、鍵を取得してから280秒以内の束を実行し、返却した。Sheaves/SheafCondition、DerivedGeneral/CompletionFunctor、Shared/CosimplicialCupProduct、A5/RootAdjunction、A8/W13AssemblyInputsの5本が成功。先のA2/AnimatedAlgebraと合わせ、全体のLean型検査が通ったdraftは6本。既存のsorryを解消済みという意味ではない。Sheaves/SetSections・GlobalSections・CechConerveLimitの3本は失敗として記録し、型検査の範囲を減らさず修正を続ける。[全8本の検査記録](bulk-5inf0/draft-block07-validation.json)と各生ログを保存した。

再現用[check_draft.py](bulk-5inf0/check_draft.py)をこの束の実行に使った。元のimportとLakeのoptionsを引き継ぎ、draftの前提だけを隔離配置へpublic importする。ソース・一時配置・olean・前提の署名を記録する。依存が後から変わった成功記録は使わない。S1の利用側3本の次の束と、完備化の利用側を、返却後に一つだけ並べ直した。

削除前後の全宣言名の照合で、機械的な削除範囲が隣の未重複のdraft補題2本（isAlmostConnective_completedFilteredColimit、perfectoidization_quotient_connective_of_ih）まで広がっていたことを検出した。両方の元の主張・未証明本文を復元した。CrystallineSiteでも空になったCrysOverの名前空間とcutoff変数の境界が残り、RΓ側3宣言の名前が変わっていたため、元の外側のscopeと明示的κを復元した。これらは未コミットのdraft修正の段階で見つかったもので、検査済みとしては数えていない。sorryの静的数は復元前584から増えるので、次の再集計値で更新する。


### 5∞-0 の削除範囲の再照合（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。[削除・置換の全件台帳](bulk-5inf0/declaration-disposition-audit.json)を作り直した。A0〜A9の名前つき宣言は1080→957、削除123名＝同名の本体の候補117名＋指示に沿った別名の置換6名。予定外の削除・改名0、新しい名前0。2本の未重複補題とRΓの3名の復元後に照合した。sorryは **705→586**。前節の584は復元前の静的数であり、この値に更新する。

[旧ルート名の追従台帳](bulk-5inf0/root-reference-refresh.json)を追加。単体集合の固有名は所有元つき対応表に合わせ、一般的なHasLimit・HasColimitは使用箇所を確かめたものだけを直す。型検査で残ったIsPresentableの曖昧さは、元から指定されているHTTの定義への完全修飾で解消する修正とした。Čech形状はΔのnerveがSSet.{0}にあることを反映し、同じrightOpのnerve写像を単体ごとに書いた。圏同値のunit/counit・錐の表示・端点移送の法則の証明も既存APIへ追従中で、新しい数学的な仮定は加えていない。端点移送の局所補題は `∀ {x x' y : E₀} (h : x = x') (e : Edge x y), ((h ▸ e).toTruncated).edge = e.toTruncated.edge` で、既存の構成の法則の証明分割（未検査、一覧の追加項目ではない）。

現在のLean差分は追加1829・削除2135、合計3964行、外枠11,100行。禁止3ディレクトリと保護されたSharedファイルの差分0、`git diff --check`も成功。第8束は通常のbulk整理券で待機しており、成功に算入していない。


### 5∞-0 のdraft検査・第8〜9束（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。第8束はGlobalSections・CechConerveLimitの2本が成功、第9束はScalarRestriction・Truncation・AnimatedDomainの3本が成功。全体の型検査が通ったdraftは計11本。既存の未証明部分は維持する。成功した5本をこの区切りでコミットする。[第8束](bulk-5inf0/draft-block08-validation.json)・[第9束](bulk-5inf0/draft-block09-validation.json)の全対象と各回の署名・成否を保持した。個別ログは再実行で更新するため、第9束の生ログをこの時点で保存した。鍵は各束の終了時に返却し、一束は280秒以内とした。

係数制限は旧sifted名の完全修飾、Truncationは旧pt射影3箇所をMathlibのHomotopyCategory.objEquivへ、AnimatedDomainは既存の評価環射・R線形性と離散埋め込みの合成の定義展開を直したもの。いずれも新しい数学的仮定・構成を追加していない。SetSectionsは第8〜9束で同じ旧版の診断が残り、第9束の採取後に入った最新修正はまだ検査前（署名が異なる）で、成功には算入していない。

次の前線はPrismaticSite・Shared/DeRhamPolynomial・Shared/Descendable。前者はCoverage.coverings・旧∞圏名、後二者は名前空間と旧pt射影の診断。A2で3宣言の所有元がimportの閉包に入っていなかったので、現在のソースから確かめた2モジュールを直接importした。古い対応表のmodule欄にはその後の分割前のパスが残るため、所有元の確認は現行ソースで行った。再検査した所有元の到達性は欠落0（型検査そのものではない）。


### 5∞-0 のdraft検査・第10〜11束（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。第10束はPrismaticSite・Shared/DeRhamPolynomial・Shared/Descendable・PrismaticEnvelopeの4本、第11束はSetSections・A0/W15K1/AuditK1の2本が成功。全体の型検査が通ったdraftは計17本（最後の補助監査ファイルを含む）。この6本もソース署名を照合してコミットする。[第10束](bulk-5inf0/draft-block10-validation.json)・[第11束](bulk-5inf0/draft-block11-validation.json)に、失敗と依存待ちの未実行分を含めて記録した。置き換わった個別ログは置き換わったことを記録し、別の回のログを誤って添付しない。各束の終了時に鍵を返し、一束280秒以内を維持した。

SetSectionsでは篩の元の圏とOverの充満部分圏の反対圏の同値、そのunit/counit、表現可能な指定錐、端点を移した同じ辺の可逆性の法則が通った。追加の数学的仮定は使わず、既存の構成の法則の証明と定義展開を直した。PrismaticSiteはCoverage.coverings、移動済みD(A)の正式名へ追従。未証明の `prismaticCohomologyFrobenius` は、既存の係数制限APIに合わせ `E : EInfinityTheory` を明示引数に取り、`Edge Δ ((E.restrictD φ).app _ Δ)` を返す型とした（その本体のsorryは保持、ほかのRΓ定義にEを加えていない）。共有de Rhamはdraftの既存の完備化と離散埋め込みの名前空間を明示した。旧pt射影の残り8箇所も標準のobjEquivに揃え、うちdescendabilityの4箇所はここで型検査が通った。

次の前線はFlatDescentとSheafGenerators・SpaceValued。局所instance、docstringのコマンド上の位置、presentabilityの完全修飾、既存の補助定義の公開範囲とprojectionの参照を修正し、第12束を通常のbulk整理券で一つだけ並べた。CAlgValued・CosimplicialEInfinity・CechAlexander・BaseChangeは、前提が成功した順に検査する。


### 5∞-0 のdraft検査・第12〜14束（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。第12束でFlatDescent・SheafGenerators、第13束でSpaceValued・CAlgValuedが成功。第14束でCechConerveLimitとCAlgValuedを依存更新後に再検査し、CechAlexanderも成功。現在のソース・前提・oleanの署名で数える有効な成功は22本。依存を変更した古い成功を除く[集計器](bulk-5inf0/summarize_drafts.py)を追加した。[第12束](bulk-5inf0/draft-block12-validation.json)・[第13束](bulk-5inf0/draft-block13-validation.json)・[第14束](bulk-5inf0/draft-block14-validation.json)を保存。各束は通常のbulk整理券・280秒以内で、終了時に鍵を返した。

Čechの問題は、同名の本体宣言が返すCategoryTheory.CechNerveDataと、draftの別構造体Sheaves.CechNerveDataの違いだった。両者のobj・proj・isLimit・proj_mapと弱終性の定義を比較し、完全に同じ内容であることを確かめた。新しい構造の移送は作らず、draft側の2宣言を本体へのabbrevに一本化した。既存の名前を残し、本体のČechデータをそのまま使う。変更したCechConerveLimitと利用側CAlgValuedを再検査して成功し、CechAlexanderも本体の引数順に合わせて成功した。

SpaceValuedは既存のkanDiscretePresheafInclusionを公開してexposeされたラッパーから使えるようにした（型・元のsorry本文は同じ）。押し出し境界の反射律とprojectionの正式名、層の名前空間、presentabilityの曖昧さ、局所instance・docstringの位置も修正した。ここでコミットする6本はいずれも現在の署名で検査済み。共有Totの評価とBaseChangeの残りを修正し、第15束で検査する。


### 5∞-0 のdraft検査・第15束と全体のsorry（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。第15束でA0/BaseChangeが成功し、現在の署名での有効な成功は23本。[第15束](bulk-5inf0/draft-block15-validation.json)を保存し、BaseChangeをコミットする。残る前提はShared/CosimplicialEInfinityの評価比較1箇所。ホモトピー後合成の端点・空の相対条件、cdgaの忘却、層の名前空間は同じ検査で通った。評価の比較にはCatの射のtoFunctorとTypeの合成の公開評価補題を追加し、第16束に並べている。新しい数学的仮定や未証明本文は足していない。

[保護対象以外の全体の集計](bulk-5inf0/all-draft-sorry-summary.json)は56本中55本が変更、sorryは **819→698**。A0〜A9の40本だけの値は **705→586**。全体の値と部分の値を区別する。現在のLean差分は追加2217・削除2486、合計4703行（外枠11,100行）。残りの見込み2,000〜4,000行は暫定のままで、外枠は増やさない。


### 5∞-0 の第16束と保護された前提（11-14昼）

一覧：済み 8／全体 14（うち追加 0）。[第16束](bulk-5inf0/draft-block16-validation.json)は共有Totの評価比較1箇所で失敗、後続5本は依存待ちで未実行。Catの射のラッパーは解消したが、ホモトピー圏への写像とnerveの零単体の表示が残った。既存の定義で同じ対象であることを明示する修正を第17束で検査中。現在の有効な成功は23本のまま。失敗したソースはまだコミットしない。

保護された前提 `Shared/EInfinityPowerOperation.lean` に、存在しない旧モジュール `SerrePositivity.InfinityCategories.Project.DerivedCategories.Homology` のimportが残っていることを静的に確認した。A4の検査前提だが、指示§1の変更禁止に従いソースを維持している。⑤a側での追従またはimport・改名だけの例外の判断を依頼した。この保護対象を一時的な互換モジュールで隠して成功と数えることはしない。他の独立した検査を先に進める。


### 5∞-0 の保護対象の例外（11-14午後、§5）

一覧：済み 8／全体 14（うち追加 0）。調整役の§5の例外承認を受け、全draftのimportとB3の一意な完全名を対応表で再走査した。残りの機械的な変更は **Shared/EInfinityPowerOperation.lean:8 のimport 1行**：`…Project.DerivedCategories.Homology` → `…Project.DerivedCategories.MappingAndStability.HomSpaces.Homology`。変更の全行は[台帳](bulk-5inf0/section5-protected-mechanical-edits.json)に保存した。主張・型・証明とA4のP⁰部分は変更していない。保護されたSharedファイルの変更禁止の例外はこの1行のみで、まだ全体の型検査は未実行。前節の前提のimport欠落は解消した。

第17束は共有Totのnerveの零単体の評価表示で失敗し、後続は未実行。[結果](bulk-5inf0/draft-block17-validation.json)を保存した。零単体の評価は定義上の等しさではなく `nerveMap_app_mk₀` の等式で揃える必要があるため、その等式を明示して第18束へ進めた。独立したArcRouteBと補助界面も同じ280秒以内の束に含めた。


### 5∞-0 のdraft検査・第18束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第18束](bulk-5inf0/draft-block18-validation.json)でArcRouteBが成功し、有効な成功は24本。ArcRouteBの型・既存の証明を変えず、B3で移った3モジュールのimport追従をコミットする。補助のShared/BarrattEcclesTheoryは本体の組み立て関数が供給済みのP⁰四欄をまだ引数に渡していて失敗した。重複する4引数だけを外し、残る十七欄を維持する修正を第19束で検査する（本体EInfinityの変更はない）。共有Totは零単体の評価の等式を明示したことで同型の合成まで通り、最後の二つのホモトピー圏の表示の展開が残った。既存のbridgeと頂点ホモロジーの定義を展開する修正を同じ束に入れた。まだ成功とは数えない。


### 5∞-0 のdraft検査・第19束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第19束](bulk-5inf0/draft-block19-validation.json)で補助のShared/BarrattEcclesTheoryが成功。有効な成功は25本。既に本体が供給するP⁰・零次・正次数・離散比較の4引数を外しただけで、残る十七欄は維持した。新しい実例を無条件に作る変更ではない。この検査済みソースをコミットする。保護対象以外の56本は全部が変更され、sorryは **819→694**（4欄の重複の削除を反映）。保護されたSharedの1行のimport追従は、この56本の外で別に記録している。共有Totの最終比較はEquivalence.mkのinverseを明示展開する必要が残り、第20束で検査中。


### 5∞-0 の保護対象の完全名（11-14午後、§5）

一覧：済み 8／全体 14（うち追加 0）。Shared/EInfinityPowerOperationの旧open下の参照も、所有元つきKL/B3表を合成して確かめた。**54・55・70・80・128〜130・151・152・157行の10参照**を、同じ宣言の新しい完全名に機械的に置き換えた。元のopen・宣言名・束縛変数・証明の手順・仮定は維持し、変更箇所を[同じ台帳](bulk-5inf0/section5-protected-mechanical-edits.json)に追加。importの1行を含めて計11参照。A4のP⁰部分は一字も変更していない。Shared全体の型検査は前提待ちであり、この改名以外の修正は許可範囲に入れていない。

[第20束](bulk-5inf0/draft-block20-validation.json)・[第21束](bulk-5inf0/draft-block21-validation.json)は同じ共有Totの最後の表示の等式で失敗、後続へ進んでいない。`simp`が圏同値・切断版のラッパーを一括で評価しないため、頂点のホモロジーの同じ定義を局所等式として示す形で第22束を検査する。成功は25本のまま。


### 5∞-0 のdraft検査・第22〜23束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第22束](bulk-5inf0/draft-block22-validation.json)の局所等式は証明が終わっており、残った余分なrflだけで失敗した（検査したソースはその後の修正とは別署名）。[第23束](bulk-5inf0/draft-block23-validation.json)でShared/CosimplicialEInfinityと、改名だけを直した保護対象Shared/EInfinityPowerOperationの2本が成功。一度は27本の成功に到達したが、A2で本体のCosimplicialAlgebraとdraftの同名定義の衝突が判明した。本体HomologicalAlgebra.Cosimplicial.Algebraの型は同じ `CosimplicialObject (Under (CommRingCat.of A))` なので、draftの重複定義を外して本体を直接importした。共有Totの再検査・その依存の再検査を第24束で行い、旧成功はその間集計から外す（有効25本）。既存の全証明は維持しており、保護対象の型・証明の変更はない。

B03の本質的小ささの本体補題はκの下限を仮定しないので、A2/DerivedPrismaticCohomology・A3/DiscreteCase・A5/PerfectSiteに残る古い追加引数を外して同じ本体補題を使った。前二者のうちA2とA5にあった濃度のsorry2個が不要になった。これらのdraft全体はまだ未検査で、成功に算入していない。


### 5∞-0 のdraft検査・第24束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第24束](bulk-5inf0/draft-block24-validation.json)で本体のCosimplicialAlgebraに揃えたShared/CosimplicialEInfinityが成功し、依存を更新したShared/EInfinityPowerOperationも成功。有効な成功は27本に戻った。共有Totの検査済みソースをコミットする。A2はimportを通過し、structurePresheafの不要なE引数、結果の型が未指定のpolyTestFrobenius、discreteEvaluationのカーネル時間切れ、逐次図式の1単体の添字の4種類が残った。後続はまだ成功に算入していない。

全draftを本体の宣言名と静的に再照合し、残る同名候補はShared/DeRhamPolynomialのdeRhamCohomologyWedgeの1件のみだった。署名が同じことを確かめ、本体への一本化を次の検査で確認する。同名だけで数学的な等しさを主張するものではない。


### 5∞-0 の全件台帳の補足（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[削除・置換台帳](bulk-5inf0/declaration-disposition-audit.json)に共有部分の2件を別表として追加した。A0〜A9の削除123名の表はそのままにし、共有のCosimplicialAlgebraとdeRhamCohomologyWedgeを混ぜて数えない。後者は第25束の検査待ち。対象の本体ディレクトリを再走査した[同名候補](bulk-5inf0/current-draft-duplicate-candidates.json)は0件（構文による候補の検査であり、型検査ではない）。[所有元へのimport到達性](bulk-5inf0/section5-owner-import-reachability.json)も保護対象を含め欠落0件。

[保護対象の再構成](bulk-5inf0/section5-protected-reconstruction.json)では、基準efa846fe8に台帳の11置換だけを適用した結果が現在のSharedファイルと完全に一致し、A4のP⁰部分も基準と完全に一致した。許可された改名以外の変更はない。


### 5∞-0 のdraft検査・第25束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第25束](bulk-5inf0/draft-block25-validation.json)でShared/DeRhamPolynomialが成功。本体のdeRhamCohomologyWedgeを直接使う型で通ったため、共有の2件の重複を外したことを全件台帳にも反映し、検査済みソースをコミットする。有効な成功は27本。全56本のsorryは **819→691**、A0〜A9は **705→584**（本質的小ささの濃度の未証明2個が本体の証明に置き換わった分を含む）。復元した未重複補題2個は保持している。

A2は280秒の束の残り時間内に完了せず、外側のgtimeoutで打切り（exit124）。成功にも通常の型エラーにも数えない。完了したde Rhamの署名つき記録とA2の未完了ログを別に保存し、鍵は上限で返した。局所の有限の検査予算を増やす方法では時間内に終わらなかったため、通常の予算に戻し、7つの中間の関手・辺の既存の結果型を明示する修正を第26束で検査する。仮定・数学的な入力・未証明本文は増やしていない。


### 5∞-0 のdraft検査・第26束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第26束](bulk-5inf0/draft-block26-validation.json)は約110秒で終了し、鍵を返却。A2の通常の型エラーは解消し、`discreteFrobeniusComponent` のカーネル時間切れ1原因と、その定数が登録されないことによる下流エラーが残った。辺を関手の頂点で評価した端点を、評価後の頂点へ揃える計算に集中している。

既存の `evaluateFunctorAt_functorVertex` から始端・終端の等式を作り、同じ辺のmapをその等式で移送する形に分割した。新しいFrobenius・仮定・数学的入力は作らず、既存の構成の端点の法則だけを明示した。通常の検査予算で第27束を検査中。有効な成功は27本のまま。


### 5∞-0 のdraft検査・第27〜28束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第27束](bulk-5inf0/draft-block27-validation.json)ではカーネル時間切れが消え、約39秒で端点のTypeの合成の評価2箇所に絞られた。同じ合成を定義から評価して[第28束](bulk-5inf0/draft-block28-validation.json)でA2/DerivedPrismaticCohomologyが約33秒で成功。有効な成功は28本。この検査済みソースをコミットする。有限の検査予算を増やすオプションは残していない。既存の辺の評価の始端・終端を公開補題で揃え、同じmapを等式で移送したもの。新しいFrobeniusや仮定は導入していない。siftedの述語2参照も[所有元の完全名](bulk-5inf0/a2-sifted-predicate-reference-refresh.json)へ追従して通った。

A1/HodgeTateMapは `import all …Prismatic.HodgeTateOneDerivative` の旧パスが1行残っていて失敗。静的import解析が `import all` を拾っていなかったため、前の「import欠落0」はこの構文を除く範囲での値だった。全draftのimportをこの構文も含めて再走査し、[残る1行](bulk-5inf0/import-all-reference-refresh.json)をB3表の正しいパスへ直した。importの種類は維持。第29束でA1と後続を検査する。


### 5∞-0 のA3のsection変数の復元（11-14午後、調整役承認）

一覧：済み 8／全体 14（うち追加 0）。`universalLciPrism` のsection変数h₀がsorryのため型から落ちていることを確認。調整役よりD4-03・D4-06と同じ「意図した型に戻す」扱いとして承認を得た。[型と全参照の台帳](bulk-5inf0/a3-boundedness-decision.json)のとおり、`universalLciPrism P₀ h₀ r` として14参照を追従し、それでh₀が必要になるlciClassifyingMap・lciMapの呼出し3箇所にも同じ引数を明示した。環・δ構造・生成元のソースは同一で、正則性を既存のcompletedFreeDelta_generator_regularから証明する。p完備性・生成元完備性・pのイデアルへの所属・剰余の有界性の4欄も、追加の仮定を入れずに本体へ寄せた。A3全体は前提待ちで未検査なので、まだ成功に算入していない。

同じ理由で型から落ちているsection変数は、調整役の承認に従い同じ扱いで戻し、今後も一覧に残す。新しい数学的な入力を追加する変更はこの扱いに混ぜない。


### 5∞-0 の本体全域での同名確認（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[全域の静的な同名候補](bulk-5inf0/all-main-draft-duplicate-candidates.json)は本体の32,937ファイルを走査して0件。前の対象ディレクトリ限定の検査を本体全域へ広げ、aliasも構文走査に含めた。構文上の名前の候補の検査であり、型の一致やLean環境による照合の代わりではない。`import all`を含め直した[所有元へのimport到達性](bulk-5inf0/section5-owner-import-reachability.json)も欠落0件だった。

A3はソース上ではDiscreteCaseが23→13、LciAndQuasiregularが30→14、計53→27のsorry。環・生成元を変えず、26箇所を本体の既存の古典的な芯とその法則へ寄せた。A3全体の型検査は前提待ちなので、この数だけを根拠に完了とはしない。対応先の[一覧](bulk-5inf0/a3-classical-followup.json)と、意図した[文脈の引数](bulk-5inf0/restored-context-parameters.json)を保存した。


### 5∞-0 のdraft検査・第29束とpd関手の型の相違（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第29束](bulk-5inf0/draft-block29-validation.json)でA1/HodgeTateMapが約32秒で成功し、有効な成功は29本。EInfinityTheoryを使うCAlg部分だけに同じ引数を渡し、古典部分の型は維持した。CrystallineInputは、落ちていたpのsection変数・Theory実現の引数・pd関手の本体版との仮定の違い・不透明な列の定義の照合が残った。

**削除候補の訂正**：[元のpdPolynomialFunctor](bulk-5inf0/pd-functor-restoration.json)は任意の係数環kを受けるが、本体版にはγ・hp・hk・hregの追加仮定がある。同じ型ではなかったため、元の構成と既存の3つのsorryを `pdModelPolynomialFunctor` として復元し、CrystallineInput・CrystallineSite・DeRhamComparisonPolyの参照を直した。一般の型へ本体の強い仮定を黙って足さない。[全件台帳](bulk-5inf0/declaration-disposition-audit.json)は同名本体への置換116、別の置換6、旧型を保った改名1に訂正（旧名123件、削除122・改名1、未説明0）。

formsCAlgは同じ厳密なformsCDGAFunctorを、選んだTheoryのcdga実現で読む形にした。旧Barratt–Eccles固有のformsBEFunctor・formsNerveは保持し、未証明のcdga構成を変えていない。pdDeRhamCDGAでsorryのため落ちたpも明示した。列と双複体の既存の定義の照合には、本体の3モジュールをimport allで読み、Mainのソースを変更しない。いずれも第31束で未検査。

[第30束](bulk-5inf0/draft-block30-validation.json)は準備処理が元ソースのmap_compの抽出で失敗したため修正前のままになり、既に失敗した同じソースを検査器が除外してLean対象0件で終了した。成功として数えない。抽出を訂正して復元を適用してから、第31束を並べた。


### 5∞-0 のdraft検査・第31〜35束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。第31〜34束の診断を受け、不透明な列の定義の照合をprivateな法則の証明へ分け、同じ列の包含を等式で移送した。[第35束](bulk-5inf0/draft-block35-validation.json)でA1/CrystallineInputが約41秒で成功。有効な成功は30／57本。A1/HodgeTateMapも第29束の成功と現在のソースのSHAの一致を確認し、この2本をコミットする。定理の追加仮定・検査予算の引上げ・本体の変更はない。pdModelPolynomialFunctorは元の一般の型と既存の3つのsorryを保持する。残るHodgeTateComparison・CrystallineSiteは失敗として証跡を保存し、修正を続ける。

READMEも現在の本体への追従・隔離した型検査の手順・保護対象の例外を反映した。型検査の成功は、残された将来のsorryの証明の完成とは区別する。


### 5∞-0 のdraft検査・第36〜37束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第37束](bulk-5inf0/draft-block37-validation.json)でA1/HodgeTateComparisonが約26秒で成功し、有効な成功は31／57本。普遍prismの宇宙を標的と揃え、本体のKoszulホモロジーの作用のinstanceと、その台の加群を区別して同じ底変換の型を記述した。Eとpの既存の引数も渡した。成功したソースをコミットする。

[現在のソース上のsorry](bulk-5inf0/all-draft-sorry-summary.json)は、保護されたSharedを除く56本で819→679、A0〜A9は705→572。未検査の変更を含むため完成の数とはしない。Leanの追加・削除の計は5,137行（第36束後の測定）、外枠11,100行。

CrystallineSiteは元からあったR̄という結合文字つきの識別子をコードだけRbarに直し、本文の表記は維持。0宇宙の添字圏のnerveは同じ関手の射列ごとの合成で持ち上げた。sorryのため落ちていたhp・hgenも[引数の台帳](bulk-5inf0/restored-context-parameters.json)に加え、承認された規則で意図した型に戻す。これとHodgeTateFiltrationは未成功で、続く束で検査する。


### A3 の意図した引数の復元の保存確認（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[ソースの保存確認](bulk-5inf0/a3-restored-parameter-source-guard.json)で、環の略記・δ構造・生成元の式が基準efa846fe8と同一であることを確認した。事前に一覧にした14参照へh₀を渡している。現ソースには、既存の普遍性を用いるlciClassifyingMapの証明に明示したHomとその生成元の法則の2出現を加えて16出現ある。正則性は承認どおりcompletedFreeDelta_generator_regularから得る。全A3の型検査は前提待ちなので、まだ成功には加えない。


### 5∞-0 のdraft検査・第38束（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[第38束](bulk-5inf0/draft-block38-validation.json)でA1/CrystallineSiteが約46秒で成功し、有効な成功は32／57本。本体のpdCechNerveの変数の宇宙に合わせ、有限変数をULiftで持ち上げ、変数の対応はj↦j.downと明示した。hp・hgenを意図した引数に戻した型も通った。検査済みのソースをコミットする。

更新後の本体全域の同名候補0、import allを含む所有元への到達の欠落0、57本から旧E3入力への経路0（閉包12,938モジュール）をPythonで再確認した。HodgeTateFiltrationは、旧loopFunctorが通常のホモトピー圏の関手だったため、同じ既存のloopDiagramTargetEquivalenceの逆射と左下の評価を合成する∞関手へ参照を合わせる。ほかはYonedaの定数の法則・letのスコープ・合成の括弧の明示で修正し、第39束で検査する。新しいloopの存在定理・仮定・sorryは加えない。


### 第39束の待ち時間中の後続の準備（11-14午後）

一覧：済み 8／全体 14（うち追加 0）。[全57本の状態](bulk-5inf0/draft-validation-after38.json)を第38束時点で保存した。成功32、修正後の再検査待ち1、未実行24。成功行には現在のソース・成果物のSHAを付け、元の古い形式のreceiptに成果物のSHAがなかったものはその区別も残した。A4のP⁰の保護領域は基準とバイト単位で同一と再確認。

DeRhamComparisonPolyの[23参照](bulk-5inf0/de-rham-universal-specialization-followup.json)は、本体のUniversalWittComparisonの既存の普遍基底の特殊化へ合わせる準備をした。正則性・完備性はその本体版の中で証明済みのものを使い、draftへ強い仮定を足さない。ほかに[所有元が確定した5参照](bulk-5inf0/remaining-unqualified-reference-refresh.json)を完全名へ直した。これらのソースは前提待ちで未検査のため、まだコミットも成功への算入もしていない。変更量はこの時点で追加・削除計約5,200行、外枠11,100行。

一時の束の実行器は、同じ走査内の依存署名の判定を再利用するだけのメモ化を加え、各Lean実行の前には全判定を取り直す。検査器本体と署名の一致条件、280秒の外側の打切りは維持。共有鍵の要求は同時に1本だけで、待ち時間を検査時間や成功に数えない。


### 5∞-0 のdraft検査・第39束（11-14夕方）

一覧：済み 8／全体 14（うち追加 0）。[第39束](bulk-5inf0/draft-block39-validation.json)は約48秒でHodgeTateFiltrationが失敗。通常のホモトピー圏のloop関手と∞関手の違い・letのスコープのエラーは解消し、augmentationの始端のYonedaの評価の照合が1箇所残る。こちらの書換え処理が見出しの名前つき引数の`:=`を定義本文の区切りと誤認し、見出しを切った構文ミスもあったため、見出しを明示して訂正した。失敗として保存し、成功は32／57本のまま。

第40束は同じ280秒の鍵の範囲で、A3冒頭のprismとlciClassifyingMapまでを現ソースからそのまま抽出する検査も先に行う。これは承認されたh₀の復元と既存の古典的な法則の証明の部分検査であり、A3全体や57本の成功件数へは加えない。原本のLake設定を引き継ぎ、検査中のソースの一致を確認し、型とaxiomsの出力を別の記録に残す。


### 5∞-0 のdraft検査・第40〜42束とA3冒頭（11-14夕方）

一覧：済み 8／全体 14（うち追加 0）。[第40束](bulk-5inf0/draft-block40-validation.json)・[第41束](bulk-5inf0/draft-block41-validation.json)・[第42束](bulk-5inf0/draft-block42-validation.json)はいずれもHodgeTateFiltrationが失敗で、成功は32／57本のまま。第40束で壊れた見出しと合成の時間切れは解消し、augmentationの始端の、二切断の添字0を通常の添字0として照合する1箇所が残った。構成子と包含関手の定義を順に明示し、第43束で再検査する。

A3冒頭の[第40](bulk-5inf0/a3-prism-prefix-block40-validation.json)・[第41](bulk-5inf0/a3-prism-prefix-block41-validation.json)・[第42](bulk-5inf0/a3-prism-prefix-block42-validation.json)の部分検査も全体としては失敗。冒頭のopenが通常は後続draftのimportから継承する二つの名前空間を、部分検査には本体の二つのpublic importで明示した。原本の古典的な宣言の本文はそのまま。docstringがvariableに付いていた構文を定義へ付け直し、Typeの値を存在命題から直接casesで取り出していた箇所を、同じ存在一意性からClassical.chooseで取り出す形に修正した。第42束の残りは構成した射の局所定義を照合する1箇所。これも第43束で検査する。

部分検査の型とaxiomsの出力では、universalLciPrismが実際にP₀・h₀・rを取り、universalLciPrismとその有界性の2宣言は標準3公理だけと確認できた。ただし部分ファイル全体は失敗であり、A3全体や全57本の成功には数えていない。後続のlciClassifyingMapがエラーで登録された段階のsorryAxも、その失敗としてログに残している。


### 5∞-0 のdraft検査・第43束（11-14夕方）

一覧：済み 8／全体 14（うち追加 0）。[第43束](bulk-5inf0/draft-block43-validation.json)でA2/HodgeTateFiltrationが約25秒で成功し、有効な成功は33／57本。有限変数は同じ有限集合のULiftで宇宙を合わせ、増大余錐の脚は同じ辺の端点の定義だけを照合した。loopは本体の既存の図式の同値の逆と評価の合成、入力の単位は同じpostcompositionの恒等・結合法則で記述する。検査済みのソースをコミットする。

A3冒頭の[部分検査](bulk-5inf0/a3-prism-prefix-block43-validation.json)も約33秒で成功。[生成した検査用ソース](bulk-5inf0/a3-prism-prefix-block43-source.txt.gz)とログを保存した。universalLciPrismの型はP₀・h₀・rを受け取り、universalLciPrism・universalLciPrism_bounded・lciClassifyingMapの[axioms](bulk-5inf0/a3-prism-prefix-audit.json)はすべてpropext・Classical.choice・Quot.soundだけ。環・δ構造・生成元の式を保った承認済みの変更が、既存の完成自由δ環の補題で通った。これはA3全体の成功とは分け、一覧の完了数にはまだ加えない。

同じ束のDiscreteCaseとBaseChangeAndTensorは失敗。前者は同じ台環のFrobeniusを明示の環射型で読む照合、後者は多項式の係数変更・名前空間・神経の定数頂点の照合が残る。後者の係数変更は、本体の証明済みchangePolyを直接使う準備にした。第44束で再検査する。


### 5∞-0 のdraft検査・第44束（11-14夕方）

一覧：済み 8／全体 14（うち追加 0）。[第44束](bulk-5inf0/draft-block44-validation.json)でA3/DiscreteCaseが約41秒で成功し、有効な成功は34／57本。Frobeniusの制限先のUnder対象は同じC.rightと明示し、零次Frobeniusを同じ台環の環自己準同型という結果型で記述した。環・射・将来のmod p比較の主張は変えず、本体へ寄せた古典的な法則の証明も通った。検査済みのソースをコミットする。

BaseChangeAndTensorは、係数変更を本体のchangePolyへ寄せたこととPΣの完全名の追従は通り、神経の端点の照合2箇所が残った。nerveEquivとYonedaの逆の評価を明示し、第45束で検査する。鍵は各束の終わりに返し、次は同時に1本だけ並んでいる。


### 5∞-0 のdraft検査・第45〜47束（11-14夕方）

一覧：済み 8／全体 14（うち追加 0）。[第45束](bulk-5inf0/draft-block45-validation.json)・[第46束](bulk-5inf0/draft-block46-validation.json)の端点の診断を受け、余積の包含とYonedaの評価を順に書き換え、同じ神経の辺の始域・終域を定義上の等式で揃えた。[第47束](bulk-5inf0/draft-block47-validation.json)でA2/BaseChangeAndTensorが約39秒で成功。有効な成功は35／57本。この検査済みソースをコミットする。係数変更は本体のchangePolyを直接使い、重複していたmap_id・map_compのsorry2個を除いた。数学的な入力・仮定は追加していない。

同じ束のA4/PerfectoidizationとA3/LciAndQuasiregularは失敗。A3は同じloopを検査済みのformShift S 1で読み、普遍prism射の補題の実際の所有元の名前に合わせる。A4は保護されたP⁰節の外だけで、反復の構文・1単体の添字・pと有界性の引数・ホモトピー圏の表示を合わせる。A4の完備包含・反射・単位はA2の同じ界面を直接使う準備にした。包含は具体的で、反射の存在はA2側の従来の未証明入力のまま一つに集約する。反射の存在を新しく証明したとは扱わない。第48束で検査する。P⁰の保護領域は変更前後で同一と確認した。


### 5∞-0 のdraft検査・第48束（11-14夕方）

一覧：済み 8／全体 14（うち追加 0）。[第48束](bulk-5inf0/draft-block48-validation.json)でA4/Perfectoidizationが約41秒、A7/DiscreteCoreが約25秒で成功。有効な成功は37／57本。A4の本体への集約・明示の引数と塔の1単体・通常のホモトピー圏の表示が通った。P⁰の保護領域は基準efa846fe8とバイト単位で同一と再確認。この2本の検査済みソースをコミットする。

A3/LciAndQuasiregular・A4/InterfaceFields・A7/AnimatedPerfectoidizationは失敗。A3は、同じPD完備化環のinstanceと構造射の生成元の法則を明示し、A1から移した最後のlciの定理の元のA・P・hPの文脈を復元する。直前のh₀の[部分検査](bulk-5inf0/a3-prism-prefix-block43-validation.json)の範囲はハッシュも同一のまま。InterfaceFieldsは通常のホモトピー圏の表示とnerveMapの零単体の評価を明示する。A7は既に使うperfectoidizationFunctorの所有元がInterfaceFieldsであるため[依存表](bulk-5inf0/draft-staging-plan.json)にその1辺を補った（57頂点、循環0、既存の順序は有効）。A7の残る変更は既存の有界性を渡し、通常のホモトピー圏の脚に揃えるもの。第49束で検査する。


### 5∞-0 のdraft検査・第49〜50束、A02・A06完了（11-14夕方）

一覧：済み 10／全体 14（うち追加 0）。[第49束](bulk-5inf0/draft-block49-validation.json)の残る診断を直し、[第50束](bulk-5inf0/draft-block50-validation.json)でA3/LciAndQuasiregular全体が約48秒で成功。有効な成功は38／57本。承認されたuniversalLciPrism P₀ h₀ rの型と参照、普遍射、完全化したprismの同じ台環のinstance、最後に移したlciの系まで通った。A3の2本のsorryは53→27で、26箇所を既存の古典的な本体とその法則に寄せた。未証明の∞比較などは元の主張のまま残す。環・δ構造・生成元の式は保存。[引数の台帳](bulk-5inf0/restored-context-parameters.json)の全行も全ファイルの検査で通っている。

[項目別状態](bulk-5inf0/item-status.json)のA02をPASSに更新。またA0/BaseChange・A1/HodgeTateComparisonの二つの振幅の定義を本体HasCochainCompleteTorAmplitudeへ寄せたことと、利用側A3の型検査がそろったためA06もPASSにした。残る項目はA01・A04・A05・A07。

InterfaceFieldsは完備化単位の同じ辺の端点の補助定義自体は通り、公開された定義の本文から使うためその補助定義も公開する1箇所が残った。数学的な構成や仮定を増やすものではない。第51束で確認する。新たに実行できたDeRhamComparisonPolyは失敗で、普遍基底に特殊化した本体の引数・実際の所有元の依存・評価の照合を続ける。


### 5∞-0 のdraft検査・第51束（11-14夕方）

一覧：済み 10／全体 14（うち追加 0）。[第51束](bulk-5inf0/draft-block51-validation.json)でA4/InterfaceFieldsが約40秒、A7/AnimatedPerfectoidizationが約25秒で成功。有効な成功は40／57本。完備化単位の同じnerveの辺は端点を明示する補助定義へ分け、公開される界面から使える公開範囲にした。新しい数学的構成ではなく、以前の式の型の照合の分割である。A7の有界性は既存のperfectPrism_boundedを渡し、脚は通常のホモトピー圏の表示へ揃えた。補ったInterfaceFieldsへの依存も実際の型検査で通った。この2本の検査済みソースをコミットする。

同じ束のPerfectSiteとAlmostConnectivityは失敗。PerfectSiteは元の余積の反復を同じNat.recで明示し、脚も同じ依存再帰で書く。構成する対象・射・未証明の法則は変えない。AlmostConnectivityはD3の二切断のホモトピー圏の対象のptから同じ頂点を読む。第52束で検査する。


### 5∞-0 のdraft検査・第52〜53束（11-14夜）

一覧：済み 10／全体 14（うち追加 0）。[第52束](bulk-5inf0/draft-block52-validation.json)でA5/PerfectSiteが約39秒、A8/AlmostConnectivityが約22秒で成功。有効な成功は42／57本。前者は元の有限余積の反復と指定された脚をNat.recで明示し、後者はD3の二切断のホモトピー圏の対象のptから同じ頂点を読んだ。通常のホモトピー圏の脚への照合も通った。この2本の検査済みソースをコミットする。

SemiperfectoidCaseは第52束で失敗し、有界性の既存の証明・includeとdocstringの配置・公開された値の選択で使う存在定理の公開範囲・ホモトピー圏の表示を合わせた。[第53束](bulk-5inf0/draft-block53-validation.json)ではそれらが通り、根の変数の改名を商へ降ろすIdeal.quotientMapₐの引数の推論1箇所が残った。係数環・両イデアル・同じ改名写像を明示して第54束で検査する。元の未証明の理想への包含の主張を変えず、新しい仮定やsorryは追加していない。


### 5∞-0 のdraft検査・第54〜55束と型の違う対応の訂正（11-14 19時台）

一覧：済み 10／全体 14（うち追加 0）。[第54束](bulk-5inf0/draft-block54-validation.json)でA5/SemiperfectoidCaseが約42秒で成功。有効な成功は43／57本。根の改名の商の射は同じ係数・イデアル・写像を名前つき引数で明示した。検査済みのソースをコミットする。

DeRhamComparisonPolyの[型の相違の台帳](bulk-5inf0/de-rham-original-contract-retention.json)：本体wittToSmallの終域はγ・hp・hk・hregを持つ条件付きpdPolynomialFunctor、元の普遍基底のdraftの終域は保持した一般pdModelPolynomialFunctorであり、同じ型ではなかった。元からあるwittToSmallとwittToSmall_frameを、それぞれuniversalWittToPdModel・universalWittToPdModel_frameとして元の2つのsorryとともに保持する。新しい比較仮定や証明済みという扱いは加えない。cechAlexanderFrameは本体の低水準の関数そのものではなく、既存のaffineCechAlexanderFrameへ特殊化する。[全件台帳](bulk-5inf0/declaration-disposition-audit.json)は113の同名所有元・7の別名への置換・3の旧型を保った改名、計123、削除120・改名3・未説明0に訂正した。

そのほかの普遍基底の正則性・完備性は既存の証明を渡して本体へ特殊化する。theoryFormsCAlg等の実際の所有元はCrystallineSiteなので[依存表](bulk-5inf0/draft-staging-plan.json)にその1辺を追加（循環0、既存の順序は有効）。未定義だった零形式の旧名は、既存の零形式・完備化単位・複体延長の同型の同じ合成を型を付けて読む準備にした。まだ全体は未検査。

[第55束](bulk-5inf0/draft-block55-validation.json)はpublic import allというこちらの書式ミスで本文の前に失敗。public importとimport allを分け、第56束に並んだ。残る普通のホモトピー圏と辺の表示の[6参照](bulk-5inf0/remaining-ordinary-homotopy-edge-refresh.json)も、VertexIso・FunctorHomと組み合わせている同じ辺を揃える準備だけをし、未検査と明記した。

現在のLeanの追加・削除の計は5,426行。段0の当初の見込み上端5,550行に近づいているが、外枠11,100行の内側である。残る項目はA01・A04・A05・A07で、新しい数学の項目は追加していない。


### 5∞-0 のdraft検査・第56〜57束（11-14夜）

一覧：済み 10／全体 14（うち追加 0）。[第56束](bulk-5inf0/draft-block56-validation.json)の診断を分け、第57束で普遍prismの正則性を乗法の単射性として明示し、p完備剰余環でpと互いに素な整数が単元になる既存の証明を同じ引数で記した。本体の非公開名を直接使うのをやめた。零次形式は既存の完備形式・複体延長の同型で読み、非公開の定義を展開する範囲だけno_exposeとした。関手の合成の等式は局所的な略記を明示して結合律で揃えた。新しい比較仮定・数学の項目・sorryは加えていない。

[第57束](bulk-5inf0/draft-block57-validation.json)で、これらとzigzagの部分は通った。ファイル全体はrootFormsAugmentationの二つの端点の照合で失敗。nerveの零単体の評価と同じ形式関手の頂点を定義上の等式で揃え、第58束で再検査する。有効な成功は43／57本のまま。Leanの追加・削除は5,460行で外枠11,100行の内側。


### 5∞-0 のdraft検査・第58〜59束と静的な再確認（11-14夜）

一覧：済み 10／全体 14（うち追加 0）。[第58束](bulk-5inf0/draft-block58-validation.json)と[第59束](bulk-5inf0/draft-block59-validation.json)でもrootFormsAugmentationの端点の照合が残った。第60束では零単体の添字を明示し、nerveMap_app_mk₀の等式をcongrArgで渡す形で確認する。他の部分は第57束と同様に通り、未説明の失敗を成功には数えていない。

[静的再確認](bulk-5inf0/draft-static-block60.json)：本体32,937ファイルと全57draftsの公開名の重複候補0。draftsとその前提のimportグラフ12,939頂点で、旧Inputs.Perfectoidization・Inputs.PerfectoidizationInterfaceへの経路0。A0〜A9のコード中のsorryは705→569、ファイルごとの増加0（未検査のソースも含むので完成の数値ではない）。全57本の現在のsorryは684。A4のP⁰節は基準とバイト単位で一致し、Sharedの保護ファイルのハッシュは承認済み11箇所の機械的変更の後と一致。変更禁止3ディレクトリの差分0。


### 5∞-0 のdraft検査・第60束、A01完了（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第60束](bulk-5inf0/draft-block60-validation.json)でA1/DeRhamComparisonPoly全体が約41秒で成功。有効な成功は44／57本。rootFormsAugmentationの端点は、零単体の添字とnerveMapの評価の等式を明示し、形式関手の零単体はComposableArrows.ext₀で照合した。同じ辺の合成で、数学的な入力・仮定は追加していない。保持した二つの旧pd比較の型を含めてファイル全体が通った。検査済みソースをコミットする。A0・A1が全て通ったのでA01をPASSへ更新した。

次のA5/StrongDescentは、削除済みのpairKoszulTowerへの古い参照で失敗した。既存のpowerKoszulTowerに同じ二つの座標を渡し、元のK(p,e)を第一冪の段として読む。D3の二切断のホモトピー圏の対象は既存のptから頂点を取る。元のRHomとKoszulの主張・仮定・sorryは増やさず、第61束で検査する。


### 5∞-0 のdraft検査・第61束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第61束](bulk-5inf0/draft-block61-validation.json)でA5/StrongDescentが約40秒で成功。有効な成功は45／57本。同じK(p,e)を既存のpowerKoszulTowerの第一冪の段で読み、D3の対象のptを使う修正が通った。検査済みのソースをコミットする。直前の報告のde Rham比較の時間は生ログに合わせ約41秒に訂正した。

次のWeaklyInitialAndDescentは失敗。includeとdocstringの順、完備化環の元のCommRing instance、完備CAlg包含・反射の名前とp引数を明示する。filtered余極限の指定比較は同じ式の中間のcoconeと射に型を付け、推論を分割して検査する。heartbeat上限は上げない。第62束に並んだ。


### 5∞-0 のdraft検査・第62〜63束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第62束](bulk-5inf0/draft-block62-validation.json)の残る推論を分け、[第63束](bulk-5inf0/draft-block63-validation.json)でA5/WeaklyInitialAndDescentが成功。有効な成功は46／57本。二段のmapCoconeは一段ずつ同じ中間の錐に型を付け、弱始対象のUnder.mkには元の標的の環と射の始域Uを明示した。検査済みソースをコミットする。

同じ束のPerfectSiteComparisonは検査中にこちらが後続修正を置いたためSTALE（無効）になった。成功には数えず、元の診断とソースが変わった事実を生ログごと保存した。今後、実行中の対象のソースは変えず、束が終わってから修正する。残る二つのanimated関手はA7/AnimatedPerfectoidizationが実際の所有元なので依存表にその1辺を追加（循環0、従来の順序は有効）。有界性は既存の完全性から渡す。ArcSiteの未修飾名は既存のSheavesの所有元をopenする。第64束で再検査する。


### 5∞-0 のdraft検査・第64束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第64束](bulk-5inf0/draft-block64-validation.json)はPerfectSiteComparisonの既存の有界性補題のimport漏れ1件、ArcSiteのIsWeaklyTerminal・CechNerveDataの二つの所有元の曖昧さで失敗。有界性補題の実際の所有モジュールPerfectBoundedをimportし、二つのČechの名前は元の意図どおりSheaves側に修飾して第65束へ並んだ。実行中の対象は変更していない。


### 5∞-0 のdraft検査・第65束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第65束](bulk-5inf0/draft-block65-validation.json)でPerfectSiteComparison（約44秒）・ArcSite（約22秒）・AfterComparison（約23秒）が成功。有効な成功は49／57本。既存の完全性から有界性を渡すこと、animated関手の実際の依存、Sheaves側のČechデータへの修飾が通った。この3本の検査済みソースをコミットする。

InterfaceLimitConeとUniversalPropertyは失敗。前者はe3LimitConeが実際に持つhRを同じ変数から転送する1箇所。後者はPrismaticのAnimatedAlgebra・polyYonedaの所有元と、通常のHomotopyCategory.homMkのAPIを直接使うようにする。selfTensorの後続のエラーはその未定義の脚の連鎖なので、先に脚を検査する。第66束へ並んだ。


### 5∞-0 のdraft検査・第66束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第66束](bulk-5inf0/draft-block66-validation.json)でInterfaceLimitCone・UniversalPropertyが成功。有効な成功は51／57本。hRの転送と通常のホモトピー圏の脚の表示、Prismaticのanimated代数の参照が通った。検査済みソースをコミットする。改名した参照の所有モジュールの到達漏れも再確認して0。依存グラフは12,940頂点、旧E3入力への経路0だった。

次のArcSheafPropertyは失敗。AsSmallから元の圏へ戻る同じ関手のnerveは、射の宇宙が違うので既存のresizedNerveMapで読む。完備化H⁰の環構造は既存のprincipalCompletionCommRingを明示する。商への射は同じf.right.homをIdeal.quotientMapへ正しい順序で渡す。二成分の関数は同じBoolによる場合分けをfunの構文で明示し、層化・大域切断の名前はSheavesの所有元に揃える。新しい数学的入力やsorryは追加せず、第67束で検査する。


### 5∞-0 のdraft検査・第67束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第67束](bulk-5inf0/draft-block67-validation.json)でArcSheafPropertyの宇宙を調整したnerve、完備化H⁰の環構造、商写像、Sheavesの参照は通った。残るのは二成分の関数のパターン構文2件。同じfalse側・true側をBool.recとcasesで記し、第68束へ並んだ。有効な成功は51／57本のまま。


### 5∞-0 のdraft検査・第68束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第68束](bulk-5inf0/draft-block68-validation.json)でArcSheafProperty全体が成功。有効な成功は52／57本。二成分の同じ定義のBool.rec・casesへの表示と、元の完備化H⁰の環構造の明示が通った。検査済みソースをコミットする。

次のSheafOfSetsExcisionはpushout.descの未指定の二本の射の推論とisIntegralPerfectoid_prodのimport漏れで失敗。同じpushoutの二本を名前つき引数で渡し、乗法・剰余への射の始域・終域を明示する。積の補題は本体のPerfectoid.FiniteProductを直接importする。第69束で検査する。Leanの追加・削除は第68束前で5,556行、当初の見込み上端5,550行を6行超えたが、承認された外枠11,100行には達していない。新しい数学の項目は追加0。


### 5∞-0 のdraft検査・第69束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第69束](bulk-5inf0/draft-block69-validation.json)でSheafOfSetsExcisionのpushoutの指定と積の補題のimportは通った。残るのはcompletionLiftが別の名前空間のものに解決された1件。本来のDerivedCompletion.completionLiftを完全名で指定して第70束で検査する。有効な成功は52／57本のまま。


### 5∞-0 のdraft検査・第70束と名前空間の訂正（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第70束](bulk-5inf0/draft-block70-validation.json)は、こちらがcompletionLiftの所有元をファイル配置からDerivedCompletionと誤って判断した1件で失敗。RingCompletion.leanのnamespaceを実際に確認し、正しいBhattScholze.PerfectoidizationInterface.completionLiftに訂正した。直前の節の「本来のDerivedCompletion.completionLift」は誤りで、ここで撤回・訂正する。第71束に並んだ。成功は52／57本のまま。


### 5∞-0 のdraft検査・第71束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第71束](bulk-5inf0/draft-block71-validation.json)でSheafOfSetsExcisionが成功。有効な成功は53／57本。補った同じpushoutの射、FiniteProductの補題、正しいPerfectoidizationInterface.completionLiftが通った。普通のホモトピー圏の6参照の台帳も全3ファイルで全体の検査が通った状態に更新。この検査済みソースをコミットする。

次のExcisionは、既存のIsIso ηの証明をasIsoで探索する1箇所で失敗。元からある証明をhηと名前を付け、@asIsoへ直接渡す形で第72束に並んだ。主張・証明の未完了の数・引数は増やしていない。


### 5∞-0 のdraft検査・第72束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第72束](bulk-5inf0/draft-block72-validation.json)でExcisionが成功。有効な成功は54／57本。同じIsIsoの証明をasIsoへ明示的に渡すことが通った。検査済みソースをコミットする。

次のAlmostPurityConnectivityは本体へ移したtrivialCoverComparison_isModuleCompleteのdocstringとinclude hRだけが残った構文エラー1件。本体のAlmost/FiniteEtaleComparison.leanの所有元を示す通常の注記に替え、孤立したincludeは除いた。後続のarcOutside_of_integral_of_localization_isoに、本来不要なperfectoid基底の仮定を付けない。新しい仮定やsorryは追加しない。第73束へ並んだ。


### 5∞-0 のdraft検査・第73束（11-14夜）

一覧：済み 11／全体 14（うち追加 0）。[第73束](bulk-5inf0/draft-block73-validation.json)でAlmostPurityConnectivityが成功。有効な成功は55／57本。本体への参照、D3の対象のpt、孤立していた移動済み宣言の注記の整理が通った。検査済みソースをコミットする。

次のIntegralDiscretenessはquotientTensorを呼ぶ2箇所で失敗。本体Almost/AlmostTensor.leanの変数宣言を確認し、同じRは暗黙引数なので(R := R)と明示して渡す。型の内容・仮定は変えず、第74束に並んだ。残るのはこの1本とA9/Assembly。


### 5∞-0 のdraft検査・第74束、A05完了（11-14夜）

一覧：済み 12／全体 14（うち追加 0）。[第74束](bulk-5inf0/draft-block74-validation.json)でIntegralDiscretenessが成功。有効な成功は56／57本。同じRをquotientTensorの暗黙引数として渡すことが通った。A8の全件が揃ったためA05をPASSへ更新し、本体の40対応の台帳も全体の型検査済みにした。この検査済みソースをコミットする。

最後のAssemblyは失敗。構造の各欄へ同じhRを名前付き引数で渡し、PerfectoidizationInterfaceE3の実際の名前空間PerfectoidizationInterfaceを開く。既存のTheoryからE3への還元を使う方針はそのまま。界面の型・主張・仮定は変更しない。第75束で検査する。残る項目はA04・A07。


### 5∞-0 停止点・完了報告（11-14夜）

一覧：済み 14／全体 14（うち追加 0）。[第75束](bulk-5inf0/draft-block75-validation.json)でAssemblyが成功し、[最終照合](bulk-5inf0/draft-final-validation.json)は**57／57本が有効なPASS、失敗0・期限切れ0**。元のLake設定（maxSynthPendingDepth=3等）を継承し、一時配置の依存12,944頂点と、draft間234辺の順序を明示した。構造の八欄は同じhRを渡し、TheoryからE3への既存の還元で組み立てた。rootの選択済みE3入力にはdraftsから戻らない。共有鍵は各束280秒以内で取得・返却し、現在は持っていない。

本体7モジュールと直接利用側を含む13対象のビルド、小監査（所有する99宣言、必要な11名）は既にPASSで、その13ソースのハッシュが最終状態と一致することを再確認した。小監査は標準のpropext・Classical.choice・Quot.soundだけ。正式BS監査への[登録案](bulk-5inf0/stage2-audit-registration-proposal.json)は案のまま。5∞-0の指示は対象ビルドと小監査であり、この枝の変更後のroot全体ビルド・full verifyを通したとは扱わない。

[完了記録](bulk-5inf0/completion.json)：本体とdraftsの公開名の重複候補0（本体32,937ファイルを走査）、旧E3入力へのimport経路0。層の検査は基準と同じ15辺で追加0・例外追加0。[層の差分](bulk-5inf0/final-layer-comparison.json)と[全出力](bulk-5inf0/layers-final.json.gz)を保存。変更禁止のEInfinity/・InfinityCategories/・AlgebraicGeometry/は差分0。Sharedの保護ファイルは承認済み11箇所の機械的追従後と同一、A4のP⁰節は基準とバイト単位で一致する。

[宣言の全件台帳](bulk-5inf0/declaration-disposition-audit.json)は123対応（同名所有元113・別名置換7・旧型を保持した改名3）、削除120・改名3・未説明0。型が異なった一般pd模型と普遍Witt比較は元の未証明の主張を保ち、強い仮定への置き換えで消していない。承認されたuniversalLciPrismのh₀と、同じ理由の[引数の復元](bulk-5inf0/restored-context-parameters.json)は全ファイルの型検査で通った。環・δ構造・生成元は[保存の確認](bulk-5inf0/a3-restored-parameter-source-guard.json)どおり。

[ソースのsorry](bulk-5inf0/all-draft-sorry-summary.json)は全57本で827→684（143減、ファイル別の増加0）。従来の変更対象56本の系列では819→676、A0〜A9は705→569。残るsorryは⑤∞で証明する元の数学であり、今回それを証明したとは主張しない。B06の一般の結晶比較は§2B6の明示の許容に従い5∞-3aへ回した。

Lean差分は追加2,791・削除2,800、計5,591行。当初見込み上端5,550行を超えたが、承認された外枠11,100行の内側。追加の数学項目は0。A07は古い基準の記載をefa846fe8へ更新し、元から基準の記載のない補助ファイルには書き足さず、保護ファイルは許された機械的追従だけに留めた。READMEの旧配置は履歴と明示した。

保護されたShared/EInfinityPowerOperationには既存のdocstring linterのwarningが残り、本文にerrorという語を含むが診断の重大度はwarning、Leanの終了コードは0である。保護範囲の文章を変えてこの警告を消すことはしていない。

これを5∞-0の単独取り込み用の停止点とする。取り込みは調整役に委ね、指示どおり続いてB5の段0（属性からの地図生成の紙の設計）へ進む。


### B5 段0・属性からの地図生成の案（11-14夜、紙のみ）

5∞-0の停止点は16e125f58。ここからはB5の段0。Lean・本体の表・scriptsは変更せず、鍵も取っていない。[入力の全件棚卸し](bulk-b5/stage0-inventory.json)と[型付きの作業表](bulk-b5/stage0-plan.json)を保存した。B5一覧：済み 0／全体 6（うち追加 0）。段0の設計は済み、以下6項目の実装は未着手。

**既存の入口。** Util/Citation.leanの#cite_tags KEYは既に1対応1JSONを出す（key・number・edition・relation・comment・declaration・module・path・line）。#cite_tags!は型も出す。citationExtは永続環境拡張、Kerodon・StacksはMathlibのnative属性を同じ出力へ載せる。新しい属性の実装を作り直さない。#cite_checkは元の環境にある定数を調べるだけで再解釈しないので、必要な候補の型・axioms・ModelCategory SSetの印の再確認に使える。

**入力の規模（CSVの行数、対応済み件数ではない）。** HTT 1,730、HA 2,866、BS 211、K 208、Kerodon 3,553、計8,568行。Kは別に5文献のitems.csvとothers.csv 47行を持つ。Kerodonのitem-tags.csvは6,613行で、一項目一Tagとは限らない。レビューはHTT・HA・Kerodonの28ファイル。略号の登録は25 KEY。B3の保存記録は1,883組・14群で欠落/余分/相違/metadata errorが0だが、これは当時の照合であり、新しいB5の環境抽出件数として使わない。

| ID | 出すものと合格条件 | 見込み行数 |
| --- | --- | --- |
| B5-01 | 入力と番号の対応表：旧表の手判断の列と機械生成の列を分ける。番号・略号・版・Tagの対応を既存レビューから固定。 | 100–180 |
| B5-02 | 環境からの抽出：既存#cite_tagsのJSONを所有モジュールごとに抽出し、原Lake設定・終了コード・ソース/oleanの署名を記録。 | 200–350 |
| B5-03 | 対応の照合と保留台帳：exact/partial4種/nativeを保存し、未対応・複数対応・旧187件・新規7モジュールを診断に残す。 | 180–300 |
| B5-04 | 地図の生成：5族の項目と宣言の両向きJSON/Markdown索引。MathlibとArchive、公開範囲、nullの行を区別。 | 180–300 |
| B5-05 | 検査と再現性：重複import、別名、nativeタグ、部分対応、失敗・古い成果物、曖昧な番号、改名後の場所を検査。 | 150–250 |
| B5-06 | 更新手順と配布：生成物と入力のハッシュ、差分の確認、各レーンの新規属性の扱い、再生成手順を文書化。 | 80–150 |

**元の判断と生成する情報。** title・kind・goal・status・reason・confidence・版と文献番号の判断は既存レビューの入力として残す。宣言の完全名・所有モジュール・現在の場所と行・属性のrelation/commentは実環境から生成する。属性があることを「証明済み」や「完全な対応」と同一視しない。partialはspecial/direction/stronger-hyp/componentと理由をそのまま保持する。native出力のrelationはnativeであり、exactへ自動変換しない。own/both/mathlibの判断は確認済みの対応表と結ぶ。未確認のnative対応は診断へ出す。

番号を文字列の先頭だけで切り落とさない。例えばBS表の1.1行にはDef 3.2の言い直しとの注記がある。文献の番号・表の安定ID・kindの対応はB3のレビュー済み判断から作り、単なる数字の一致で結ばない。Kの「論文」「9人論文」などもbibliographyのKEYとの明示の対応表を使い、題名の類似から推測しない。Kerodonは番号とTagの両方向を保存する。

**抽出の範囲と手順案。** 対象はrootの現役の閉包、対応表の所有モジュール、現役の属性を持つモジュールの和。rootを一度importするだけではroot外の対応を落とすので、所有モジュールごとの小さい一時Leanを生成し、Util.Citationとそのモジュールをimportして#cite_tagsを呼ぶ。採取した環境のモジュールと、宣言の定義の所有モジュールは別の列にする。別モジュールから既存宣言へ属性を付ける場合もあるので、所有元が採取元と違うという理由で捨てない。全採取レコードのimport重複を(key,edition,number,declaration,relation,comment)でまとめ、同じ(key,edition,number,declaration)に異なるrelation/commentがある場合はconflictとして報告する。異なる別名は同じ宣言へ勝手に潰さない。LeanのJSON診断のinfoの中の完全なレコードだけを読む（警告本文の波括弧を拾わない）。終了コード非0・欠落モジュール・ソース/olean/設定の期限切れは抽出失敗とし、空の成功として扱わない。

Mathlibの対応は外部のものとして保持し、宣言の所有元をSerrePositivityへ付け替えない。必要なMathlibのTagを別モジュールで付けている場合は、その適用元も抽出対象へ足す（Mathlib全体を一律にimportしない）。pathはmodule名から推測して確定せず、実際のsource rootで解決・照合する。rangeがない場合はnullのまま診断へ出す。Archive、scripts、drafts、ModelCategory SSetを満たせないものは現役の対応に混ぜず、除外理由付きの台帳へ残す。Mathlibタグを自前宣言へ移すこともしない。

**保留の取り扱い。** 旧187件は元のcoverage-location-refresh台帳とB3の最終判断を対応元付きで突き合わせて再計数する。187件が今も全部未解決、または全部解決したとは仮定しない。名前の末尾だけで再結合しない。5∞-0の新規7モジュールはciteの記載0で、監査対象は99宣言。99全部を新たな文献対応と扱わず、原典の項目を記した主宣言だけを候補台帳に挙げ、型・範囲の判断が未確定なら保留にする。B5の地図生成のついでに無承認で属性を付け足さない。

**出力案。** research/generated-citation-maps/<KEY>/にitems.json・declarations.json・index.md、共通にmanifest.json・unmatched.json・excluded.jsonを置く。5族をまず対象とし、他KEYは宣言索引までで、新しい文献の項目表は作らない。既存items.csvを属性だけから上書きせず、手判断のカタログと生成された参照のviewを分ける。元の「名前 @ パス:行」はB3の根拠の履歴として残し、現在の参照としては環境の値を使う。逆引きは宣言→文献項目と項目→宣言の双方を生成する。

**検査案。** 2回生成の同一性、同じ依存の複数import、複数の文献対応、別名、partial4種とnativeの保持、Mathlib所有元、privateとrange=null、曖昧な番号、旧187件の照合、改名後の場所、失敗や古い成果物が空成功にならないことを小さいfixtureで確認する。最後にB3の受理済み対応と新抽出を集合比較し、説明のない欠落・余分0にする。新規候補や未対応は除外して数を合わせず、件数と理由を出す。

見込みは手書き890〜1,530行（道具・意味のあるfixture検査・文書。生成物と一時Leanは除く）、0.5〜1.5日。環境抽出は今回未実行なので所要時間は未実測。最初の50所有モジュールで壁時計・最大メモリを測り、残りの数から時間を見直す。待ち時間を除いた見込みと鍵待ちを分ける。一晩で済むとはまだ約束しない。実行時は--wait 3600・bulk、昼は280秒以内、夜は30分以内、所有モジュールごとのreceiptを保存して再開可能にする。

B5段0はここで止める。B5の実装、既存地図の置き換え、追加の属性付け、B3′の移動・改名には進んでいない。


### B3′ 着手・範囲の確認（11-14夜）

一覧：済み 0／全体 22（うち追加 0）。main 32d364b53からbulk/b3primeを切った。22項目はR8-2を先頭に、R7-3(a)(b)(c)(d)・R7-4・R7-5・R7-6(c)・R7-7、R8-1・R8-3・R8-4・R8-7・R8-8・R8-9、R10-3・R10-5(a)(b)(d)(f/g)・R10-7、B3残りの照合を数える。段0の表を作成中で、Lean・既存scripts・他レーンの作業木は変更していない。ビルド・適用も未実行。

R8-2はRingCompletion.leanへの既存の切り出しを再利用し、Setup・Completionの環の部品と、nerve・指定錐の部品を区別する。Completion節全体を環のファイルへ移すと∞の依存を残すため、一律の節単位では分けない。

R8-1に指示の範囲の衝突がある。§1はEInfinity→BSの2辺の解消を求めるが、§2の保護例外はTheoryInterfaceとそのimporter。もう一辺はEInfinity/Perfectoidization/ComparisonからDerived/Interfaceへのもので、ComparisonはTheoryInterfaceをimportしない。TheoryInterfaceだけを動かしても残る。CAlg_R版のComparison・Interface・DerivedCorollaryの3本（計255行）を削除せずBS/Perfectoidization/Interface/CAlgへ機械的に移す案を[具体的な表](bulk-b3prime/r8-1-scope-decision.json)にした。宣言の完全名・型・証明は保持し、旧モジュールの再公開stubで逆辺を再導入しない案。保護例外の承認前には適用しない。

4つの必須の旧パス文字列について、稼働5枝のmainとの分岐点以降のLeanと未コミット/未追跡Leanを読み取りで調べた[下限の調査](bulk-b3prime/mandatory-impact-lower-bound.json)は0ファイル。これは全移動・全改名の最終影響件数ではない。30ファイル条件を満たしたとまだ扱わず、残りの表と影響の静的調査を続ける。


### B3′ 段0・全表と準備への移行（11-14夜）

一覧：済み 2／全体 22（うち追加 0）。基準mainは32d364b53。[22項目の表](bulk-b3prime/stage0-items.json)、[モジュール移動案](bulk-b3prime/module-map.proposed.json)、[所有元付き宣言名の案](bulk-b3prime/namespace-map.proposed.json)、[6切り出し先](bulk-b3prime/split-plan.proposed.json)を保存。71本の全体移動、公開ソース宣言1,861行のうち1,486改名。これは構文上の表であり、private・生成宣言を含むカーネル全表は元の環境のsnapshotで準備中に補完する。R7-3(a)のMonicRelation/Familyと(d)のPrismPresentationはmainに実装済みなので再移動しない。

調整役の§5の承認により、CAlg_RのComparison・Interface・DerivedCorollaryも保護例外となった。[承認記録](bulk-b3prime/r8-1-scope-decision.json)を更新。削除せず名前・型・証明を保ってBS側へ移す。旧パスの再公開stubはEInfinityからBSへの逆辺を戻すため作らず、集約importを整理する。

[静的な衝突検査](bulk-b3prime/stage0-target-collisions.json)は本体33,638ファイルの公開ソース宣言に対する行き先名衝突0、分割先パス衝突0。[直接importの解析](bulk-b3prime/stage0-import-closure.json)では変更所有元111、逆向きの閉包191モジュール。RootEnvelope三本・PerfectPrismDivisionComparison・PDivisionSource・TensorCompatibilityは現rootから到達しない。証明済みの別構成・終点として公開し、未使用という理由では削除しない。監査に移動済みの四本は再移動しない。

[稼働6枝の文字列調査](bulk-b3prime/branch-impact-stage0.json)は合計2ファイル（⑥の過去のB4 JSON二本）、Lean 0、行き先パス衝突0。⑤a・⑤d・③二枝・⑥・Kerodon reviewを読み取りだけで調査。未コミット/未追跡と文書・データも対象にし、改名対象の完全名・旧モジュール/パスを検索した。単なる文字列調査であり意味上の参照の採取とは区別する。過去の表は履歴として残し、B4用に写像の合成を提供する。適用前に動いている枝を再走査する。承認範囲内かつ30ファイル以下なので停止せず隔離した準備へ進む。

DivisionResidueの移動は暫定案。現在のファイルはNormalizedの有限塔・忠実平坦性に依存するため、丸ごとの移動だけではDelta→Andreの逆辺を作る。一般の依存の閉包を調べ、分離できなければその移動を取り下げて元に残す。文書の「旧パス」は現在0件。工程名の候補と引用の歴史の注記を分け、属性の意味や対応番号を機械的に消さない。

[時間の見込み](bulk-b3prime/stage0-timing.json)：準備4〜12時間、適用と全検証3〜8時間（鍵待ちを除く、今回のプレビューは未実測）。以前のB3の実測はroot 689秒、verify（3ジョブ）2,968秒。全監査106本の実測合計も付表に保存した。今回の閉包が小さくてもroot・全監査・verifyは省略せず、最初のプレビューの実測で見直す。昼は280秒以内、夜30分以内・--wait 3600・bulk、全監査/verifyは夜。適用の直前に通知し、それまではBSの取り込みを止めない。


### B3′ 準備・R8-2の分割プレビュー（11-14夜、未適用）

一覧：済み 2／全体 22（うち追加 0）。隔離worktree /tmp/bulk-b3prime-previewを作り、packagesは既存を参照、buildはcopy-on-writeの独立したコピーにした。他レーン・main・この枝の本体Leanは変更していない。R8-2を最初に実行した[プレビュー](bulk-b3prime/r82-preview/preview.patch)は、元の64宣言をBS側32・通常の圏16・通常の完備化16へ三分割する。元からHomologicalAlgebraにあるRingCompletionは再利用し、nerve・単体的四角形・指定錐はBS側に残す。

対象3モジュールはビルド成功。[保存比較](bulk-b3prime/r82-preview/r82-comparison.json)はv3bの64親宣言で欠落・余分・未説明0（生のsnapshotは184→185カーネル行。生成行の取り扱いはB3と同じ既存比較器）。型・本体・公理・カーネル属性を検査し、比較器やsnapshotの規則は弱めていない。元の宣言のコマンドはバイト単位で保存。所有元の写像と原snapshotの圧縮版、ハッシュは[manifest](bulk-b3prime/r82-preview/manifest.json)に保存した。

最初の25宣言だけの分割も未説明0だったが、通常の商図式とArcOutsideを使う環側に古い依存が残ったため7宣言を加えた。その初回比較で11差分を検出し、Mathlib.Combinatorics.Quiver.ReflQuiverのimport不足によるquiver instanceの違いと特定。元のinstanceを供給するimportを加え、最終比較で0に直した。初回の差分を許容して通したのではない。

直接利用する環の5本はimport一行だけをRingInterfaceへ替えた。RootAdjunction・IntegralClosureCompletion・IntegralApproximation・PerfectoidFilteredColimit・ArcPerfectoidBaseで、その和の静的閉包334モジュールにInfinityCategoriesは0本。これら5本の対象ビルドと172親宣言の保存比較も成功したが、最後のMathlib import修正後の環境で再照合するため次の鍵の塊へ入れた。この再照合が済むまで最終receiptは保留とする。

全体の準備は187モジュールの元環境snapshot、162本の参照採取を再開可能な束で進めている。importだけの集約4本には所有宣言がないことを静的に確認し、importとroot検査で扱う。参照採取は既存bulk_collectを使い、Lakeの元のsetupを継承する。共有鍵は一回ずつ、昼270秒・夜1,650秒、--wait 3600。

依存の閉包の調査で、DivisionResidue全体の移動は撤回し、独立な剰余・テンソル表示12宣言の切り出しへ変更した。[残す理由](bulk-b3prime/retentions.json)：平坦性・正則性がNormalizedとOrdinaryRoots/Adjoinの有限塔に依存し、全体移動はDelta→Andreを新設するため。残るLciEnvelopePresentationからその平坦性への辺を解消したとは扱わない。更新後の案は全体移動70本・切り出し先7本、公開ソース表1,848行（改名1,486）。またRootSourceの一般の反射比較は1460〜1591行の節だけを対象とし、その後の具体的δ根添加の完備性は一般のファイルへ混ぜない。


### B3′ 準備・環側の再照合と静的な層の修正（11-14夜）

一覧：済み 2／全体 22（うち追加 0）。R8-2の最後のimport修正後に環側5本を再ビルド・再採取し、[172親宣言の保存比較](bulk-b3prime/r82-preview/r82-consumers-comparison.json)は未説明0で通った。原環境とプレビューの生snapshot・各実行のreceiptを追加し、保留を解除した。本体への適用はまだ行っていない。

InitialLimitの行き先をLimitsAndColimits/から**Cofinality/InitialValueCone**へ修正した。初期案の§7.1に置くと、実際に使うInitialCofinalityの§7.2への新しい逆辺になるため。同じ§7.2に置き、例外を追加せずに扱う。名前もCofinalityの名前空間に揃える。ネイティブの[切り出し前の依存の確認](bulk-b3prime/native-split-closure-preliminary.json)ではInitialLimitは一般のKerodonの部品だけ、RootSourceの反射比較も外部のBS依存なし。生成された式補題・局所notationの全所有元は既存の厳格なv3b処理で検査し、構文上の行数だけで検査済みにはしない。

R8-4の互換wrapper一個は[削除・利用先変更の台帳](bulk-b3prime/redirects-and-deletions.json)へ独立に記録した。削除を改名と混ぜて比較の欠落を隠さない。Finiteとwrapper本体も参照採取に追加し、対象は187 snapshotモジュール・164意味上の参照ファイルとなった。

改名のプレビューではnamespaceとopenを元のままに保ち、実際の使用を完全名へ書き換える。元環境の採取が済んだ19本はプレビューの保留0まで確認したが、改名後のビルドは未実行。宣言名の位置にLeanが同時に記録するLocalInfoは、同じ位置の自分のglobal binderと、宣言コマンド範囲またはネイティブのselection位置で照合できた場合だけ合成の情報として扱う。任意の用語位置の曖昧性は除外しない。この調整は隔離した準備用コードだけで、他レーンが使う共通の道具は変更していない。型・本体の保存比較による最終確認は別に必須とする。


### B3′ 準備・基準にある層の未登録（11-14夜）

一覧：済み 2／全体 22（うち追加 0）。移動前の基準32d364b53と、R8-2等だけのプレビューで既存の層検査を実行したところ、どちらも既存305モジュールのper-file tier未登録で停止した。[全件と直接import](bulk-b3prime/baseline-unclassified.json)を保存。DiagramComparison149・CosimplicialTotalization91・その他65。これらはgitに追跡された本体であり、作業用一時ファイルではない。例：BKStandardZeroGeneratorはmainの1599b1e50で入った。現mainのlayers.jsonも基準と同じで、未登録を補う新しい表はまだ取り込まれていない。

この失敗を「層の違反0」と扱わず、任意のConsumers指定や例外で覆わない。調整役へ割当の根拠を照会する。その間も、元環境の採取と承認範囲のプレビュー準備は続ける。今回新設するInitialValueConeにはPortableを提案しているが、基準の305件を登録したとは主張しない。


### B3′ 準備・305本の層の機械的な登録（11-14夜、調整役の指示に追従）

一覧：済み 2／全体 22（うち追加 0）。調整役が指定したB3のruleをimportの依存順に適用し、[305本の割当表](bulk-b3prime/new-main-tiers.json)を保存。Portable21・Comparison67・Consumers217。既存の層変更0・例外変更0。推測による補正、循環による未決定、tier-order/implementation-boundaryの違反は0。設定への追加はB3′の束に含め、現時点では隔離プレビューの設定にだけ加えた（元環境の本体・設定は採取中のまま）。

[検査の概要](bulk-b3prime/tier-classification-summary.json)と[全出力](bulk-b3prime/tiers-baseline-report.json.gz)を保存。節の順序の逆辺は移動前から46件ある。以前のB3の出力との[差](bulk-b3prime/baseline-layer-delta-from-b3.json)も一覧化した。これらへ新しい例外を加えて0件にせず、今回の変更前後で増えないことを検査する。InitialValueConeの行き先をCofinalityへ直したのも、この新規逆辺を避けるためである。


### B3′ 準備・夜の採取と全名前空間の表（11-14 23時台）

一覧：済み 2／全体 22（うち追加 0）。R8-8の20本すべての旧Perfectoidization.Derived名前空間を表へ揃えた。ArcはPerfectoidization.Arc、RootAdjunctionはPerfectoidization.Construction、§10の四本はBhattScholze.Almost、純粋なIntegralApproximationはCommutativeAlgebraへ。移動しない型IsPerfectoidization・IsPrismaticEnvelope・OrientedPrism・DeltaStructure・PrismOverのメソッドは、その実際の型の名前空間を保つ。別ファイルの型に属するメソッドも親の新しい完全名と揃え、モジュールのパスから名前空間を推定しない。

更新後は全体移動70本・切り出し先7本、公開ソースの所有元/改名表1,936行（改名1,607）。閉包は201モジュール、importだけの四本を除くsnapshot197・参照採取176。進行済みの束番号と成果物は保ち、増分10モジュールだけを末尾へ加えた。新しい全表でも他枝への文字列の影響は2ファイル、行き先パス衝突0。名前を変えず所有モジュールだけが移るCAlg_R等の宣言も検索に含めた。

[一般の三つの新ファイル](bulk-b3prime/projected-generic-plan.json)は独立プレビューの対象ビルドとsnapshot採取に成功（[実行記録](bulk-b3prime/generic-target-build-receipt.json)）。InitialValueCone14・IteratedPDH0 8・AdjoinResidue12宣言。これは対象ビルドの成功であり、元ファイル全体の保存比較の成功とは区別する。[部分プレビューの層比較](bulk-b3prime/partial-preview-layer-comparison.json)は基準46・プレビュー46・新規0、例外追加0。

[準備のチェックポイント](bulk-b3prime/preparation-checkpoint.json)：128モジュールの部分カーネル表15,367行を作り、この範囲の公開ソース名の欠落は0。前提9,629モジュールのprivate元名5,228件、.ileanの欠落0・モジュール内の正規化名の衝突0。notationの補助宣言は元のコマンドとネイティブの型を根拠に分け、通常のprivateをモジュールを無視して同一視しない。部分表は圧縮版を保存し、全体が採取されてから実際の移動後のカーネル名と再照合する。

採取済み127本は改名プレビューの保留0。修飾付きの宣言名五箇所は、同じ位置のネイティブ宣言とsource selectionを確認して完全名へ書き換えた。宣言名の変更が本体の名前解決の文脈を変える場合も元の参照を保つよう扱う。共通の道具は変更せず、隔離した準備コードで行っている。全体の対象ビルド・v3b・引用/タグ・root・正式全監査・verifyは未実施であり、適用の通知もまだ出していない。夜は一束1,650秒以内・--wait3600・bulkの一つの整理券で続ける。


### B3′ 準備・23:46の記録

一覧：済み 2／全体 22（うち追加 0）。元環境の参照採取は160／176本、snapshotの束は22まで成功。共有鍵は夜の上限1,650秒で返却・再取得し、一つの整理券だけで続けている。全体の改名後のビルドと保存比較は未実施。

[完全名の全本体走査](bulk-b3prime/qualified-name-coverage-check.json)でも、変更名への参照がimportの閉包の外へ漏れたものは0（文字列・コード双方）。[引用の採取計画](bulk-b3prime/citation-baseline-plan.json)は実際の属性適用元1,099モジュール・25 KEY。前後の実環境を照合する手順、対象ビルドの束、隔離プレビューの適用手順、コメント以外のバイト列を保つ文書更新の手順を準備コードへ保存した。これらの全体実行を終えたとは扱わない。


### B3′ 準備・全体プレビューと対象ビルド（11-15未明）

一覧：済み 2／全体 22（うち追加 0）。元環境の参照採取176／176とsnapshot197モジュールが完了。公開ソースの欠落0、ネイティブのカーネル表は17,543行。改名プレビューは176本で保留0となり、全体207モジュールのソース束（全体移動70本・切り出し先7本・旧wrapper削除1本）を隔離した作業木へ反映した。[記録と全ソースhash](bulk-b3prime/full-preview-preparation-checkpoint.json)。実際の枝のLean・scriptsにはまだ適用しておらず、凍結の通知も未実施。

[全体の層の比較](bulk-b3prime/full-preview-layer-comparison.json)は基準46・プレビュー46・新規0、例外追加0。Finiteの旧wrapperへのimportが残る一箇所を全体生成器で直し、同じ検査を再実行した。静的な通常の本体のimportグラフでは欠落0・循環0、EInfinity→BSの直接辺2→0・間接依存0、公開対象6本はrootから到達を確認した。Archiveの非ビルド源は区別し、これを全ファイルのビルド成功とは扱わない。最終ソースの静的receiptは対象ビルド修正が揃ってから更新する。

対象ビルド203本を共有鍵bulk（--wait3600、夜一束1,650秒）で開始した。切り出した被約環の補題のringタクティクのimport不足を修正。また、その補題だけを使う二本は、旧Transfinite/Limitの推移的importが供給していたperfectoidの被約性とHAの主元完備化の比較も使っていたため、宣言の実際の所有モジュールを明示した。型・証明は変えていない。修正後の束を検査中で、対象全体の成功・v3b全体の未説明0・引用/タグ一致・root・全監査・verifyは未完了。

R8-8の[draftsの行き先欄](bulk-b3prime/draft-header-plan.json)は現基準で18本。A4/A7→Construction、A5→Descent、A6→Arc、A9→Interface、A8の§10→Almostの案を第一行のコメントだけに用意した。「仮」は保持し、A4のP⁰を含む本文・import・宣言名・型・証明のバイト列は変えていない。R8-9/R10-7で挙がった古い利用入口・別チャットとの調整・未存在の比較名・残る工程の説明もコメントだけで訂正した。全コメント以外のバイト列が同一である検査を付け、引用属性の文字列は変更していない。


### B3′ 準備・元のopenの解決先とmain増分（11-15未明）

一覧：済み 2／全体 22（うち追加 0）。新しいBhattScholze.Almost名前空間が元の`open Almost`を隠すことが対象ビルドで判明した。元環境のネイティブなcommand情報は`SerrePositivity.Almost`を示すので、元の解決先を`open _root_.SerrePositivity.Almost`として保つ。名前のある単純なopen/scoped openは同じ方法で元の解決先を明示し、移動先のモジュール名から新しいopenを作らない。この変更後も改名プレビュー176本・保留0。再生成したソースの対象ビルドを続けている。

現main 391b2a0d2までの[差分の文字列走査](bulk-b3prime/main-increment-impact.json)はコード273パス・今回の旧名/旧モジュール名への該当2ファイル（EInfinity集約、BS正式監査）・98箇所。BS本体の差分0。実適用直前に再確認し、EInfinity集約の新しいimportを残して追従する。[追加40本の層の案](bulk-b3prime/main-increment-tiers.json)はPortable4・Comparison2・Consumers34、未決定0・既存の層/例外変更0、検出は同じ逆順46件のみ。これはまだ枝にmainを取り込んだ結果ではなく、適用準備である。

[最新のプレビューimportグラフ](bulk-b3prime/full-preview-import-graph.json)は、通常の本体31,768→31,774モジュール、欠落0・循環0・EInfinity→BSの直接/間接依存0・公開6本のroot到達を確認。元の全本体のgraphに実ソースの束を重ね、変更外のファイルがないことをgitの差とソースSHAで検査している。Archiveは層検査と同じく対象外。カーネルの全行の所有元表は[圧縮版](bulk-b3prime/before-kernel-disposition.json.gz)にした（比較内容は省略していない）。


### B3′ 準備・文書の対象追加と八辺の扱い（11-15未明）

一覧：済み 2／全体 22（うち追加 0）。移動・改名の依存閉包の外にも、承認範囲のコメント訂正が[9モジュール](bulk-b3prime/additional-doc-modules.json)あった。追加の元環境snapshotを共有鍵で採取し、全体を206モジュール・18,384カーネル行へ拡張（公開ソース名の欠落0）。参照採取176本は変更していない。これらも対象ビルドと同じ厳格なv3bへ含める。文書を含むソース束は216モジュール、importだけの四本を除く対象ビルドは212本。現在のソース版で40本が成功し、残りを検査中。別のソース版の成功と混ぜずhashで区別する。[状態とソースhash](bulk-b3prime/preparation-status-2026-11-15.json)。

R7-3(b)の[八辺の台帳](bulk-b3prime/r7-3b-edge-ledger.json)は、基準で解消済み2、今回の解消予定5、維持1。完全平坦性・主元完備化の三本はB3ですでに一般の場所にある所有元へimportを付け替え、LciEnvelopeRegularは切り出したIteratedPDH0へ付け替える。LciEnvelopePresentationは、実際に使うdeltaAdjoinDivisionResidue_moduleFaithfullyFlatとNormalizedの構成がAndré側の根添加にも依存するため、この辺を残す。DivisionResidue全体のDeltaへの移動は取り下げ、独立した12宣言だけを抽出する。維持した辺を解消済みと数えない。

環の界面の大きいimportを外した後、下流ArcValuationExtensionが推移的に得ていたAlgebraicClosureを失うことも対象ビルドで検出した。元の採取はMathlib.FieldTheory.IsAlgClosed.AlgebraicClosureのAlgebraicClosureを示すので、その実際の定義元を明示する。証明・型の変更はしない。

今回の文書束は252コメントを訂正し、コメント以外のバイト列を保持した。分割されたファイルのmodule docstringと、他の分割先の節見出しが文脈に付いて残る箇所も、該当する部分の説明へ整理した。CompletedTensorには§8と§10で共有する芯を明記した。引用属性の理由文字列は変更していない。現ソースの正式なPython層検査は基準46・プレビュー46・新規0、通常の本体のimport欠落0・循環0・EInfinity→BS直接/間接0。実際の枝への適用と凍結の通知はまだ行っていない。


### B3′ 準備・最終プレビューの対象ビルドと保存比較による型の復元（11-15 01時台）

一覧：済み 2／全体 22（うち追加 0）。省略された旧パスのコメントを全BSで調べ、閉包外の訂正を合計17本へ広げた。元環境snapshotは214モジュール・18,963カーネル行（公開ソース名の欠落0）。全体224モジュールのソース束について、importだけの四本を除く[220対象のビルド](bulk-b3prime/full-preview-target-complete.json)が全て成功した。原本と移動後のprivate名は前提9,637モジュール・元名5,231件で突き合わせ、通常のprivateの欠落0・衝突0・.ilean欠落0・notationの未対応0。共通スクリプトや比較器は変更していない。

厳格なv3bの束009で、FiniteとConeの型・本体に24行の差分を検出した。旧wrapperだけが使っていたAlgebra.FinitePresentationのsection変数が、より弱い仮定の既存BS定理への直接呼出しでは未使用となり、定義の引数から落ちていたため。includeを置く案ではdefに保持されず、同じ差分が残ることも新しいsnapshotで確認した。そこでPerfectoidizationの定義の頭に**元の型と同じ引数列・順序・implicit性を明示**し、値は同じBS定理の選択のままとした。呼出し元も含む束009は、比較器を一切変えず型・本体の差分0でPASS。[復元の記録](bulk-b3prime/finite-fp-restoration.json)と[修正前二回・修正後の生snapshot](bulk-b3prime/finite-fp-restoration-evidence.tar.gz)を残した。24行を説明付きに分類して通したのではなく、実際に直して0とした。全体のv3bは引き続き検査中。

引用・Kerodon/Stacksタグの実環境照合は、宣言名の接頭辞ではなく**実際の定義元モジュールがSerrePositivityであること**で対象を選ぶ。大域名前空間の拡張やprivate宣言を落とさず、元のカーネルの所有元表と同じprivate名規則で前後を比較する。まだ照合の成功とは扱わない。

B4用に[drafts本文の文字列の影響](bulk-b3prime/draft-body-b4-impact.json)も採取した（28ファイル・50箇所、コメント・文字列を含む静的候補）。本文・import・型・証明は変更せず、A4のP⁰の保護を保つ。承認範囲の将来の置き場所の第一行18本とは区別して渡す。実際の枝のLean/scriptsへの適用と凍結の通知、root・正式全監査・full verifyは未実施。


### B3′ 準備・全体保存比較の完了とB4の表（11-15 01:34以降）

一覧：済み 2／全体 22（うち追加 0）。[全29束・214モジュールのv3b](bulk-b3prime/full-preview-preservation-complete.json)が完了した。比較対象4,440→4,439行、承認済みwrapper削除1行、**未説明0**。18,963行のネイティブなカーネル表・通常privateの所有元・生成補助宣言のinventoryも従来の基準で扱い、[生snapshot・比較・同じ規則](bulk-b3prime/full-preview-preservation-v3b.tar.gz)を保存した。比較器とバイナリは変更していない。削除行はrawのremovedに残して承認範囲を個別に記録した。

[B4の改名資料](bulk-b3prime/B4/README.md)には70本のモジュール移動、所有元を持つ公開ソース宣言1,936行、実際の移動先が存在する2,580行の書換表を用意した。生成された式補題の同名が別々のネイティブ環境で作られる4行は、通常のAPIの所有元を推測せず別inventoryへ残す。既存のCLIの移動先一意性の検査も通した。旧wrapperの削除・弱い仮定のBS版への呼出しの変更は、同型の宣言の改名と区別する。元の有限表示性を必要とする定義では元の引数列を保つ。

各枝の元HEADと採取一覧を[レーン表](bulk-b3prime/B4/lanes.json)に保存。短い名前を確認する候補は⑤a79本・⑤d191本・③-a102本・③-b93本・⑥153本、Kerodon0本。完全名/旧importの文字列一致は全枝のLeanで0だが、これを非修飾参照まで含む修正必要数0とは扱わない。draftsはこのcollectに含めず、本文28本の別表へ分けた。他のレーンの作業木への書込みは0。

[適用前のmainの読み取り検査](bulk-b3prime/application-main-preflight.json)ではmain391b2a0d2、BS本体増分0、移動先衝突0。束に含む元ファイルの変更はEInfinity集約だけだった。実適用時にはmainの新しいimportを保って四つのBS固有モジュールへ追従し、基準プレビューの集約で上書きしない。

引用/タグの前後のネイティブ採取は進行中。実際の枝への適用・凍結通知・root・正式全監査・full verifyは未実施であり、B3′完成とはしない。夜は通常の共有鍵bulk・wait3600・一束30分以内で続ける。


### B3′ 適用開始・main増分の追従とroot成功（11-15 01:57〜02:06）

一覧：済み 2／全体 22（うち追加 0）。[引用・タグの全件照合](bulk-b3prime/citation-comparison.json)は2,564→2,564件、欠落0・余分0・衝突0。KEY・番号・宣言名・実際の所有元・関係・理由・版を確認した。これで隔離準備の対象ビルド・全v3b・引用照合が全て通った。

調整役へ「適用に入る」と通知し、main391b2a0d2を取り込んだ（merge2bbec4f28）。[適用前の全guardと適用結果](bulk-b3prime/actual-application.json)に従い、255パスへ書込み・71旧パスを削除。224モジュールの束、正式監査12本、draftsの将来の置き場所の第一行18本、層の設定だけを反映した。EInfinity集約はmainの新しいimportを保ち、BS固有の四ファイルへ至る二つの入口だけを外した。BS固有CAlg_R三本は削除せず、元の名前と型・本体を保ってBS側に置いた。

層の登録は基準305本、main増分40本、一般の新ファイル1本の合計346件。既存の層・例外変更0。実作業枝の[Python層検査](bulk-b3prime/actual-layer-comparison.json)は32,043モジュール、既存の逆順46件・新規0。正式監査のモジュール集合は、分割先も含めて元の宣言の所有元を移送し、判定・axiom許可リスト・探索は保つ。

最初のrootでは、BS集約に追加した十本のimportがmodule docstringの後ろになっている構文エラーを検出した。個別220対象から集約自身を除いていたため、rootで初めて見つかった。十本をヘッダに移し、importの集合が同一であることを検査した（[修正記録](bulk-b3prime/actual-aggregate-header-fix.json)）。[再実行のroot全体ビルド](bulk-b3prime/root-build-complete.json)は32,194 jobsで成功。通常の共有鍵bulk・wait3600・30分以内の束・32GB監視を用いた。

検証済みプレビューとソースSHAが同じ223モジュールだけのキャッシュを原子的に複写し、旧モジュールの成果物を除去した（[記録](bulk-b3prime/verified-cache-install.json)）。main増分で異なるEInfinity集約のキャッシュと古いsetupは使わず、通常のLakeビルドで依存のtraceを検査した。原環境は保存済みsnapshotを使い、適用後の作業枝から採り直したafterとのv3bを進行中。正式全監査とfull verifyは未実行で、完了判定はまだ行わない。


### B3′ 実配置の保存比較完了と全22項目の照合（11-15 02時台）

一覧：済み 2／全体 22（うち追加 0）。本体の適用をc42e8b477へコミット。[実配置のv3b](bulk-b3prime/actual-preservation-complete.json)は保存済みの独立した元環境をbeforeとし、移動後の作業枝からafterを新規採取した。29束・214モジュール、4,440→4,439行、承認済みwrapper削除1・未説明0。[生snapshot・比較・同一規則](bulk-b3prime/actual-preservation-v3b.tar.gz)を保存。privateの元名は実作業枝の.ileanと検証済み独立プレビューで同じことも確認した。

[実際の全importグラフ](bulk-b3prime/actual-import-graph.json)は32,043モジュール、基準からの全ソース差分548パスを重ねた。欠落0・循環0・EInfinity→BSの直接/間接依存0、公開対象六本のroot到達を確認。準備の束だけでなく取り込んだmainの増分も含む。

[BSの元の逆向き34辺の台帳](bulk-b3prime/actual-bs-reverse-edge-ledger.json)は1解消・33維持。SupportedQuotientをExcisionTorの隣へ置いた一辺を解消。IntegralExistenceの三分割後もE3界面からTheorem10.11/Corollary8.14を導く存在部分への依存は残るため、その辺は解消済みとしない。原台帳のネイティブ参照と理由、改名後の両端・現在のimportも残した。層の例外は増やしていない。

[全22項目の実装照合表](bulk-b3prime/scope-items-applied.json)では承認範囲の実装・既存mainで済んだものを全件対応させた。適用済みと最終完了は区別し、正式全監査・full verifyが通るまでは済み2のまま。B3の維持表のうちPD固有cochainHomotopy、R83/Spectrum、広いR21、未使用削除は引き続き範囲外。

B4の採取候補を枝の最新HEADと未コミットの本体を読むだけで更新：⑤a98本・⑤d191本・③-a102本・③-b98本・⑥164本・Kerodon0本。完全名/旧モジュールの文字列一致は0だが、非修飾名の追従まで不要とは判断しない。draftsは別表のまま。他レーンへの書込み0。現在は実配置の属性再照合を進め、続いて正式106監査を一本ずつ通常の共有鍵で行う。


### B3′ 実配置の属性一致・正式監査の前提（11-15 02:26）

一覧：済み 2／全体 22（うち追加 0）。[実配置の引用・タグ照合](bulk-b3prime/actual-citation-comparison.json)は2,564→2,564件、欠落0・余分0・衝突0。所有元1,099モジュール・18組・25 KEYのネイティブ採取で、KerodonとStacksも含む。[実環境の生記録](bulk-b3prime/native-citations-actual.tar.gz)を保存。

[本体の範囲の検査](bulk-b3prime/actual-source-scope-check.json)はmain391b2a0d2との差で309の本体・scripts・draftsパス。承認束の255書込みと71削除の内側に収まり、準備時と同じ17パスはmainと同じバイト列である。全適用ソースのSHA一致、範囲外変更0。比較器・採取器・verify本体は変更0。

[正式監査の全inventory](bulk-b3prime/all-audit-inventory.json)は106本でmanifestと完全一致。前提のビルドは36,526 jobs、31.1秒で成功（[記録](bulk-b3prime/all-audit-prerequisites-complete.json)）。監査本体を一本ずつ開始した。[完了条件の検査](bulk-b3prime/completion-audit.json)は12／14で、未完了は正式全監査とfull verifyのみ。これらを省いて完成扱いにはしない。


### B3′ 正式監査で検出した短名の追従（11-15 02:31以降）

一覧：済み 2／全体 22（うち追加 0）。先行のadamsとBS全体の正式監査は成功。3本目のInitialCoefficientで、監査用の受渡し型に残ったPowerRootPolynomial・powerRootPolynomialDeltaの旧短名がunknown identifierとなった。[失敗と修正確認の生ログ](bulk-b3prime/formal-audit-initial-failure-and-confirmation.tar.gz)を保存し、二箇所を所有元付きの新しい完全名へ直した。同じ監査は16.6秒で成功、185生成宣言を含め標準三公理のみという結論も同じ。

全監査を字句走査し、旧短名とBhattScholze.…の省略名も[五ファイル・111箇所の表](bulk-b3prime/audit-short-name-plan.json)へ追加した。元の所有元が一意の名前を、B4のネイティブ照合済み完全名で置換する。新しいopenは作らず、受渡し型の引数・仮定・式・axiom許可・判定条件は保持。従来の12本の追従と重なるため、変更した正式監査は合計14本となる。本体のLeanと保存比較の結果は変更していない。

[正式106監査の全名・省略名の再走査](bulk-b3prime/audit-name-coverage.json)は残候補0。これは静的検査であり、全監査成功の代わりにはしない。最新の監査ソースのhashで正式監査をやり直す。適用のreceiptにも監査だけの追加を明記し、全ソースのhash guardを維持した。


### B3′ 正式46監査成功・EInfinity監査の明示import（11-15 03:25以降）

一覧：済み 2／全体 22（うち追加 0）。正式監査は46／106本まで成功。47本目のaudit_einfinityは、以前EInfinity集約経由で得ていたBS界面の宣言が見つからず停止した。CAlg_R三本とTheoryInterfaceの宣言は名前を変えずにBSへ移しているため、改名表の非恒等行だけの走査では捕捉できなかった。[元のエラーログ](bulk-b3prime/audit-einfinity-original-import-failure.tar.gz)を残した。

同監査の先頭に、移動後の実際の所有元であるTheoryInterface、CAlg/Comparison・Definition・DerivedCorollaryの四importを追加。必要名配列、検査の述語、exampleの型、axiom許可は変更0。ライブラリのEInfinity→BSの辺は復活させず、BS界面も検査する専用監査の依存を明示した。正式監査の変更は合計15本。

[先行46本の入力一致の証跡](bulk-b3prime/audit-input-equivalence.json)を作った。各監査のソースSHA、本体全体・Root・Lake/toolchain・refactor道具・bibliographyのgit tree/blob、適用した非監査ソースはc2bf2a4fbと同一。原receiptは書き換えず、46本の原SHAも保存。FSを読む先行五つのarea監査は、いずれもモジュール名から導くSerrePositivityのソースだけを読み、他の監査スクリプトを入力にしていない。残り41本にも他の監査への依存はない。専用orchestratorの再開条件を本体/設定の指紋と各監査の個別SHAに分け、同一入力の既済46本を保持して47本目から再開した。比較器・publicなverify・採取器は変更0。最後のfull verifyではキャッシュ結果を使わず106本すべてを新規実行する。

[監査のモジュール集合の照合](bulk-b3prime/audit-module-scope-coverage.json)は69本・欠落0。[属性の保存場所](bulk-b3prime/actual-citation-location-check.json)も2,564件・1,099ファイルで有効、すべて作業枝内の相対パス。R7-3(b)の[実際の八辺](bulk-b3prime/r7-3b-actual-edge-ledger.json)は基準解消2・今回解消5・維持1で、予定だけでなく実importと所有元を確認した。


## B3′ 正式監査通過・full verify中断（11-15 05時）

一覧：済み 2／全体 22（うち追加 0）。全22項目の適用は済んでいるが、最終ゲートが残るため完了とはしない。

正式監査106本は全件成功（一本ずつ、通常のbulk鍵を監査ごとに返却）。[結果](bulk-b3prime/all-audits-complete.json)と[原記録](bulk-b3prime/formal-audits-checkpoint.tar.gz)を保存した。先行46本は既述の入力同一性の証跡により保持し、その元receiptを編集していない。保存比較29束・214本の未説明0、引用/タグ2,564組の欠落・余分0、root成功も維持している。

B4の補助手順は、共有の書換器を変更せず、宣言の実際の移動先のimportを資料側で補う。[README](bulk-b3prime/B4/README.md)とrewrite.py、移動した公開宣言の所有元1,606行（同名721行）を保存した。静的4ケース・header3ケースと、実Leanの失敗再現/補完後成功の2ケースが通った（[結果](bulk-b3prime/B4-regression-complete.json)、[原記録](bulk-b3prime/B4-tool-regression.tar.gz)）。分割された定義・削除wrapper・EInfinityにBS依存を戻すものは保留にする。他のレーンの作業木の変更0。

full verifyは`871516d78`でキャッシュを使わず4ジョブ・32GBで実行。rootと監査前提のbuildは成功したが、監査104／106の時点でプロセス合計RSSが32,190,054,400 bytesとなり、32GBの監視上限で中断した。04:29:26〜04:57:37、1,691秒。30分の上限の前に鍵を返している。[中断の全記録](bulk-b3prime/full-verify-attempt-001.tar.gz)を保存し、成功のsummaryを作っていない。古いverifyのsummaryを今回の成功として再利用していない。

[チェック表](bulk-b3prime/completion-audit.json)は16／17成功、残りはfull verifyだけ。直列のaxiom監査とsorry検査も含むため、完全実行は30分を超える見込みである。指示書§2の通常の30分上限を維持し、full verifyの再実行一回だけ夜の鍵を最長60分使う承認を依頼した。メモリ上限は増やさず、次回はスケジューラに余裕を持たせる。現在は鍵を持たず、次のverifyも要求していない。5∞-3a段0の紙の案は準備しているが、B3′完了報告ではない。


### full verifyの再実行の準備（11-15 05時）

一覧：済み 2／全体 22（うち追加 0）。今回の中断前の104本は公式の入力署名と原ログが一致したが、`verify.sh` のgateは `VERIFY_CACHE != 1` を要求するため、キャッシュによる再開案は取り下げた。キャッシュを有効にしたverifyは実行しておらず、試験準備で隔離したキャッシュも元に戻した。比較器・公開のverify・判定条件は変えていない。

[次回の設定案](bulk-b3prime/next-full-verify-plan.json)は、通常のbulk鍵・wait3600・夜間・4ジョブ、スケジューラのメモリ予算28GB、実測の停止上限32GB。キャッシュなしで全106監査・root・前提・sorryを初めから回す。今回の監視上限超過を避けるためにメモリの余裕を設ける。長い鍵の一回の例外（最長60分）の回答待ちであり、再実行は始めていない。ゲート済みの完了報告もまだ出していない。


## B3′ 完了報告（11-15 09:25）

一覧：済み 22／全体 22（うち追加 0）。基準はmain32d364b53、適用前にmain391b2a0d2をmerge2bbec4f28で取り込んだ。適用の通知は11-15 01:57。本体の適用c42e8b477、監査側の改名/importの修正c2bf2a4fb・871516d78を含む検証HEADは`107d005583fe01dc50b97945f0586063458e48af`。本体のLeanは適用後の保存比較を通した版と同一で、以後の修正は監査側の参照とimportである。

| 検査 | 結果 |
| --- | --- |
| 隔離プレビューの対象ビルド | 220／220成功（importだけの四集約はrootで検査） |
| 実配置のv3b | 29束・214モジュール、比較対象の親宣言4,440→4,439行、wrapper削除1・未説明0 |
| ネイティブな元の全カーネル表 | 18,963行、公開ソースの欠落0 |
| 引用・Kerodon/Stacksタグ | 2,564→2,564、欠落0・余分0・衝突0。実場所も全件有効 |
| 実配置のimportグラフ | 32,043モジュール、欠落0・循環0・EInfinity→BSの直接/間接0 |
| 五段の層 | 既存の節逆順46→46・新規0。層/例外の変更0、346本を規則で登録 |
| root | 32,194 jobs成功。full verifyでもrootと監査前提の二buildが成功 |
| 正式監査 | 106／106成功、すべて一本ずつ。合計4931.6秒、観測最大24.17GB |
| full verify | **PASS・gate:true**。build2・audit106・sorry1成功、失敗/既知扱い0、3036.568秒 |
| B4補助の回帰 | 静的4ケース＋header3ケース、実Leanでimport欠落の再現と補完後の成功を確認 |
| 完了条件 | [全17検査](bulk-b3prime/completion-audit.json)成功、[全22項目](bulk-b3prime/scope-items-complete.json)を照合 |

[全保存比較](bulk-b3prime/actual-preservation-v3b.tar.gz)、[正式監査・verifyの原記録](bulk-b3prime/formal-audits-and-full-verify.tar.gz)、[full verifyの全summary](bulk-b3prime/full-verify-summary.json.gz)を保存した。full verifyは11-15朝の明示承認に従い、昼にVERIFY_JOBS=3・VERIFY_MEMORY_GB=24・VERIFY_CACHE=0で、全106監査を新規実行。10GB超の観測値と従来の大きい監査を同時実行しない組へ入れた。先行する正式監査は共有鍵bulk・wait3600を一監査ごとに返却し、各束30分以内。今回のfull verifyだけは明示承認どおり共有鍵を使わず、一回の時間上限を設けなかった。スケジューラの24GB予算と大きい監査の相互排他を維持し、従来の32GBの緊急停止監視も残した。

正式監査の途中で、短名五ファイルとEInfinity集約から外したBS界面の明示import漏れを修正した。監査の型・述語・必須名・axiom許可を変えず、全監査を通した。同一入力の先行46本の原receiptは編集せず[入力一致の証跡](bulk-b3prime/audit-input-equivalence.json)で保持した。最後のfull verifyではそれらも含め全106本を結果キャッシュなしで実行している。比較器・採取器・publicなverifyの変更0。先の中断したverifyは成功として数えず、[中断の原記録](bulk-b3prime/full-verify-attempt-001.tar.gz)も残した。今回のPASSで再実行の承認待ちは解消した。

### 移動・維持・取り下げ

全体移動70本・切り出し先7本、旧パス71削除（旧wrapper1を含む）。公開ソースの所有元/改名表1,936行（改名1,607）、実在する新しい名前への書換表2,580行。型に属するIsPerfectoidization等のメソッドは実際の型のnamespaceを保つ。CAlg_R三本は削除せずBSへ移し、EInfinityの宣言名を保った。

R7-3(b)は[八辺の実配置](bulk-b3prime/r7-3b-actual-edge-ledger.json)のとおり基準解消2・今回解消5・維持1。DivisionResidue全体のDeltaへの移動は取り下げ、独立した12宣言だけを抽出した。忠実平坦性とNormalizedのAndré依存は残す。BSの元の節順の34辺は[台帳](bulk-b3prime/actual-bs-reverse-edge-ledger.json)のとおり1解消・33維持。IntegralExistenceを分割しても残るTheorem10.11への依存は、解消済みと数えない。PD固有cochainHomotopy、R83/Spectrum、広いR21、未使用宣言の削除は範囲外のまま。これ以外の追加取り下げは0。

Finiteは既存BS定理を直接呼ぶ際に落ちた有限表示性を、**元と同じ明示の引数列**で復元した。未説明の24行を説明扱いへ替えたのではなく、型・本体を実際に直し同じv3bで0にした。root最初の集約headerエラーもimportをdocstringの前へ直して再実行済み。

### B4の資料

[READMEと一行の書換コマンド](bulk-b3prime/B4/README.md)、module-map、所有元付きpublic-owner-map、namespace-rewrite-map、実際のimport元1,606行（同名721行）を渡す。共有の道具は変更せず、資料側のrewrite.pyで公開宣言の所有元を補う。分割元の定義・弱い仮定の削除wrapper・EInfinityへBSを戻す変更は保留にする。[回帰記録](bulk-b3prime/B4-tool-regression.tar.gz)。

| レーン | 枝 | 元環境で採取する本体の候補 | 完全名/旧module文字列一致 |
| --- | --- | ---: | ---: |
| 5a | `math/bs-impl` | 0 | 0 |
| 5d | `math/bs-m15` | 0 | 0 |
| 3a | `math/inf-supply` | 7 | 0 |
| 3b | `math/inf-supply-b` | 180 | 0 |
| 6 | `math/scheme` | 7 | 0 |
| kerodon | `research/kerodon-review-c` | 0 | 0 |

これらは短名も調べるための候補数で、変更が確定した件数ではない。branch/HEAD・manifestはlanes.jsonへ保存。draftsはcollectから外し、本文28本・50箇所の別の文字列の影響表を渡す（保護したA4のP⁰も本文変更0）。将来の置き場所の第一行18本だけは承認範囲で追従済み。他のレーンの作業木/枝への書込み0。mainへの取り込みは調整役が行う。


### 検証中に進んだmainとの境界

今回のfull verifyの対象は上記の107d00558（取り込み済みmain391b2a0d2）である。終了時のmain51723ce33にはその後の非BS本体の増分766パスがあり、BS本体の変更は0。作業木を変えないmerge-treeの予覧ではEInfinity集約は自動統合、監査audit_bhatt_scholze_stage2.leanだけが競合した。新しいmainの行の旧module/変更対象の完全名の文字列一致は0だが、短名は未判定のため[main増分の採取候補763本・一覧・統合予覧](bulk-b3prime/B4/main-increment-handoff.json)をB4へ追加した。六レーンの一部の差分がmainへ取り込まれて候補0になった分も、この別の一覧に含めている。検証した枝へこの増分を混ぜず、主張の範囲を明記して渡す。調整役の取り込みではmain側の監査追加を保持する。統合後のmainが今回のfull verifyを通ったという主張ではない。mainへの書込み0。

## 5∞-3a 段0：一般の多項式 Hodge–Tate 比較（紙の案）

この節は B3′ 完了後の実装前の設計である。Lean の新規定義・定理・証明は追加していない。実在する本体の API と、これから型を設計する候補を分ける。③-b の ∞ 圏の橋は前提にしない。

### 範囲と数学の終点

`stage-ii-second-half.md` の5∞-3aに従い、一般の**有界向き付き** prism と有限変数の完備多項式代数について、既存の `hodgeTateMap` の全次数の全単射性 `HodgeTateIsoStatement P hP r` を示す。任意に選んだ同型の存在で標準のηの同型性を置き換えない。著者版のProp6.2はまず一変数、Thm6.3はétale層の一般の定理なので、この段で実装するのは多項式の古典模型に制限した部分であり、Thm6.3全体を完成扱いにしない。

原典は `paper/refs/BS-prisms-author.pdf`（SHA256 `4cb49a42c80fc734fb7585da273538e09632431ba06709ae05a11ded6673c27a`）、PDF44頁のLemma4.22、51–52頁のConstruction6.1・Prop6.2・Thm6.3。テキスト抽出だけでなく三頁を画像でも確認した。arXiv版の番号に読み替えない。

Cor5.5の一般の結晶prismへの帰結（5∞-0のB06）はこの段で回収する。ただし一般HT比較を使って、その一般HT比較の証明に必要な結晶入力を先に証明したことにはしない。まず既存のZp・多項式の結晶入力を一般の結晶基底へ標準写像ごと移し、その後に普遍向き付き基底、一般基底、公開する系の順にする。

含めないものはCor4.12のCAlg値の底変換、siteのRΓとの同定D27、非向き付き基底・étale層全体、一般のE∞構造。これらは5∞-3b等の持ち分のまま。draftの `HasFiniteCompleteTorAmplitude`・`baseChangeB`・`affineModuleDiagram` に依存する証明は、今回の古典の実型へ置き換える。通常の導来圏の1圏としてのlimitをホモトピーTotの代わりにはしない。

### 既存の入力（現在の本体で存在するもの）

| 入力 | 実在する場所・API | そのままでは主張できないこと |
| --- | --- | --- |
| 完成と擬同型の保存 | `HomologicalAlgebra/DerivedCompletion/ComplexCompletion/Basic.lean` の `complexCompletionFunctor` と擬同型保存 | 底変換と無限の積の可換性は別途必要 |
| 積全複体 | `HomologicalAlgebra/CochainProductTotalizationHomotopy.lean` の `cochainProductTotalizationFunctor` | 全ての余単体的導来図式の関手的な模型を既に持つという意味ではない |
| 有限完全Tor振幅 | `HomologicalAlgebra/CochainCompleteTorAmplitude.lean` の `HasCochainCompleteTorAmplitude`、`exists_cochainCompleteTor_model` | 後者の対象ごとの分解の存在から、関手的な半自由分解を仮定しない |
| Construction6.1の保存性 | `BhattScholze/Prismatic/HodgeTate/Comparison/CrystallineCover/Construction61Reflection.lean` の `quasiIso_of_completedCover_semifree_map_quasiIso` 等 | K-flat性・完備性・指定された比較射という前提を落とさない |
| 同じ被覆のTor入力 | 同ディレクトリの `CrystallineCoverCompleteTor.lean` | Koszul版の幅3と、mod pの普通のTor幅≤1を区別する |
| 項ごとのprism底変換 | `Prismatic/CechAlexander/Comparison/AffineCechPrismBaseChange.lean` の `cechAlexanderAffine_baseChange` | 項ごとのδ同型からTotやηの比較まで済んだとはしない |
| 厳密な多項式作用 | `Prismatic/HodgeTate/Affine/HodgeTateAffineModel.lean` の `htSec`、`HodgeTateModule.lean` のprivate `htCoefficients` | 必要なら既存データの公開wrapperを作る。新しい作用の存在を仮定しない |
| 実際のR線形複体 | `HodgeTateModuleComplete.lean` 内の `toModules R X ι` と `alternatingCofaceMapComplex (ModuleCat R)` | `reducedModel` 自身は余単体的環であって鎖複体そのものではない |
| 標準ηと終点 | `HodgeTateCompletedMap.lean` の `HTAlgebraMap`、`hodgeTateMap`、`hodgeTateMap_unique`、`HodgeTateIsoStatement` | `affineForms` は既に完備形式である。未完備の自由加群計算だけで完備版の結論に飛ばない |

[既存API13件の場所・ソースハッシュ](bulk-5inf3a/existing-api-inventory.json)も保存した。これは静的なソース一覧であり、新しい比較射のLean型検査ではない。

### 項目と実装順の案

| ID | 作るもの・受け渡す型の要件 | 確認する出口 |
| --- | --- | --- |
| HT01 | 既存の厳密な余単体的R加群模型と、その積全複体・cohomology同一視を公開する最小のAPI | 元の `hodgeTateCohomology'` とη⁰・η¹との可換図式。標準写像を保存 |
| HT02 | Lemma4.22の鎖複体版：有限生成J、`HasCochainCompleteTorAmplitude f x c`、一様に下に有界な余単体的入力について、**自然な**完備導来底変換–Tot比較射とその擬同型性 | 冪のKoszul塔・有限切断・尾部の一様下界。任意の非有界な余単体的入力へ拡張しない |
| HT03 | Zpの結晶計算を一般の結晶prismの多項式模型へ移す。原典の平坦性の前提と標準脚、向きによるBocksteinの係数を明示 | draftの `hodgeTate_iso_crystalline` が意図する型。一般HTを仮定せずに得る入力 |
| HT04 | 普遍向き付き基底について、Construction6.1のαによる比較とHT02を接続し、既存の保存性で標準ηの擬同型性を戻す | 一変数のProp6.2とその指定された比較写像 |
| HT05 | 一般の有界向き付き基底へ戻し、有限変数へ拡張。形式の積・完成・Bocksteinと既存ηの一意性で照合 | 全rについて `HodgeTateIsoStatement P hP r` |
| HT06 | Cor5.5の公開する系、対応表、専用監査、保留したdraftの項目との照合 | 系が一般の結晶入力と循環しないこと、全次数で標準ηそのものを検査 |

HT02では元の有限列のTor条件から冪のKoszul塔に必要な一様の下界を渡す補題も証明する。新しい比較射のLean名・完全な引数列は未確定で、ここではLean型検査済みのsignatureを提示しない。候補の実型は、環C→S、有限列x、自然数c、C加群の厳密な余単体的鎖複体から、既存の積全複体模型上の完備導来底変換比較を作るもの。原典のD≥0条件を模型に反映し、一般の∞圏のlimitの追加を要求しない。固定したK-flat係数分解を用いてC線形で自然な比較を作り、S線形の標準写像へ制限後の模型比較で接続する案を最初に検査する。これは実装の候補であり、係数分解に架空のS作用を仮定しない。対象ごとの半自由分解を勝手に余単体的な分解へ束ねることもしない。

HT04–05では原典52頁の一般基底への帰着をそのまま追う。A₀→Aを有限Tor振幅や平坦と仮定しない。制限したK-flat複体が自動的にK-flatだとも仮定しない。比較の模型と合成を明示する。prismの射でf(d)=u d′となるとき、向きの単元とBocksteinの正規化の式を確かめる。ηの底変換の係数を1と決め打ちしない。

### 終点の型と補題の型の案

本体へ置く公開終点の案は、現行draftと同じ次の型である（この段では未実装）。

```text
-- namespace SerrePositivity.BhattScholze.Prismatic
-- {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
-- (P : OrientedPrism p A)
affineLine_moduleComparison (hP : IsBoundedPrism P) :
  Function.Bijective (hodgeTateMapZero P hP 1) ∧
  Function.Bijective (hodgeTateMapOne P hP 1) ∧
  ∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' P hP 1 i)
hodgeTate_iso (hP : IsBoundedPrism P) (r : ℕ) :
  HodgeTateIsoStatement P hP r
hodgeTate_iso_crystalline (hcrys : P.generator = (p : A)) (r : ℕ) :
  HodgeTateIsoStatement P (crystallineBounded p P hcrys) r
```

HT02は、環射f:C→S、有限列x（J=(x)）、幅cとその有限完全Tor条件、厳密な余単体的C線形複体K、各項がD≥0に属するという条件から、自然な比較射
`BĈ_f(TotΠ K) → TotΠ(BĈ_f K)` の `QuasiIso` を得る型を目指す。これは数学的なsignatureの案で、未定義のBĈをLeanの既存名のように扱わない。項ごとのホモロジーの下界を、勝手に複体の各成分の零条件へ置き換えない。半自由模型の選択をした場合は、比較射の自然性と模型への非依存を別の法則の補題として確認する。

### B06とdraftへの返却

`drafts/A1/HodgeTateComparison.lean` の `hodgeTate_iso_crystalline` と `hodgeTate_iso` は、この段の本体定理と同じ型を目指す。本体へ同じ完全名で昇格するdraft宣言は重複を除いてimport経由で使い、中間補題の名前が異なる場合にだけ委譲を書く。旧報告B06の `deRhamComparison` という表記は、本体BSと全draftの双方に該当する宣言がないため訂正する。存在しない名前を実装対象に数えず、現行の `affineLine_moduleComparison`・`hodgeTate_iso`・`hodgeTate_iso_crystalline` の上記の型で返却先を示す。Cor5.5の古典的な帰結を、CAlg∞の比較やCor4.12と混ぜない。一般の結晶比較をZpの特殊場合で置換して完了とはしない。

### 規模・検査と最初の停止点

新規のLemma4.22の模型と自然性が主な不確実性である。HT01とHT02の型・比較射をまず一つの小さい束にし、既存のK-flat/完備化APIへ無理なく接続するかを検査する。この時点で、追加の一般の導来関手や型の変更が必要になれば、数学の範囲を広げず報告する。HT03–06はその出口を固定してから実装する。

初期の行数見込みは、HT01の公開wrapperが100〜300行、HT02が1,500〜3,000行、HT03〜HT05が計1,200〜3,000行、HT06の監査・draft追従が200〜500行、合わせて**約3,000〜7,000行**。新規のLemma4.22の自然性・模型比較が上端を左右する。共通の規模の規則に従うなら外枠は上端の2倍の14,000行だが、これはこの段0での実装承認を意味しない。見込みの半分に達した時点で実測と残りを報告する。

時間の見積りは**API確認とHT02が2〜4日、結晶入力・普遍/一般基底・有限変数・監査が追加2〜4日、全体4〜8日程度**の作業幅とする。新しい鎖複体版のLemma4.22に実測はなく、B3′の移動の実測をこの数学の所要時間へ換算しない。初回のHT02の型検査と対象ビルドの後に見直す。既存のHT比較の古い行数見積りだけで全体を約束しない。

実装段の各束は対象ビルド、標準ηとの可換性、axiom/sorry監査を行う。Zpの既存ケースだけでなく、一般の有界向き付き基底を引数に持つ終点を監査する。既存の本体の無関係な型や数学を変えない。段0ではLeanの変更0、ビルドの鍵の使用0。**紙の段0を提出し、数学の実装は承認後に進める。**

一覧：済み 0／全体 6（うち追加 0、HT01〜HT06の実装件数）。段0の調査・設計を提出する。数学の実装はこの段0の範囲に含めない。


## 5∞-3a 着手（11-15、承認後の実装）

一覧：済み 0／全体 6（うち追加 0）。新しいactive目標とmain7e03e17a7のbulk-5inf3a.md §1の承認を受け、B3′の枝を保持して、336942ab0から`codex/bulk-5inf3a`へ分けた。mainのB3′取り込みは調整役が行う。HT01・HT02を最初の束とし、外枠14,000行、約7,000行の途中報告を守る。

[作業中の一覧・ソースhash](bulk-5inf3a/implementation-progress.json)を保存した。ここで記した新しいLeanはまだ型検査前で、成功の件数には入れない。HT01は既存のprivateな係数射を同じまま公開し、厳密な余単体的R加群・cohomologyの線形同値・cup積・標準ηの次数0/1との照合を記述した。HT02は固定した係数の実際の半自由分解を使うR線形の模型と、K-flat入力での通常の係数拡大への自然な比較、主元の冪と完備化の下界、積全複体の対角線の完全性を記述中。係数分解にS作用を仮定せず、余単体的入力の分解を対象ごとの存在から勝手に束ねない。

最初の対象ビルドはbulk・wait3600・280秒の束で一つだけ並べた。B3′の鍵の免除は使わない。HT02の実測と残りの見込みの報告は、既存K-flat・完備化APIへの接続を実際に型検査した後に行う。現時点ではこの節をその検査済み報告として扱わない。

監査への登録案は、BS stage IIからAffineCochainMapとTotalizationのLowerBound・CompletionBounds・ResolvedScalarExtensionをimportし、標準ηとの同値、K-flat比較、実際の完備化/全複体の下界のkernel型とaxiom閉包を検査する形。型検査で定まった公開APIと合わせて本体に登録する。HT03〜HT06の終点を先に仮定したり、定理名だけを足して監査に数えたりしない。


### HT01・HT02の第1束の検査（11-15）

一覧：済み 0／全体 6（うち追加 0）。通常のbulk鍵を取り、束002は7対象を逐次検査して約48秒で返却した。[検査記録](bulk-5inf3a/first-bundle-001-002.tar.gz)と[現在のソースと一致する成功](bulk-5inf3a/first-bundle-checkpoint.json)を保存。Totalization/Componentsの103行が型検査成功。これは全複体の成分・微分・行の完全性のAPIの成功であり、Lemma4.22自体の完成ではない。

HT01のprivateデータを公開値へ無理に露出しない形、存在証明から固定係数データをClassical.choiceで選ぶ形、自然性の射の結合順、整数添字とModuleCatの射の評価を修正して、束003を同じ280秒の通常の鍵で並べた。HT02の固定K-flat係数模型・実際の完備化・Totの下界の連結は、この検査が通った後に実測をまとめる。型が通っていない終点や補題を成功扱いにしない。他のレーンとmainの作業木の変更0。

### 5∞-3a：固定係数模型の対象検査（11-15 朝、継続中）

bundle-004 で `AffineCochainModel`、`Totalization.Components`、`Totalization.ResolvedScalarExtension`、`Totalization.ColumnPrimitive` の4本が通った。検査時の SHA256 と現行ソースの一致を確認した分だけコミットする。既存の非有界半自由分解から固定係数模型を構成し、そのテンソル関手の擬同型保存、K-flat 入力の通常の底変換への比較射、その自然性、実際の主元完備化関手への接続が型検査済みである。係数模型に架空の標的環作用を付けていない。

HT01 の標準ηの公開判定、HT02 の完備化の下界・積全複体の対角線の下界は検査で出たエラーを修正中。これらの完了、および自然な完備底変換–Tot比較射の擬同型性はまだ主張しない。次の束を通常の bulk 整理券（--wait 3600、昼280秒以内）で待機中。検査記録は `bulk-5inf3a/checked-api-checkpoint.json` と `first-bundle-003-004.tar.gz`。

一覧：済み 0／全体 6（うち追加 0）。承認された HT01・HT02 を続行する。

### 5∞-3a：HT01・HT02 の既存 API 接続の実測（11-15 10:51）

`bundle-006` は **10/10 本成功**。現行ソースの SHA256 は全件検査時と一致し、新規10モジュールの **206 宣言（生成宣言を含む）の公理閉包は標準三公理のみ**。検査記録は `bulk-5inf3a/first-api-connection.json` と `first-api-connection-005-006.tar.gz` に保存した。

実測は新規 Lean **1,101 行**（HT01 の係数線形模型と標準ηの照合215行、HT02の補題886行）。最新の10本の対象ビルドの累計46.85秒は、前提のキャッシュがある対象検査の値で、rootや凍結の時間の推定ではない。着手の記録コミット9b07c9f22（10:15:59）からこの確認まで約35分だが、その記録以前の作業を含む総実装時間の計測ではない。共有鍵は通常のbulk整理券、各束280秒以内を守った。

接続済みの実型は、任意の非有界入力に対する固定K-flat係数模型のテンソル関手、その標準の通常底変換への比較（入力K-flat時に擬同型）、任意の有限列に対する `HasCochainCompleteTorAmplitude` から同じ模型のKoszulホモロジーの下界、主元の実際の `complexCompletionFunctor` 後の下界、行簡約した積全複体の下界である。一般の有限列のTor条件を主元の場合へ弱めてHT02全体を済んだとはしていない。積全複体の下界は項ごとの有界性を追加せず、対角線のコホモロジーの零性から原始元を構成した。

自然なテンソル–Tot比較は、直和と積の普遍性から次数ごとの射を構成し、符号 `(-1)^(a*n)` の公式まで型検査した。**鎖写像性・自然性、有限切断との比較、有限生成イデアルの冪と完備化を通る最終的な擬同型性は未完了**。HT01も積全複体への公開同一視を仕上げてから完了に数える。

HT02の残りは約1,200〜2,600行、HT02合計約2,100〜3,500行へ見直す（当初1,500〜3,000行の上端を少し超える見込み）。主な残りは鎖写像性と自然性、有限切断と尾部、有限列の冪・完備化、最終比較である。所要は追加2〜4作業日程度の幅を保つ。鍵の待ちと数学の実装時間を分け、今回の小さい対象ビルドだけで完成時刻を約束しない。HT03〜HT06は未着手。新たな範囲の追加はなく、外枠14,000行内で続行する。

一覧：済み 0／全体 6（うち追加 0）。このAPI接続の報告を記録し、停止せずHT01・HT02の束を続ける。

### 5∞-3a：HT01 完了（11-15 朝）

`AffineTotalModel.lean` で、元の係数線形余鎖模型を整数次数へ零延長し、縦次数零の二重複体の指定積全複体として公開した。既存の `ProductTotal.singleRowIso` の指定射影と `extendHomologyIso` を用い、元のコホモロジー・標準ηへの射影公式と、元の `HodgeTateIsoStatement` との同値を型検査した。元のHT同型性を仮定せず、別の任意のηや作用を選んでいない。η⁰・η¹と積は前の `AffineCochainMap` の公式を同じ指定射影で受け取れる。

`bundle-007` は **11/11本成功**、新規11モジュールの**232宣言の公理閉包は標準三公理のみ**。全ソースのSHA256が検査時と一致する。記録は `bulk-5inf3a/ht01-checkpoint.json` と `ht01-bundle-007.tar.gz`。BS stage IIの登録案はHT01の葉を `Comparison.AffineTotalModel` にまとめ、HT02の完成した葉と一緒にimport・所有元一覧へ加えるもの。現在の本体の一括監査の登録はまだ変更していない。

一覧：済み 1／全体 6（うち追加 0）。HT01を完了とし、HT02を続行する。

### 5∞-3a：HT02 の尾部の下界と零行の比較（11-15 午前）

`TailBounds.lean` で、最初のN行が零で残る各行のコホモロジーがb未満で零なら、指定積全複体のホモロジーがN+b未満で零となることを証明した。さらに既存の完全Tor上界cの後の行簡約の全複体ではN+b−c未満で零となる。尾部で零にする行以外に項ごとの有界性は仮定しない。

`TensorZeroRow.lean` は指定零行射影を鎖写像として作り、その自然性、標準テンソル–Tot比較の次数成分との可換性、および零行での微分との可換性を型検査した。依存する次数の輸送は等式からの射で明示し、既存の積全複体の符号のスコープに揃えた。正の行での微分との可換性はまだ未完了で、全体の鎖写像や擬同型性を済んだとはしない。

対象検査はTailBoundsがbundle-009で成功、TensorZeroRowがbundle-013で成功。現行ソースと検査時のハッシュは全件一致し、**新規13モジュールの256宣言の公理閉包は標準三公理のみ**。証跡は `bulk-5inf3a/tail-zero-row-checkpoint.json` と `tail-zero-row-008-013.tar.gz`。通常の共有鍵を使い、各束は280秒以内。

一覧：済み 1／全体 6（うち追加 0）。HT02の正の行の比較と有限切断を続行する。

### 5∞-3a：HT02 の随伴による比較鎖写像（11-15 午前）

既存の `ProductTotal.homTotalIso` と `tensorHomEquiv` を用い、行ごとの随伴の単位を積全複体へ移して逆転置する標準比較 `tensorTotalComparisonInt` を作った。任意の整数横次数の二重複体について**鎖写像として構成し、二重複体の射に関する自然性を証明した**。任意の同型を前提にせず、同じ単位と指定されたHom–Tot同型の逆を用いている。比較射の擬同型性はまだ主張しない。

`ExtensionRows.lean` は、非負横次数で指定した射から、元の図式の零延長を始域とする鎖写像を構成する法則を与える。標的の負の行の零性を追加せず、始域の零性で境界を扱う。これを使って、最初に固定した非負横次数のTot模型への接続を検査中である。指定された符号付き次数成分との一致、有限切断、有限列の完備化後の擬同型性は残っている。

`TensorAdjointComparison` はbundle-015、`ExtensionRows` はbundle-016の対象検査に成功。現行ソースのハッシュを確認し、**新規15モジュール・293宣言の公理閉包は標準三公理のみ**。証跡は `bulk-5inf3a/adjoint-comparison-checkpoint.json` と `adjoint-comparison-014-016.tar.gz`。鍵は通常のbulk、各束280秒以内。

一覧：済み 1／全体 6（うち追加 0）。HT02を継続する。

### 5∞-3a：HT02 の指定非負模型への接続（11-15 午前）

`TensorNaturalComparison.lean` は、随伴の単位を非負行で取り、`extendRowHom` で零延長の始域からの射へ延長した後、指定されたHom–Tot同型で逆転置する。これにより、始域 `cochainTensor L (total K)`、終域 `total (tensorRows L K)` の比較 `tensorTotalComparison` を**鎖写像として型検査した**。始域・終域の積全複体は最初に固定した同じ `cochainProductTotalizationFunctor` の値である。

対象検査bundle-017に成功し、現行ソースと検査時のハッシュの一致を確認した。**新規16モジュール・316宣言の公理閉包は標準三公理のみ**。証跡は `bulk-5inf3a/nonnegative-comparison-checkpoint.json` と `nonnegative-comparison-017.tar.gz`。非負横次数版の自然性、元の符号付き次数成分との一致、有限切断、完備化後の擬同型性はまだ残る。

一覧：済み 1／全体 6（うち追加 0）。HT02を継続する。

### 5∞-3a：検査待ちの間の HT02 の整理（11-15 昼）

通常のbulk整理券でbundle-021を待つ間に、残る有限切断・完備化の証明経路を `bulk-5inf3a/ht02-next-proof-route.md` に保存した。既存の局所化のHomによる完備性の判定の型を確認し、零延長と加法的関手の指定同型、および行ごとの完備性をTotへ渡す補題のソースを用意した。これらはまだ対象検査前であり、完了扱いにしない。固定した正の二項Koszul複体のtelescopeのHomとして、本体の主元完備化と単位を表示する案も記録した。この自然同型と単位の一致は、今後型検査してから使う。

進捗の入口 `bulk-5inf3a/implementation-progress.json` を、検証済みHEAD24023c875・HT01完了・最新の全件公理監査316宣言と、作業木の未検証部分を分けて更新した。鍵のスクリプトはmainと差がないことを確認した。待機中の束は最初の2本と監査が通ったときだけ関連4本へ続く形にし、全体280秒の上限を保持する。共有鍵の要求は一つだけである。

一覧：済み 1／全体 6（うち追加 0）。HT02の未検証部分を準備し、通常の検査の順番を待ちながら続行する。

### 5∞-3a：昼の整理券の再要求と残る証明経路（11-15 昼）

bundle-021 の最初の要求は3600秒でrc75となり、ビルド自体は始まらなかった。通常の規則のまま一件だけ再要求した。共有鍵の免除や別の待ち要求は使っていない。束は引き続き全体280秒で打ち切る。

待ち時間に、完備な行のTotの完備性を用いて、元の標準鎖写像に完備化を施し、標的の標準単位だけを反転する比較とその単位の合成公式を用意した（`CompletedComparison`）。始域・終域は本体の完備化と元の指定Totのままである。この経路なら無限Totと完備化の直接の交換を先に証明する必要はなく、有限頭部と尾部の評価に分けられる見込みである。`NaturalTruncation` には横次数だけを切る頭部・尾部、射影・包含と既存の尾部評価との接続を用意した。**追加ソースは未検証で、HT02の擬同型性は未証明**。前のHom表示は未実装の代案としてメモに残す。

現在の束は、最初の2本と17モジュールの公理監査が通ったときだけ、関連6本へ逐次進む。失敗があれば成功した対象だけを別途公理監査し、未確認のものと分ける。直近の全件監査済み数学HEADは24023c875、316宣言のまま。今回の基準336942ab0から追加した23本、2,335行（未検証部分を含む）のハッシュと行数は `implementation-progress.json` の `working_source_inventory` に記録した。既存のComparison配下の本はこの規模に含めない。

一覧：済み 1／全体 6（うち追加 0）。HT02を継続する。
