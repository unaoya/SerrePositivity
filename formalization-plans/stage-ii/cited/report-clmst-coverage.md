# 現在地

- 段：**KB-W1 / B6 進行中**。
- 一覧：**済み 8／全体 10（章）**。
- 作業場所：`/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-cited`。枝：`research/cited-coverage`。pwd一致を確認し、指定の `git merge main` を実施。
- KB-W1基準HEAD：`f35b01be9fdb8cf3c664b32123b6e8ebaf5d070f`。章ごとにコミットし、2章ごとに停止せず途中報告する。
- 次：第9章の型と原文を再照合する。Lean・ビルド・鍵は使わない。既存 own・both・mathlib 行は変更しない。

## CC-W1 納品（停止コミット `156ac3c32`）

`research/clmst-coverage/` に toc・12列の items・review/ch1–ch8・4列の edges・none 全件の検索表を作成した。状態の正本は review で、items の status・declarations・reason は空欄。

全 **147項目**（数値番号つき環境123、Theorem A–G 7、表示式17）。Definition・Theorem・Lemma・Proposition・Corollary・Remark・Example に加えて Claim・Caution・Convention・Notation・Conjecture・Question を含む。本論文の引用項目だけに限定していない。

状態：**own 4、mathlib 0、both 0、partial 20、interface 6、none 117**。引用・導出辺は **572件**（internal 344、external 228）。各項目の仮定・結論の差と対応宣言は対応表に置いた。

## 判断上の要点

原典の一般項目に対し、単項イデアル、特定の基底イデアル、代数係数・零次ホモロジー、パラメータ生成イデアルだけに対応するものは partial とした。Proposition 2.4.9 の (a) の単項版を、一般 J の忠実性・純性まで含む項目全体として扱っていない。2.2.6(a) の加法性と項目全体の colimit の範囲も区別した。

Corollary 4.0.4・Proposition 4.0.10・4.0.14 の型は原典の範囲と照合したが、標準 perfectoid 化の存在には E3 の sorry 入力へのソース上の依存が残るので interface とした。本文に直接 sorry がないことを、依存先も含めた kernel 検証の代用にしていない。

原典の印刷番号と PDF 内部リンク名に相違がある。導入の記号つき式 `(*)` も採用したため表示式は17件。印刷 `(6.0.1.1)` のリンク名は `equation.6.2.2.1`、Definition 8.5 のリンク名は `conjdef.8.5`。表には印刷された番号・種類を採用した。CLMST の [BS22] の刊行版番号を、登録済み BS19 著者版番号と同一視していない。

既存表との範囲・版の注意点は対応表 README に記した。既存の対応表を変更していない。

## 検証・証拠

PDF は指定の `../SerrePositivity/paper/refs/CLMST-2209.04046v4.pdf` を読み取りのみで使用。SHA-256 は `0001a9a56839319b5d36c79fcd0dedc9dd66ac0b38029773d923fa4037f944fa`（88ページ）。テキストの項目採取を PDF の named destinations と独立照合し、123個の数値番号つき環境と17個の式の集合・ページの一致を確認した。Theorem A–G は本文で確認。p.33・68 を描画して表示番号と引用箇所を目視した。

全147件の review、none 全117件の検索、キー一意性、12列形式、状態の正本、内部辺の両端、採用宣言36件の位置・型・本文・指紋を静的に検査。検索範囲は本体33,542・Archive1,871・Mathlib8,602ソース。Mathlib の revision は lake-manifest と一致した。

大きい採取記録・検索結果・宣言抜粋・ソース指紋・独立 PDF 照合記録・作成／検査スクリプトは `~/serre-evidence/cited/clmst/` に置き、目録のみ `evidence/cited/clmst/manifest.json` に保存した。目録の commit は監査対象の `9bfb015051ee96dd2b3d24c6e63801aa61de4a07`。目録は指定の `scripts/docs/evidence_manifest.py` で生成。

Lean コードの変更、Lean 実行、ビルド、`lake env lean`、PDF の複写・変更はしていない。ここで紙資料をコミットして停止する。


## CC-W2：本論文が引用する外部結果

`git merge main` を実行し Already up to date を確認。現在の基準 main は取り込みコミット `63622412d`。指示書 §3 と今回の指示に従い、`research/paper-coverage/external.csv` を6列で作成した。

external **78辺の先の全47種類**を漏れ・余分なしで収録。番号なしの文献は number を空欄に保った。**25行**（CLMST 7、BS19 1、K 文献17）は status・declarations を空欄にし、reason に既存正本のファイル・実在する行番号キーを指定した。CLMST の状態は review から読む。既存表の状態を複製しない規則を README に記した。

単発文献 **22行**の判定は **own 4、mathlib 2、partial 10、none 6**。原典の一般形に対する整域・完全剰余体・パラメータ Koszul・Noether 基底・構造層などへの特殊化は partial。none 全6行の検索記録を残した。採用宣言の一覧は external.csv と証拠に置き、本報告には転記しない。

Ma17「2.2」の補題と節の共用、BGT「9.3」と式 `(9.3)` の区別、LT Appendix B／Drinfeld 3.1／TT のまとめ行の正本キーを明示した。KuranoShimomoto の番号なしと1.1の辺は二行として保持。これらの番号解釈の注意点は README に記し、既存の edges や他文献の対応表は変更していない。

各引用箇所と主張・宣言を静的照合し、採用宣言17個の型・周辺条件・本文・指紋・直接 sorry を点検した。CSV の列、キー一意性、78辺すべての照合先、25行の参照先の実在、6行の none 検索、既存表の不変更を検査。Lean の変更・ビルド・実行・kernel 依存検査はしていない。

原著本文の取得範囲には限界がある。Roberts89 は Ma17 2.4 の再掲、Roberts85／Gillet–Soulé／Serre は本論文が使う主張と現行ソースを中心に照合し、書誌と取得失敗も記録した。Monsky の一般存在主張は Ma17 §2.2 の再掲と本論文の引用でも確認した。未取得の原著全体を点検済みとはしていない。

CC-W2 の証拠を `~/serre-evidence/cited/clmst/cc-w2/` に分離し、`scripts/docs/evidence_manifest.py` による目録だけを `evidence/cited/clmst/cc-w2/manifest.json` にコミットする。目録の監査対象 commit は `63622412df745e41206647c4e57778b7060a840d`。CC-W1 の証拠目録は保持する。

停止点は、この外部引用表・README の追記・本報告の現在地更新・CC-W2 証拠目録を含むコミット。ブループリント生成器や Lean へは進まない。

## NB-W1

### 納品

`research/kerodon-coverage/notes/` に14項目の `1.x.y.z.md` と5つの導入・つなぎ原稿、全段落の移動表を持つ README、所見と未配置本文を持つ issues.md を作った。凍結中の t-01〜t-05 を読み、文言・旧番号・数式を保った Markdown に転記した。項目は item-tags.csv と照合し、本文外に既存 review の Lean 名を記す。標準単体 1.1.0.9・部分単体的集合 1.1.0.14 は項目表と Tag にあるが180件の review にないので、状態や宣言を推定して付けていない。

入力は43環境・88本文ブロック（p・li・表データ行）。41ブロックを番号別・節別原稿へ置き、47ブロックを issues.md の未配置本文へ全文保留した。README は88ブロックを一件ずつ列挙する。CSS・ナビゲーション等を除く本文の未記録は0。

### 主な所見

指示書の「第1章にあたる解説」という入力範囲と実際の章立てに差がある。coherent nerve は第2章、空間の∞圏は第3章、join・slice は第4章であり、第1章の導入へ無理にまとめていない。章外47ブロックは第1章用の生成対象外として保留し、未配置理由と候補を README に、全文を issues.md に置いた。t-05 の5行の表も trivial Kan の行だけ第1章で、導入・残り4行を分けると「次の表」の指示先が途切れる。この点を所見に明記した。

一段落が1.1.0.6と1.1.0.7等の複数項目にまたがる場合は文言を切り直さず主たる項目へ一度だけ転記した。式を挟む複数pは同じ原稿内の順序を維持。元のページ内・ページ間リンクは表示文言を保って新しいブロックのアンカーへ移した。research の引用規則と原稿間リンクの区別は未決として記録し、恒久の配置は決めていない。

issues.md には表・囲み（env）・cases等の数式・リンク・来歴アンカーとリストを例示した。対象5ページには画像・pre・div.box はなく、それらの変換は試せていないと明記。旧番号と Kerodon の番号・種類の差、Kan 定義での正次数条件の省略、coherent nerve の包含順の規約差も原文を変更せず所見に残した。

### 検証・証拠

88ブロックの表示テキストを転記後と照合し、本文中の295数式片（区切り・内部TeX）を逐一比較した。88個のブロックIDは重複・欠落なし。README の全行と原稿内リンクの実在アンカーを照合した。入力HTML5ファイル・対応表3ファイル・生成器の計9ファイルは基準HEADと同じハッシュで、変更していない。Lean の変更・実行、Verso・Lean のビルド、ブラウザーでの描画確認はしていない。

証拠は `~/serre-evidence/cited/notes-kerodon1/`。段落対応・元リンクと移設先・入力と出力のハッシュ・検査結果・段限りの転記/検査スクリプトを保存した。コミットするのは `evidence/cited/notes-kerodon1/manifest.json` の目録だけ。目録の commit は基準HEAD `02fd6ba06408721b5fa593a56ea5eebcfa31f2ae`。今回の原稿は生成器に接続せず、このコミットで停止する。

## AR-W1

### 途中コミット：群分けと主要宣言

Archive 全体を83群に分け、`research/archive-review/groups.csv` と `filtered-exchange-inventory.md` に主要宣言の一覧を置いた。FilteredExchange は68群・1,726本・96,551行。全体では1,871本・109,913行。大きい CoherentColimit と CoherentCospan は細分し、小さい接頭辞は名前空間・import と共通の操作を見てまとめた。

これは途中版で、主張・文献・対応・目標・推奨はまだ空欄。各群3〜9個の主要宣言を抽出し、その型と周囲の変数を次に読む。抽出の全結果は git 外 `~/serre-evidence/cited/archive-review/`、目録は `evidence/cited/archive-review/manifest.json`。このコミット後も停止せず、照合を続ける。Archive・本体・対応表・Lean は未変更、ビルドしていない。

### 最終の紙と集計

`research/archive-review/` の groups.csv（指定12列）・FilteredExchange の群別主要宣言一覧・README・kerodon-rows.md を完成させた。全1,871本・109,913行を85群へ一度ずつ割り当て、各群3〜7個、計420個の主要宣言または匿名 example の型・文脈・定義の右辺を読んで主張を書いた。最初の68群から復帰候補の小群を分離し、FilteredExchange は最終70群・1,726本・96,551行。

| 推奨 | 群 | 本数 | 行数 |
| --- | ---: | ---: | ---: |
| 戻す | 2 | 5 | 320 |
| 材料として残す | 10 | 161 | 13,171 |
| 消してよい | 6 | 69 | 5,780 |
| 判断できない | 67 | 1,636 | 90,642 |

大半について削除可能と結論したものではない。主要型を読めても、旧モデルの比較式を現 API に完全に置き換えられるか、P⁰・BS・K の主張の証明に独自の部品として要るかは確定できず、その範囲を判断できないとした。全文の全証明を逐行査読したとは報告しない。

### 数学の中身からの推奨

復帰候補は FilteredDiagonalCriterion・FilteredKanContractibility・WeakContractibilityNonempty の3本と、ConeMappingRestriction・SliceRestrictionRightFibration の2本。本体の必要方向だけに対して、filtered 性の coslice 弱可縮性/対角 cofinality による逆判定がある。後2本は slice/right fibration 側を補い、本体の coslice/left 側と同一視していない。対応先と復帰先の案は groups.csv と README に記載。P⁰ 閉包の Kerodon 9.1.1.18・9.1.5.7・4.3.6.12 に根拠がある。Kan 同値9.1.1.20は閉包外だが既存表の own の根拠を是正する対象。

旧余極限経路には座標補助だけでなく、filtered な底の有限族を同じ fiber へ移す、境界を固定する、元の余極限頂点の cospan 極限錐を輸送する数学がある。4群94本は Kerodon 9.1.5.7 の証明材料として残す案。ただし一般の有限極限交換の本体は既に `smallSpaceFilteredColimit_map_isLimit_finite` と `coherentFilteredLimitExchangeShape_finite` にあり、1,726本を一般交換のため一括復帰する根拠にはしていない。

DG の68本は匿名 example 261個、名前付き17個の標数2/特定次数・成分への検査を含む。名前付き17個についても本体の一般定理の型・適用を並べて確認した。5群は数学を失わずに消してよい案だが、検査資産としての価値は別。WIP RelativeFiller 1本も、本体の一般の相対ホモトピーを pushout-product に適用する wrapper と確認した。合計69本を数学的な削除可の候補とした。

DescentConditional 67本はKの地図 maps/paper/items.csv の required な3.2・3.3の計算材料として残す案。ModelCategory・cofibrant generation・Quillen 条件や既存の Čech 降下/転送階数式を仮定した型であり、係数 L 自身への適用の不足を解消してはいない。既存の型クラス合成失敗の記録を、仮定の論理的矛盾と取り違えていない。BS の個別の必須項目との対応は確定しなかった。

### Kerodon 行・sorry・import

Archive のパスを宣言欄に含む4行（4.3.6.12、9.1.1.18、9.1.1.20、9.1.5.7）と、理由欄だけの9.1.8.11を記録。9.1.1.20は型の主張は原典と一致するが Archive だけの宣言を own に数えられない。本体の filtered⇒弱可縮⇒可縮Kan という一方向を根拠に partial とする案を示した。他の行は partial 維持。原典を Tag で照合し、02PJ の単独取得タイムアウトは同じ命題の小節02P8で補った。対応表は未変更。

コメント・文字列を除く直接 sorry と新規 axiom 宣言の検出は全群0。ただし依存先までの kernel 公理検査はしていない。各群の本体/Mathlib の現名あり・改名候補・所在未確定をユニークなモジュール数で記録した。改名候補は末尾の名前だけの一致で、互換性確定とはしない。現本体33,542ファイルには Archive の直接 import が見つからなかったが、DGκと条件付き降下にはそれぞれ専用の監査スクリプトから import がある。

### 最終検証と証拠

85群の列・全1,871本の一意な割当て・行数・420個の主要宣言のソース位置・本体の比較宣言の位置・原典番号/P⁰閉包の該当番号・5つの対応表参照行を検査した。Archive 全ソースのハッシュと基準HEADからの変更なしを確認し、本体・exposition・blueprint・対応表・lake設定・toolchain も変更していない。Lean の変更・実行・ビルド・kernel 確認なし。

証拠は `~/serre-evidence/cited/archive-review/`。途中時点の5ファイルを上書きせず保持し、最終の抽出・型比較・import・DG特殊化比較・原典取得・検証は `final/` に追加した。コミットするのは `evidence/cited/archive-review/manifest.json` の目録だけ。目録の commit は基準HEAD `7c2528f6594b63074e7955f2f0c57db15ace4e2e`。この最終の紙をコミットして停止する。

## KB-W1

指示書と codex-review.md §6・§8.1 を読み、partial 1,574・none 1,417の全2,991行を対象とした。原文はKerodon公式の小節ページから項目Tagごとに取得。現在の本体とロックした隣接Mathlibの宣言をソースから索引化し、KL-W1・B3・B3′・OE-W1後の場所も検索範囲に含む。原文・型・検索結果の大きい証拠はgit外 `~/serre-evidence/cited/kerodon-b6/`、目録だけをコミットする。

### 第1章

69行（旧partial40・none29）を全件照合した。旧partialのうち21をnone、18をpartialとして種類を付記、1をownへ更新。旧none29は全て再検索後もnone。保持したpartialの種類はcomponent12・direction3・special2・stronger-hyp1。

代表例：1.1.4.8の候補は「X全体を非退化単体で表示する余極限」で、原文の「次数≤kに制限した全単体圏からの骨格表示」という別の射ではないためnone。1.5.7.1・1.5.7.3も、sequentialSpineの包含をグラフの指定射と同定する橋が引用型になく、別の射の類似だけをspecialとしない。1.1.4.13は境界からの面制限の単射性がhom_extから直接得られる結論成分としてpartialを維持した。

1.5.5.6は現在の RelativeInternalHomTrivialFibration.lean:24 に、任意の単射iとtrivial Kan fibration pの相対内部Hom比較πがtrivial Kan fibrationとなる型があり、原文の同じ比較射を扱うのでownへ更新した。模型圏の追加仮定はない。

第1章だけ末尾にpartial_kind列を追加し、元のown・both・mathlib111行は全既存フィールドを保って新列を空にした。verdict・axioms・check、区切り・改行と対象外行の引用符も維持。新たなkernel確認という意味を付けていない。全対象行の一覧は `review/check/b6-ch1.md`。この章のコミット後も停止せず第2章へ進む。

### 第2章

154行（旧partial80・none74）を再照合。partial48行をnoneへ、32行は種類を付して維持。旧noneのうち2.1.1.5を、単位つきモノイダル圏から非単位部分を直接忘却できるstronger-hypとしてpartialに変更し、73行は再検索後もnone。結果はpartial33・none121、種類はcomponent18・stronger-hyp8・special6・direction1。

原文の逆包含のPathと現行包含順模型、原文のdg符号とHA符号、商型正規化と核型正規化を比較する宣言がない候補は、類似の構成だけでpartialにしなかった。2.4.5.11はKan性から両端点評価が自明Kan fibrationとなる方向、2.5.6.21は核型正規化の包含のホモロジー同型という結論成分を直接持つ。既存own・both・mathlib59行は全既存フィールドを保存。

第1〜2章の計223対象行を完了（済み2／全体10章）。章別全件表はreview/check/b6-ch1.md・b6-ch2.md、ソースの型と公式原文の比較・検索記録はgit外。Lean・ビルド・kernel実行・鍵は使用していない。そのまま第3章へ進む。

### 第3章

274行（旧partial121・none153）を再照合。旧partial81行をnone、40行は種類を付して維持。旧noneから3.6.6.1・3.6.6.8を被覆写像に限定した区間ホモトピー持ち上げのstronger-hypへ変更し、151行は再検索後もnone。結果はpartial42・none232、種類はstronger-hyp15・component14・special10・direction3。既存own・both・mathlib65行は変更なし。

原文が第0面を指定するincidenceと最後の面によるBoundaryLift、球面からの写像の商と独自の境界定値単体の商、全区間写像によるホモトピー引き戻しとKan置換を使う模型は、比較する宣言がないものをnoneに整理した。単に写像空間や極限のKan性を持つ候補も、原文の連結度・切断次数の結論の一部とは数えない。exInfinityの有限極限保存、同じ単位の単射性、有限部分集合圏の余極限の弱可縮性など直接の成分・特殊形はpartialを維持した。

全対象行の判定はreview/check/b6-ch3.md。公式原文・型・none153行の再検索と新規候補の抜粋はgit外に保存し目録を更新。Lean・ビルド・kernel実行・鍵はなし。

### 第4章

454行（旧partial267・none187）を再照合。旧partialは127行を種類つきで維持、134行をnone、6行をownへ更新。旧noneのうち3行をpartialへ変更、184行はnoneを維持。結果はpartial130・none318・own6、partialの種類はspecial53・component33・stronger-hyp30・direction14。既存own・both・mathlib134行は全既存フィールドを保存した。

4.3.7.13は現本体のslice側のtrivial Kan fibrationも合わせ、両側の結論がそろう。4.4.1.4・4.4.3.6・4.4.5.4・4.4.5.7は同じequivalence lifting・coreの射への既存判定を直接適用できるためown。4.8.1.11は一般のfullSubcomplexOnVerticesに頂点の本質的像の述語を代入して定義全体を直接与えられる。専用の名称の有無だけでpartialに制限しなかった。

pinched→interval写像空間には現本体に自然な圏同値と作用の可換式があり、同じ射の同値性の比較には適用できる。一方、この同値だけで厳密pullbackやfibration性を移すものは数えない。4.3.6.12はArchiveのslice宣言を根拠から外し、現本体のcoslice側のcomponentのみとした。κによる数値的smallnessと宇宙版Smallの間の比較が型にない候補もnoneにした。

旧noneからは4.5.7.12・4.5.7.14をKanな塔の重み付きHom・重みのanodyne制限に限ったspecial、4.8.5.15をn=0の合成本質的全射性に限ったspecialへ変更した。全対象の判定はreview/check/b6-ch4.md。第1〜4章計951行を完了（済み4／全体10章）。原文・型・検索はgit外、目録だけ更新。Lean・ビルド・kernel実行・鍵は使わず、停止せず第5章へ進む。

### 第5章

297行（旧partial179・none118）を再照合。旧partialは83行を種類つきで維持、93行をnone、3行をownへ更新。旧noneは5.3.2.18のKan値図式のhomotopy colimit比較と5.4.2.1のinterior fibrationの定義中のinner horn持ち上げ条件をpartialへ変更、116行はnone。結果はpartial85・none209・own3、種類はcomponent39・special21・stronger-hyp20・direction5。既存own・both・mathlib48行は全既存フィールドを保存した。

5.3.1.7の評価のtrivial Kan fibration性、5.3.5.8のuniversal scaffoldの圏同値性は現在の型が原文全体に一致する。旧理由で要求していた追加の自然性・weighted nerveへの復元はこの項目の結論にはなく、ownとした。5.5.3.1もQCatの対象・coreのHom・豊穣合成とCatInfinityの定義がそろい、ownとした。5.1.4.13は現本体のcartesian三角形の合成と取消しを使い、底が準圏の場合のstronger-hypを確認した。

通常圏のcartesian射とnerveの辺の比較、hQCat値の輸送とSet値の輸送、豊穣sliceの全coherent nerveと単一fiber、QC_Objによる積分とpointed-spaceによる積分、QC値の全表現のTWと空間値left transport witness空間は、それぞれ同じ対象・射である比較がない候補をnoneとした。特にUがleft fibrationでも任意QC値表現が同じ空間値データになるわけではなく、後者のKan性や可縮性をそのまま原文TWの特殊形とは数えない。準圏性だけを返す型も、薄い2面と指定外hornを含む∞-bicategory性の全体の代用にしなかった。

全対象行の判定はreview/check/b6-ch5.md。原文・型・再検索・追加候補のソースはgit外に保存し、目録だけ更新した。Lean・ビルド・kernel実行・鍵はなし。次は第6章。

### 第6章

114行（旧partial62・none52）を再照合。旧partialは43行を種類つきで維持、14行をnone、4行をmathlib、1行をownへ更新。旧noneは6.2.1.21をD=Δ⁰・n=−2の右随伴による終対象保存のspecialに変更、51行はnone。結果はpartial44・none65・mathlib4・own1、種類はcomponent22・direction8・special8・stronger-hyp6。既存own・both・mathlib31行は全既存フィールドを保存した。

専用の述語名や合成補題の不足だけはpartialの理由にしなかった。6.1.2.14はAdjunctionのcounitを指定した存在量化、6.1.6.6・6.1.6.8はExactPairingの評価／余評価を指定した存在量化で定義全体を表せるためmathlib。6.1.5.6もAdjunction.compに存在する随伴の証人を代入すれば両側の合成の存在が直接得られるのでmathlib。6.3.3.1はIsLocalizationを辺集合で存在量化した原文の定義全体でown。

同じ原文の一方向・結論成分を返さない候補はnoneとした。例は、6.2.2.16のreflectorによる反転判定とcoslice制限の五条件、6.3.2.9のwalking equivalenceを貼る模型と指定Qを貼る模型、6.3.6.4〜6.3.6.5の初頂点射と最終頂点を経由する指定射。模型圏由来の6.2.5.4・6.2.5.7は指定cf collageと輸送の型も読み、§6に従いModelCategory・SM7等の入力と具体例のinstanceなしを明記した条件つきpartialのまま。

第1〜6章の計1,362対象行を完了（済み6／全体10章）。全件表はreview/check/b6-ch6.md、原文・全候補型・再検索と追加ソースはgit外に保存し目録だけ更新。Lean・ビルド・kernel実行・鍵はなし。そのまま第7章へ進む。

### 第7章

473行（旧partial299・none174）を原文と型で再照合。旧partialは138行を種類つきで維持、151行をnone、10行をownへ更新。旧noneは7行をpartialへ変更、167行はnone。結果はpartial145・none318・own10、種類はcomponent58・stronger-hyp44・special36・direction7。既存own・both・mathlib46行の全既存フィールドは保存した。

同じ全錐・全余錐のFunctorIsoによる移送（7.1.3.19）、点ごとの余極限の存在と指定余錐の判定（7.1.8.3）、左右anodyneの取消し（7.2.1.7）、opと積の厳密な比較によるleft cofinal性（7.2.1.19・7.2.1.20）は現本体の型を合成して原文全体を得るのでown。7.3.5.8は既存の右Kan存在判定も合わせて両側を満たす。7.3.8.3・7.3.8.20は同じ包含への左Kan条件から余極限の制限・存在のiffを得る。7.5.2.1はweighted nerve上のcocartesianSectionsという実際の全部分準圏の構成、7.5.4.4はBK比較の自然性と二つから三つの性質で同じ三条件の判定を与える。

原文が指定する写像空間同値をh FunのHom集合の全単射だけで代用するもの、全関手準圏の結果を比較なしにファイブレーションのsection準圏へ移すもの、通常圏のMono・IsPullback・van Kampen条件を∞圏の対応する述語と比較する型がないものはnone。全局所余錐から関手制限の境界充填を得る部品だけも、全関手が点ごとにleftKanExtendedFromであるという結論と同一視しなかった。相対余極限の絶対化はU=idでなく終対象への射であると訂正した。7.5.4.12は新しいgeneral_reflectionの型により、古いlim比較同値などの余分な仮定が不要なKan値のspecialへ更新した。

旧noneからはrepleteを加えた反射部分圏の終対象（7.1.4.34）、monoかつstrict pushoutでのleft cofinal性（7.2.1.16）、指定comma相対余極限も入力する左Kan延長（7.3.5.10・7.3.5.11）、保存関手の頂点条件（7.6.6.5）、Spaceのfiltered余極限と有限極限の交換という条件(3)の特殊形（7.7.7.1・7.7.7.2）をpartialとした。

計1,835対象行を完了（済み7／全体10章）。全件表はreview/check/b6-ch7.md。公式原文・全候補型・none全174行を含む再検索・追加ソースと決定過程はgit外の章別証拠、目録のみ更新。Lean・ビルド・kernel実行・鍵はなし。第8章へ続ける。

### 第8章

447行（旧partial173・none274）を再照合。旧partialは71行を種類つきで維持、92行をnone、7行をown、3行をmathlibへ更新。旧noneは8.5.6.1・8.7.5.6・8.7.5.14を仮定を限ったpartialへ変更、271行はnone。結果はpartial74・none363・own7・mathlib3。種類はcomponent34・special24・stronger-hyp12・direction4。既存own・both・mathlib36行の全既存フィールドは保存した。

edgewiseの両射影と双対同型（8.1.1.7）、couplingとprofunctorの元の型（8.2.0.1・8.3.2.1）、定値一点の関手（8.3.4.11）、指定標準Kan余錐と恒等単位による密度（8.4.1.5・8.4.1.15）、一般余錐のretract閉性からの余極限保存のretract閉性（8.5.1.14）は専用名の不足だけを欠落にせずownとした。通常圏のKaroubiの対象と分裂等化子・余等化子を使う8.5.2.1・8.5.2.4・8.5.2.5はmathlib。標準Yonedaの恒等関手の左Kan性8.4.2.1は現本体の同じ型によりsmallな場合のspecialとした。

数値κで切った空間圏と宇宙パラメータ、整数spineとN(Idem)、指定された相対指数と固定始域の関手空間、QC全体上の反転・随伴形成と固定二対象間の関手は、同じ対象・射への比較がなければ混同しなかった。Moritaの一般形と冪等完備化・inner fibrationを追加した場合の差、flat性とcocartesian fibrationを追加した場合の差をreasonに記した。

第1〜8章の計2,282対象行を完了（済み8／全体10章）。全件表はreview/check/b6-ch8.md。原文・型・旧none274行の再検索・追加候補と判断過程はgit外へ保存し、目録だけ更新。Lean・ビルド・kernel実行・鍵はなし。停止せず第9章へ進む。
