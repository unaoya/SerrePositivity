# 現在地

- 段：**AR-W1 進行中。FilteredExchange の群分け・主要宣言一覧を先にコミットする途中点（停止しない）**。
- 作業場所：`/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-cited`。枝：`research/cited-coverage`。pwd 一致を確認し、指定の `git merge main` を実施した。
- 基準HEAD：`7c2528f6594b63074e7955f2f0c57db15ace4e2e`（main 取り込み後）。今回の途中コミット件名は `docs: inventory archived mathematical topic groups`。
- 次：宣言の型・文献番号・現本体との主張の一致・目標の必要性・import の状態を調べ、全群の推奨と Kerodon 行の訂正案を完成させる。紙だけで進める。

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
