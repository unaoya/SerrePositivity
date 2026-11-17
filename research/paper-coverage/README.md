# 本論文の全体対応表（⑤d、2026-11-17）

ユーザー承認11-17、指示書 `formalization-plans/stage-ii/p0/paper-blueprint.md` に従い、最新main `c499fc236` から枝 `codex/paper-coverage` を切って作成した。Leanの追加・変更・実行・ビルドはしていない。

## 結果

§1〜§5の見出し26件、番号つき環境27件、番号つき式47件、図1件を採取した。`items.csv` は **75行**（図を除くと74行）。主張・証明とその準備段落の引用辺を `edges.csv` に置き、状態の正本は `review/ch1.csv`〜`ch5.csv` とする。

| 状態 | 項目数 |
|---|---|
| own | 37 |
| mathlib | 0 |
| both | 0 |
| partial | 8 |
| interface | 13 |
| none | 17 |

辺は **262件**（internal 184、external 78、根拠位置ごと）。

## ファイルと状態の読み方

- `toc.md`：採用版・PDF指紋・全見出し・外部引用の略号／版。
- `items.csv`：HA・DAG XIIIと同じ12列の項目目録。二重管理を避けるためstatus・declarations・reason欄は空にし、同じnumberのreviewから読む。`lean_citations`はソースの文献属性にある明示的なPaper番号の件数、plan_citationsは今回は未集計の空欄。
- `review/ch<N>.csv`：各項目の状態・現行の対応宣言・仮定と結論の差・sorryの確認。
- `edges.csv`：指定の4列。項目の主張・証明の明示引用、式の定義段落と同定した証明箇所、Theorem3.1の§3.1準備と§3.3の後置証明を含む。位置はPDFページとlayout行で追跡できる。文献番号リスト、範囲引用、`that paper`によるCLMSTの引用も展開した。式ラベル・環境見出し・Proof of…の見出しそのものは辺に数えない。
- `review/check/source-items.csv`：全75項目の種類・ページ・原典位置。`declarations.csv`と`declarations.json`：対応宣言と旧表の補助宣言についての型・ソース指紋・本文のsorry・明示的な依存経路。
- `review/check/legacy-crosswalk.csv`：旧表の全行と新表への引継ぎ先。旧状態・理由の転記ではない。
- `review/check/none-search.csv`：none項目の検索語・探索範囲・型の候補・採用しない理由。検索の不一致は数学的な不存在の証明ではない。
- `review/check/intro-references.csv`：番号つき項目の範囲外にある導入・背景の引用。これを前後の定理の証明の引用と偽って割り当てない。

`own`は本体に原典の範囲に当たる証明を確認したもの、`partial`は確認した部分と残る差を理由に明記したもの、`interface`は未証明の入力やsorry依存が残るもの、`none`は同じ主張の対応宣言を確認できなかったもの。Mathlibの補題を使うだけでは論文の項目全体をmathlib/bothとは数えない。

式(3.9)・(4.1)のような**仮定の表示**のownは、その仮定を持つ型の対応であり、Cの存在を無条件に証明したという意味ではない。原典の大域設定を引数として受け取る補題と、その設定を実際に構成する定理を区別した。添字は原典のhomological iに対し、複体側のcochain次数q=-iで対応させる。

## 主な確認結果

- Theorem1.1の `main_statement` は原典と同じ一般の正則局所環・有限加群の主張を持つ。自身にsorryはないが、通常K0降下、漸近K0降下、混標数perfectoidizationのE3界面への明示的なsorry依存経路があるのでinterface。
- Theorem2.5は両標数で同じCと全パラメータの公式を返す宣言があるが、混標数の存在がE3界面に依存する。等標数のconductorや有限段の計算と分けて記録した。
- Theorem3.1の本体入力はH=Aに特殊化した局所K0版で、任意の連結非可換係数・有理Kスペクトルの同値(3.1)を構成したものではない。
- Proposition4.3では、現在の `paperRankHomology` と `completedRankHomology_isHomological` によりLengthSerreQuotientへのホモロジー関手まで確認した。非負性・有限support・K0のEuler準同型もあるので、旧表の「数値部分のみ」というpartialをownへ見直した。式(4.2)も一様支持liftを追加仮定せず、像の商内支持から得る係数公式を確認した。
- Lemma4.6と式(4.7)の連結係数による一般のMorita表示は確認できない。Theorem4.7は別の `supportedRankK0_descent` 入力に依存している。
- Corollary1.2のstrict transformとassociated gradedによる同値は、KSTのチャートや主定理の存在だけでは対応済みにしない。

## sorryの点検と限界

**101宣言**を宣言ごとに点検した。各宣言の本文からコメント・文字列を除いてsorry/admit/sorryAxを検出し、現在のsource hashと位置を記録した。うち直接sorryを持つものは3宣言、明示的な参照経路でsorryへ達したものは14宣言。ownとして採用した宣言には、その本文のsorryも今回の探索で見つかった明示的なsorry経路もない。

明示参照の追跡はnamespace・import閉包内の定数名から行った**静的なソース点検**であり、Leanの `#print axioms` を実行した結果ではない。型クラスの暗黙推論・構文展開まで含む完全なkernel依存集合を証明したものではない。`axioms`欄にもkernel検査を再実行していないことを明記した。旧表のkernel-evidenceは過去revisionのものなので、今回の検査済み結果として流用していない。

非Archive本体で現在本文にsorryを持つ宣言は次の4件。主定理から今回の明示参照追跡で達したのは先頭の3件であり、Kan–Quillen入力へは未到達だった。

| 宣言 | 場所 | 主定理からの明示参照経路 |
|---|---|---|
| SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3 | SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean:54 | あり |
| SerrePositivity.Section4.supportedRankK0_descent | SerrePositivity/Paper/Section4/SupportedDescent.lean:41 | あり |
| SerrePositivity.theorem_3_1_K0 | SerrePositivity/Inputs/Descent.lean:50 | あり |
| SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillen_model_exists | SerrePositivity/InfinityCategories/Project/ModelCategoryComparison/Inputs/KanQuillen.lean:36 | 今回未検出 |

- `SerrePositivity.main_statement` → `SerrePositivity.Section5.positivity_of_residueCharP` → `SerrePositivity.Section5.positivity_of_complete_residueCharP` → `SerrePositivity.Section5.positivity_of_complete_algClosed` → `SerrePositivity.Section5.chi_prime_pos_of_complete_algClosed` → `SerrePositivity.Section5.core_of_complete_algClosed` → `SerrePositivity.Section5.core_of_normalization_bases` → `SerrePositivity.Section2.theorem_2_5` → `SerrePositivity.Section2.lengthAlgebra_mixedCharacteristic` → `SerrePositivity.Section2.MixedPerfectoid` → `SerrePositivity.Perfectoidization` → `SerrePositivity.BhattScholze.exists_perfectoidization_of_finite` → `SerrePositivity.BhattScholze.Inputs.exists_perfectoidization_of_integral` → `SerrePositivity.BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`
- `SerrePositivity.main_statement` → `SerrePositivity.Section5.positivity_of_residueCharP` → `SerrePositivity.Section5.positivity_of_complete_residueCharP` → `SerrePositivity.Section5.positivity_of_complete_algClosed` → `SerrePositivity.Section5.chi_prime_pos_of_complete_algClosed` → `SerrePositivity.Section5.core_of_complete_algClosed` → `SerrePositivity.Section5.core_of_normalization_bases` → `SerrePositivity.Section5.core_of_lengthAlgebras_with_parameter_choice` → `SerrePositivity.Section5.core_of_lengthAlgebras` → `SerrePositivity.Section5.twistedEuler_pos_of_lengthAlgebras` → `SerrePositivity.Section5.lambdaChi_pos_of_parameter_lengthAlgebras` → `SerrePositivity.Section5.lambdaChi_pos_of_parameter_tower` → `SerrePositivity.Section5.exists_secondComparison_pos_of_regular` → `SerrePositivity.Section4.supportedRankK0_descent`
- `SerrePositivity.main_statement` → `SerrePositivity.Section5.positivity_of_residueCharP` → `SerrePositivity.Section5.positivity_of_complete_residueCharP` → `SerrePositivity.Section5.positivity_of_complete_algClosed` → `SerrePositivity.Section5.chi_prime_pos_of_complete_algClosed` → `SerrePositivity.Section5.core_of_complete_algClosed` → `SerrePositivity.Section5.core_of_normalization_bases` → `SerrePositivity.Section5.core_of_lengthAlgebras_with_parameter_choice` → `SerrePositivity.Section5.core_of_lengthAlgebras` → `SerrePositivity.core_of_twistedEuler_pos` → `SerrePositivity.firstComparison` → `SerrePositivity.normComparison_of_lengthAlgebra` → `SerrePositivity.lemma_3_5` → `SerrePositivity.lemma_3_5c` → `SerrePositivity.theorem_3_1_K0`

## 旧§3・§4表の引継ぎ

指示書は63項目とするが、基準mainの旧 `research/k-coverage/maps/paper/items.csv` は **62行**だった。うち原典の番号つき環境・式34行は新表の同じキーへ照合し直した。節見出し11行と、番号なしの定義・証明部分17行の計28行は、tocまたは原典の親項目のreviewへ対応させた。3.5a–cなどの便宜的な分割を新しい原典番号にしていない。

補助宣言についても現在の型・sorryを再点検し、crosswalkに現行位置を載せた。たとえば幾何・中心台の補助が証明済みでも、スペクトル値Lの降下全体をpartial/ownへ自動的に引き上げない。旧表や他文献の対応表には書き込んでいない。

## 引用辺の読み方

引用の辺であり、無条件に循環のない証明順を表すわけではない。たとえばLemma5.1の主張中のTheorem1.1は「証明すべき命題」の参照であり、証明済みのTheorem1.1を仮定するという意味ではない。外部引用に番号が指定されていない場合は略号だけを残す。参考文献[17]は本文で文献全体を引き、ReferencesでTheorem1.1を明示するため、その同定位置も別辺として記録した。

## 検収と停止

75個の一意なキー、26見出し、式47件の連番、全75件のreview、対応宣言の現在の位置・本文指紋、各状態とsorryの整合、辺の両端と略号・根拠位置、旧62行すべての引継ぎ先を検査した。PDFのp.10・18・21・29を描画して、(3.1)/(3.2)のスペクトル対K0、(4.2)/(4.3)、式(4.6)対Lemma4.6、最終(5.17)/(5.18)の表示番号を目視確認した。

この新しい対応表の紙資料だけをコミットして停止する。既存の対応表・論文PDF・Leanコードの変更と、Lean実行・ビルドは行っていない。

## 引用した結果の表（CC-W2、2026-11-17）

`external.csv` は `edges.csv` の external **78辺の先の全47種類**を、`source,number,statement_ja,status,declarations,reason` の6列で収録する。`source` と空白区切りの `number` を再結合すると辺先に完全一致する。番号なしの文献引用は number を空欄に保ち、存在しない定理番号を追加しない。文献全体への引用の statement_ja は、本論文が使用する結果の要約であり、文献全体の形式化完了を意味しない。

状態・宣言の二重管理を避けるため、**25行は status・declarations を空欄**にして、reason に正本のファイルと行キーを記す。空欄は none ではない。

- CLMST 7行：`research/clmst-coverage/review/ch<N>.csv` の同じ番号から状態と宣言を読む。2.2.6(a) は親キー 2.2.6 の (a) の確認範囲を読む。親項目全体の colimit の不足を (a) の加法性の不足と混同しない。
- BS19 1行：`research/bs-coverage/items.csv` の number=8.5。正本の状態語・note も含めて読む。本論文の arXiv v4 と正本の著者版の範囲・版の対応を確認し、番号だけで版を同一視しない。古い宣言パスを external.csv に転記しない。
- K の文献17行：LT は `research/k-coverage/maps/land-tamme/items.csv`、BGT は `.../bgt/items.csv`、TT と Drinfeld は `.../others.csv`。TT のまとめ行なども実在する正本の行キーで参照する。既存表の状態をこの表で上書き・再判定しない。

残る **単発文献22行**は、使用主張と本体・Mathlib の現行宣言の型を静的に照合した。内訳は **own 4、mathlib 2、partial 10、none 6**（both/interface は0）。特殊な環・加群・複体だけの対応は partial とし、一般形との差を reason に書いた。none 全6行の検索語・範囲・ヒットと採用しない理由は git 外の `none-search.json` にある。

主な注意点：

- Ma17 の辺先「2.2」は、本論文 p.5 の Lemma 2.2 と p.8 の Section 2.2 の両方で使われる。同じ辺先キーの一行で両者を明記し、補題全体の Lech 型帰着を剰余体拡大だけで own にしない。
- BGT の辺先「9.3」は §9.3 の引用であり、既存表の式 `(9.3)` とは異なる。reason は `number=§9.3` と `§9.3 localization` を指定する。LT「Appendix B」は `number=§B`。Drinfeld 3.1 は `number=§3.1` の構成を指定する。
- KuranoShimomoto の番号なしの辺と 1.1 の辺はそれぞれ一行を保つ。原典の非整域も含む Cohen–Gabber 定理に対し、本体の整域版は partial。
- Ma17 2.4／Roberts89 の一般有限自由複体の Frobenius ホモロジー消滅に対し、本体の証明済み入口は完全剰余体のパラメータ Koszul 複体の特殊例。一般消滅を hRoberts として受け取る補助を、一般定理の証明とはしない。
- Stacks 03QH は有限代数の積分解等と Hensel 性の同値。完備 Noether 局所環上の有限整域の局所性という本体の使用時の系に対応範囲を狭めたため partial。0BRI・0BRJ は Mathlib に一般の有限群作用の推移性・剰余分数体の正規性・分解群写像の全射性を確認した。
- Stacks 0815 は任意の qcqs 基底と有限型準連接加群の平坦化。本体の Noether 基底、有限加群や構造層の入口だけから一般形全体を own にしない。
- Balmer–Schlichting 1.10・1.12 は、それぞれ実際の Retract による完全三角形の定義と Karoubi 完備化の三角構造を照合した。Skalit の4項目と Jannsen の一般正則ブローアップの主張、Goodwillie の相対比較は同じ主張の宣言を確認できず none。

主張の確認には、本論文の各引用箇所に加え、[Skalit v2](https://arxiv.org/pdf/1409.3616v2)、[Ma v3](https://arxiv.org/pdf/1609.00095v3)、[Kurano–Shimomoto v2](https://arxiv.org/pdf/1510.03573v2)、[Faltings Appendix 2](https://numdam.org/item/AST_2002__279__185_0.pdf)、[Balmer–Schlichting](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/balmschl.pdf)、[Goodwillie](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/goodwillie-cyclic.pdf)、[Jannsen の付録](https://annals.math.princeton.edu/wp-content/uploads/annals-v172-n3-p03-p.pdf)、[Stacks の各 Tag](https://stacks.math.columbia.edu/tag/0815) を読み取り参照した。原典URLと確認位置は各行の reason に記す。

Roberts89 は原著章の本文を今回採取できず、Ma17 Theorem 2.4 の再掲で主張を確認した。Roberts85 は AMS PDF が403、Gillet–Soulé は出版社の購読画面まで、Monsky は原著の表紙・導入まで、Serre は書誌の確認にとどまる。これらは本論文の使用主張（Roberts89／Monsky は Ma17 の再掲も）と現行ソースを照合した判定であり、未取得の原著全体を精読したという記録ではない。

採用宣言17個の現行位置・型・周辺の変数条件・本文・指紋を保存した。本文の直接 sorry は検出していないが、全依存の kernel 検査や Lean 実行を行った結果ではない。検索は本体・Archive と、lake-manifest と revision が一致する隣の Mathlib ソースを読み取り対象にした。Archive の宣言は実装の正本として採用していない。

証拠は `~/serre-evidence/cited/clmst/cc-w2/`、目録は `evidence/cited/clmst/cc-w2/manifest.json`。CC-W1 の証拠・目録は変更しない。既存の items・edges・review と BS/K/CLMST の正本も変更していない。生成器のノード追加は調整役の次の作業であり、この段では紙資料のコミットで停止する。
