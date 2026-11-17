# BS（Prisms）の項目ごとの対応表

BT-W1（2026-11-17）。対象は Bhatt–Scholze, *Prisms and prismatic cohomology* の著者版の全番号つき **211項目**、§1–§18。原典は `../SerrePositivity/paper/refs/BS-prisms-author.pdf`（SHA-256 `4cb49a42c80fc734fb7585da273538e09632431ba06709ae05a11ded6673c27a`）。本論文が引用する項目だけには限らない。

## 正本と書式

**状態・対応宣言・判定理由の正本は `review/ch<N>.csv`。** HA・HTT と同じ7列 `number,status,declarations,reason,axioms,check,partial_kind` で、原典の節ごとに18ファイルを置く。

- `items.csv` は目録。番号・種類・題・日本語題・goal・design を保存した。旧 `status,declarations,note,confidence` は空にし、二重管理しない。goal は以前の目標への必要性の記録で、今回再判定していない。
- `own` は同じ対象・射の主張を本体の宣言の型から得るもの。`partial` は直接得られる限定部分があり、`special,direction,stronger-hyp,component` の差を reason に明記する。証明の部品・類似の定理・比較未供給の別模型は `none`。
- `interface` は **E3 の存在の sorry に依存する界面・公開定理**。原文の全範囲が実装済みという意味ではない。離散入力、D(R)への忘却、Type u の標的等の差を理由に書く。単に参考文献として名前が挙がるだけでは interface にしない。
- `declarations` は現在の `名前 @ パス:行`。正の根拠は現本体のみ。none 行では、採用しなかった本体の候補や drafts の所在を記録することがある。
- `axioms` は空。`check=found/not_found` は今回の静的な型・所在照合の記録であり、kernel 実行や `#print axioms` の結果ではない。Lean変更・ビルド・鍵の使用はない。

凍結中の `exposition/ja/bs/build_items.py` は **動かしていない**。勉強ノート・`map/data.json`・`doc1-check.csv` は以前の調査・表示の記録であり、今回の状態の正本ではない。生成器や表示の追随は別作業とする。

## 集計と旧状態からの遷移

**own 25、partial 46、interface 6、none 134、計211。** mathlib・both に判定した行はない。partial_kind は special 18、component 22、stronger-hyp 6、direction 0。

| 旧状態 | own | partial | interface | none | 計 |
| --- | ---: | ---: | ---: | ---: | ---: |
| proved | 24 | 6 | 0 | 3 | 33 |
| proved_special | 1 | 37 | 0 | 6 | 44 |
| parts_in_body | 0 | 2 | 1 | 12 | 15 |
| drafts | 0 | 0 | 0 | 13 | 13 |
| e3_input | 0 | 0 | 5 | 2 | 7 |
| design_only | 0 | 0 | 0 | 2 | 2 |
| none | 0 | 1 | 0 | 96 | 97 |

旧語の一括置換ではない。例：3.4 は正則列と Frobenius 完全平坦性の型も確認して own、10.3 は任意 J の perfectoid 核への一般定理の適用で own。旧 proved の2.36・2.38・2.39は、表示環・Tor と原文の指定 PD-envelope/derived pushout の比較が未同定なので none。旧 parts_in_body の4.19は同じ余単体項の底変換という直接の部分があり partial、6.1は追加の cochain 入力を明記して partial、10.11は E3 integral 欄を追って interface。

## BS 整理の段0へ渡す所見

1. **site RΓ と模型を区別する。** 4.9・4.10・5.5 の旧 proved_special は reducedModel 上の HT 写像・Bockstein・結晶基底の同型である。4.11・5.2・6.2–6.4も、site の RΓ と模型を結ぶ比較・Tot の交換が未供給なので none とした。主張述語 HodgeTateIsoStatement の定義だけも同型の証明として数えない。4.19の項ごとの底変換との境界を保つ必要がある。
2. **PD 表示環と universal PD-envelope の同定を明示する。** 2.36・2.38・2.39 の候補は通常環の表示・p正則性・Tor消滅・底変換を与えるが、指定された PD-envelope と SCR の derived pushout との橋を今回未同定。2.37の Tor 消滅、2.42の通常環の Koszul ホモロジーによる定義も、SCR の主張と同じとは扱わない。既存の cite 属性に own と書いてある場合も、この紙の判定とは一致しない。必要な比較の所在を段0で確認する対象にする。
3. **E3 の欄と参考文献を分ける。** 1.17・8.2・8.5・8.12・8.14・10.11は界面の存在に依存する。8.4は coconnective 欄が削除済み、8.11は arc 上 RΓ の欄がなく drafts のみなので none。8.2の φ-perfection の式や E∞ 構造を、D(R) の perfd 欄で構成したとはしない。
4. **並行する宣言を即座に削除しない。** 7.4の André 経路と root-envelope 経路は同じ普遍単位の全射性の別証明。5.5/4.11の hodgeTate_iso_polynomial_Zp と hodgeTate_of_deRham_cartier は同じ結晶基底の模型上の同型を渡す並行入口で、利用先を調べて統合を判断する。7.8の一般圏論と PrismOver の冪等分裂は、一般結果と適用例の関係。
5. **一般形と特化版を合わせて読む。** 10.3は単項 perfectoidIdeal_lemma103 だけでなく、perfectoidKernel_quotient_isIntegralPerfectoid と一般商の三定理を組むことで任意 J の主張を得る。10.2の拡大閉性・10.7の mod p^n 冪等性も一般商の根拠がある。一方で圏同値・almost有限射影・不分岐は別の未実装部分である。
6. **目録の既知の注記。** 16.9 の kind は旧目録で Theorem のままだが、原典は Example 16.9（q-PD対の例）。[GR, Theorem 16.9.17] の直後の証明と混同せず、今回の判定は Example に対する none。目録の6列は今回保存したので、種類の訂正は別作業。1.5が指す3.5も原典は Lemma として読む。

## 検証と証拠

`check_locations.py` を items の状態列を空にする **前に読取りのみ**で実行し、旧358エントリの ok168・移動127・行47・未解決16を得た。書換えオプションは使わず、現本体の宣言索引と実ファイルで review の名前・型・所在を照合した。このスクリプトは items を読む旧形式のため、空にした後の実行は review の検証にならない。今回の review 検証の手順と結果は git 外の証拠に置いた。

全211番号が一度ずつ現れること、18節、列・状態・partial_kindの整合、目録6列の保存、全対応先の現ファイル・行・正の根拠の完全修飾名、Archive/draftsの正の根拠からの排除を静的に確認した。非interfaceの正の根拠では、**native import閉包のソース**からコメント・文字列を除いた sorry/sorryAx を検出せず、interface6行だけが Inputs/PerfectoidizationInterface.lean の存在入力へ到達した。これは宣言ごとの完全なaxiom閉包のkernel検証ではない。

原文抽出、実際の型と文脈、検索、旧所在確認、遷移、静的検証の証拠は `~/serre-evidence/cited/bt-w1/`。コミットするのは `evidence/cited/bt-w1/manifest.json` の目録だけ。
