# CLMST の全項目対応表（CC-W1、2026-11-17）

指示書：`formalization-plans/stage-ii/cited/clmst-coverage.md`。作業木 `SerrePositivity-cited`、枝 `research/cited-coverage`、照合対象 HEAD `9bfb015051ee96dd2b3d24c6e63801aa61de4a07`。原典は arXiv:2209.04046v4、版・指紋・全見出しは `toc.md`。

**紙とソースの静的照合のみ。Lean の変更・実行・ビルド・kernel 検査はしていない。** 既存の paper-coverage・bs-coverage 等も変更していない。

## 集計

全 **147項目**：数値番号つき環境123件、導入の Theorem A–G 7件、式17件（数値番号16件と記号ラベル `(*)` 1件）。親項目の (a)/(b) 等は重複する番号として増やさない。

| 状態 | 件数 |
|---|---:|
| own | 4 |
| mathlib | 0 |
| both | 0 |
| partial | 20 |
| interface | 6 |
| none | 117 |

辺は **572件**（internal **344**、external **228**、根拠位置ごと）。同じ文献項目を複数の位置で引くと複数辺になる。

## ファイル

- `toc.md`：版、PDF 指紋、全節見出し、番号なしの独立見出し、外部文献の略号と版の扱い。
- `items.csv`：paper-coverage と同じ12列。status・declarations・reason は空欄で、同じ number の review を正本として読む。confidence は原典採取の確度。lean_citations・plan_citations は未集計の空欄であり、0を意味しない。
- `review/ch1.csv`–`ch8.csv`：節ごとの状態・宣言の現行位置・仮定と結論の差。§1 は A–G と `(*)`。式も掲載節の review に入れる。
- `edges.csv`：`number,depends_on,evidence_location,kind`。内部項目と外部文献の、主張・証明・式の導出段落での引用を記録。外部文献の定理番号を CLMST の内部番号と誤認しない。本文中で同定できる設定 Notation 4.0.1 への明示参照も含む。
- `review/check/source-items.csv`：原典の全147件の種類・PDFページ・layout の開始／終了行。入れ子の Claim では親の証明範囲と重なる。式の行範囲は表示の位置を探すための窓で、数式全文の転記ではない。
- `review/check/none-search.csv`：none 全117件の検索語・探索範囲・ヒット行数・候補位置の例・採用しない理由。候補位置は検索結果の最初の5行であり、対応宣言の列挙ではない。
- `review/check/proof-ranges.csv`：後置・分割された証明の親項目への対応。
- `review/check/background-references.csv`：番号つき項目の外にある背景・準備段落の外部引用。直前の定理の証明依存として扱わない。
- `evidence/cited/clmst/manifest.json`：git 外の採取・照合記録の目録。保存先は `~/serre-evidence/cited/clmst/`。PDF本体は複写していない。

## 状態と差の読み方

`own` は原典の範囲に対応する定義・証明を本体ソースで確認したもの、`mathlib` は項目全体が Mathlib に対応するもの、`both` は両方で項目全体を確認したもの。`partial` は部分結論または特殊な場合だけに対応するもので、`partial_kind=part/special` と reason に残る差を記す。`interface` は該当範囲の宣言はあるが未証明入力への依存があるもの。`none` はこの探索で同じ主張の対応宣言を確認できなかったもの。

partial に Mathlib の宣言があっても、項目全体を mathlib と数えない。たとえば Definition 5.3.3 では群完備化側のみを採用した。関連する一般補助が存在するだけで、BCM 正則性、signature、非分裂イデアルの構成まで済んだとはしない。

原典で予想・問いであるものも none の対象とした。none は「偽」や「形式化不可能」、数学的な不存在の証明を意味しない。原典に従った未証明の入力型を用意したことと、関連する一般理論があることも区別する。

## 主な確認結果

- 本論文が引く項目だけに限定しなかった。§3 の F-signature、§5 の BCM・有理 signature、§6 の変換則、§7 の応用、§8 の予想と因子対の定義まで含む。
- Definition 2.2.1 の三段階の正規化長さと Proposition 2.2.3 の一致は own。Proposition 2.2.6 は (a) の加法性と単射系の有向和の公式を確認したが、(b|ii) の一般の全射 filtered colimit まで確認できないので、項目全体は partial。本論文が引用する **2.2.6(a)** と全項目の状態の違いは、部分番号の違いである。
- Proposition 2.4.9 の採用宣言は単項 J=(a) に対する (a) の Tor 零化。任意の有限生成 J、(b) の忠実性、最後の almost 純性まで含むと解釈しない。Theorem 4.0.3 の全加群版の宣言も、二つの明示入力を受け取り、(b) の忠実性全体を供給しないため partial。
- Corollary 4.0.4 は局所コホモロジーと全有限段の任意パラメータ Koszul の両結論、Proposition 4.0.10 は実際の mod p^N almost 局所化圏の同型、Proposition 4.0.14 は任意有限段の p^(nd) 正規化と階数の系まで確認した。原典より狭い単一のパラメータ例だけをこれらの全体対応とはしていない。
- これらと Proposition 2.4.7、Notation 4.0.1、Claim 4.0.15 の標準 perfectoid 化には E3 の未証明入力が残るので interface。宣言本文に直接 sorry がないことと、未証明入力に依存しないことは異なる。`Perfectoidization` → `exists_perfectoidization_of_finite` → `Inputs.exists_perfectoidization_of_integral` → `Inputs.exists_perfectoidizationInterfaceE3` のソース上の経路を確認した。
- Proposition 4.0.16 は J=m_A A_infty の場合、Corollary 4.0.18 はパラメータ生成イデアルでの等号の部分だけを partial とした。任意の準素イデアルに自動で一般化しない。
- Question 4.0.19 は `e(I)/d! ≤ e_perfd(I)` という一般下界の問い。Remark 4.1.6 は R_perfd を絶対整閉包内の像で置き換えると値が変わる反例。各項目の性格を保ち、正値性や選択独立性の定理に読み替えない。

## 原典採取と引用辺の点検

テキスト採取に加え、PDF の named destinations と独立に照合し、数値番号つき環境123件と表示式17件の集合・ページがすべて一致した。Theorem A–G は本文で確認した。Definition 8.5 の内部リンク名は `conjdef.8.5` だが、印刷された見出しの Definition を採用した。

PDF 内部の `equation.1.0.0.1` は印刷上の `(*)`、`equation.6.2.2.1` は印刷上の `(6.0.1.1)` である。表には印刷ラベルを使う。外部文献 [ČS24] の `(2.1.3.1)` を CLMST の式として採取していない。p.33 の入れ子 Claim と5つの表示式、p.68 の変換則の表示を描画して目視した。

Theorem 6.0.1 の後置証明（§6.2）、Remark 7.0.3 の後に続く Theorem 7.0.2 の証明、Proposition 4.1.3・4.1.4・Corollary 4.1.5 に分割された Theorem 4.1.1 の証明を親定理へ対応づけた。Claim の後に親の証明が再開する箇所も、Claim に全文を誤配属していない。改行で Corol-/lary 等が分断された引用は原典で補った。

辺は引用・導出の記録で、無条件に非循環な証明順を意味しない。式と親の証明の相互参照や、定理の証明分割の辺もある。背景比較の外部文献は evidence_location の引用本文を見て解釈する。

## ソース検査と限界

本体の非 Archive 33,542ファイル、Archive 1,871ファイル、Mathlib 8,602ファイルを読み取り検索した。Mathlib は隣の本体の `.lake/packages/mathlib/Mathlib` を使用し、revision `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6` がこの作業木の lake-manifest と一致することを確認した。この作業木に `.lake` を作っていない。

36個の採用宣言の位置・型・本文とソース指紋を保存し、本文中に直接の sorry/admit/sorryAx がないことを静的に点検した。E3 への依存は上記の明示的なソース経路で別に判断した。**全宣言の kernel 依存閉包を証明したわけではない**。暗黙の型クラス推論や構文展開を含む `#print axioms` の結果として読まない。

none の検索は番号だけの衝突を避け、内容語による広い候補抽出を使った。ヒット数はコメントを含むソース行数であり、対応定理の数や全候補の逐一型検査数ではない。F-signature の定義がなくても他分野の signature にヒットする等の候補は採用しない。各項目の採用しない理由を review と検索表に残した。

既存表との番号・版の注意点は、2.2.6(a) と全項目の範囲の違い、および CLMST [BS22] の刊行版番号と BS19 著者版番号の違い。ソースの「証明済み」という説明も、直接 sorry がないという局所的事実から E3 への依存を除いたという意味には読み替えない。既存表は修正していない。

## 停止点

147件の一意なキー、全147件の review、none 全117件の検索、内部辺の両端、全外部辺の原典位置、採用宣言の現行位置と指紋、PDF の独立番号照合を検査した。対応表・本報告・証拠目録の紙資料だけをコミットし、CC-W1 で停止する。CC-W2 とブループリント生成へは進まない。
