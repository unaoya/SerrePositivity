# DAGXIII の項目と Lean の宣言の対応表

2026-11-16、`research/dag13-ns-coverage`。基準 main `55f6cfbea`。
[指示書](../../formalization-plans/stage-ii/p0-section-map.md) §1、P⁰ の節単位の地図の資料。
全篇 290 項目を採取・照合。版と全見出しは [toc.md](toc.md)、集計は [review/summary.md](review/summary.md)。

## 形式と正本

[HA の形式](../ha-coverage/README.md)に合わせる。
`items.csv` の列は `number,kind,title,section,status,declarations,reason,confidence,lean_citations,plan_citations,kerodon,goal`。
HA と同様、items の status・declarations・reason は空で、**照合状態の正本は review/*.csv のみ**。
日本語の title は原典の主張の短い要約で、原典に付いている英語の題の転記ではない。

`review/*.csv` の列は `number,status,declarations,reason,axioms,check,partial_kind`。
status は own・mathlib・both・partial・none。
partial は原典の成分・特殊化・片方向・強い仮定での結論が宣言の型から直接得られる場合だけ。
証明材料・別の模型・別の演算で比較定理がないものは none とし、候補と不足を reason に残す。
`declarations` は `完全名 @ path:line`、Mathlib の path はそのパッケージの根から。

今回の依頼は紙の照合で、登録生成以外の Lean 実行は行わない。
`check=found/not_found` は原典と**ソースの型**を照合した結果。新しい #check・公理監査は未実行で、axioms は空欄。
source-types.json の signature はセクション変数を省略する宣言ソースの断片であり、kernel が展開した完全な型と称しない。
confidence は型を照合した行 high、検索による不存在判定 medium。none は数学的な証明不能を意味しない。

## 証拠と検査

- `review/check/source-items.csv`：全項目の kind・section・PDF 頁・pdftotext -layout の行。
- `review/check/claim-evidence.json`：項目ごとの原典の主張・照合順・直接引用件数・検索群・判定理由。
- `review/check/search-evidence.json`：project と Mathlib の概念・特殊例の検索、候補の宣言型断片とソース SHA。
- `review/check/source-types.json`：positive/partial の全宣言の完全名、現在のパス・行、型の断片・変数文脈・SHA。
- `review/check/edition.json`：版・PDF SHA・見出し・基準コミット。
- 検査：`python3 research/dag13-coverage/review/check/audit.py`（二文献を一緒に検査、Lean は起動しない）。
- 原典の再採取：`python3 research/dag13-coverage/review/check/extract_inventory.py --book dag13 --pdf /path/to/paper.pdf`。

P⁰ の節（DAG XIII §1.1・§2.1・§2.2、NS I.1・I.3・III.1・IV.1）を先に照合し、その後は本文順。
同じ内容でも文献をまたいで行を統合しない。kerodon 列は確認した同内容の HA・DAGXIII・NS の番号も許す。
証明の依存先はこの列へ混ぜない。列挙していない同内容の対応がないと主張するものではない。

## 引用と目標の印

citations.csv は SerrePositivity/**/*.lean、plan-citations.csv は formalization-plans/（archive を除く）と research/p0-lurie/ の直接の文献名付き言及を採取。
番号範囲は展開、同じ行の同じ番号は一件。文献名を省略した引用・改行をまたぐ引用・節だけの引用は項目に推測で配らない。
この限定した件数を items の二つの citations 列へ入れる。引用の存在は対応が証明済みという意味ではない。
BS;inf は依頼された P⁰ の先行照合の節全体、inf は Pro・モノイダルの一般基盤、その他は -。
全原項目の保持とは独立の計画上の印で、今後の節の閉包の正本を複製しない。

既存の HA・HTT・Kerodon の対応表・既存 P⁰ 地図は変更しない。差は [今回の報告](../../formalization-plans/stage-ii/report-dag13-ns-coverage.md)へ。
