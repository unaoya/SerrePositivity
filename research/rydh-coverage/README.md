# Rydh 対応表

Rydh, Submersions and effective descent of étale morphisms（arXiv 0710.2488v3）。[版・SHA-256・節別目次](toc.md)。

全 111 項目（番号付き環境 111、番号付き表示式 0）。own 0、mathlib 2、both 0、partial 13、interface 0、none 96。辺 266 件（internal 151、external 115）。

- [items.csv](items.csv) は目録。状態・宣言・理由の正本は [review/](review/)。
- [edges.csv](edges.csv) は PDF の項目参照・文献引用と、明示した経路上の入力。PDF の y はページ上端からの位置。表示式からその所属項目への辺も収めた。引用を含むので、論理的な依存だけを列挙する表とは範囲が異なる。
- [none の検索](review/check/none-search.csv) は同じ見出し・章の主題・本文冒頭から採った語を宣言名とファイル名に照合した結果。件数は機械候補の総数。CSV は上位の候補を示し、全件は git 外の検索記録で読める。none は静的探索で対応を確認できなかったことを示す。
- [証拠目録](../../evidence/cited/rydh/manifest.json) に PDF 抽出、照合した型と検索記録の所在・SHA-256 を収めた。Lean は起動せず、宣言をソースで確認した。

3.10 のアフィン基底での fppf–proper 細分を `partial / special` とした。3.12 の準コンパクト開被覆–固有細分の判定は別行に置いた。

## 既存の対応表からの参照

既存の `research/bs-coverage/review/ch*.csv` と `research/paper-coverage/external.csv` を、略号・arXiv 番号・文献名で照合した。この文献を指す行は確認できなかった。
