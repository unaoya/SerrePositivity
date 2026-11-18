# BM18 対応表

Bhatt–Mathew, The arc-topology（arXiv 1807.04725v4）。[版・SHA-256・節別目次](toc.md)。

全 171 項目（番号付き環境 150、番号付き表示式 21）。own 8、mathlib 1、both 0、partial 14、interface 0、none 148。辺 415 件（internal 260、external 155）。

- [items.csv](items.csv) は目録。状態・宣言・理由の正本は [review/](review/)。
- [edges.csv](edges.csv) は PDF の項目参照・文献引用と、明示した経路上の入力。PDF の y はページ上端からの位置。表示式からその所属項目への辺も収めた。引用を含むので、論理的な依存だけを列挙する表とは範囲が異なる。
- [none の検索](review/check/none-search.csv) は同じ見出し・章の主題・本文冒頭から採った語を宣言名とファイル名に照合した結果。件数は機械候補の総数。CSV は上位の候補を示し、全件は git 外の検索記録で読める。none は静的探索で対応を確認できなかったことを示す。
- [証拠目録](../../evidence/cited/bm18/manifest.json) に PDF 抽出、照合した型と検索記録の所在・SHA-256 を収めた。Lean は起動せず、宣言をソースで確認した。

4.8 の G-A6-1 経路 B を `partial / special` とした。完全標数 p のアフィン構造層への制限と、原典の対象圏・関手・被覆の範囲の差は 4.8 の行に記した。

## 既存の対応表からの参照

既存の `research/bs-coverage/review/ch*.csv` と `research/paper-coverage/external.csv` を、略号・arXiv 番号・文献名で照合した。この文献を指す行は確認できなかった。 BS19 8.10 は関連する完全構造層の経路を扱う。BS19 側 review の 8.10 行はこの文献番号を直接掲げておらず、経路 B の出典は ⑥ の 2h・2i 報告を参照。
