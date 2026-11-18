# BS17 対応表

Bhatt–Scholze, Projectivity of the Witt vector affine Grassmannian（arXiv 1507.06490v3）。[版・SHA-256・節別目次](toc.md)。

全 171 項目（番号付き環境 165、番号付き表示式 6）。own 2、mathlib 0、both 0、partial 9、interface 0、none 160。辺 296 件（internal 190、external 106）。

- [items.csv](items.csv) は目録。状態・宣言・理由の正本は [review/](review/)。
- [edges.csv](edges.csv) は PDF の項目参照・文献引用と、明示した経路上の入力。PDF の y はページ上端からの位置。表示式からその所属項目への辺も収めた。引用を含むので、論理的な依存だけを列挙する表とは範囲が異なる。
- [none の検索](review/check/none-search.csv) は同じ見出し・章の主題・本文冒頭から採った語を宣言名とファイル名に照合した結果。件数は機械候補の総数。CSV は上位の候補を示し、全件は git 外の検索記録で読める。none は静的探索で対応を確認できなかったことを示す。
- [証拠目録](../../evidence/cited/bs17/manifest.json) に PDF 抽出、照合した型と検索記録の所在・SHA-256 を収めた。Lean は起動せず、宣言をソースで確認した。

4.1(i) の有限アフィン v 被覆族・完全構造層の Čech 版を `partial / special` とした。4.6 の射影 Čech 版と原典の fppf 層コホモロジーの差は 4.6 の行に記した。

## 既存の対応表からの参照

既存の `research/bs-coverage/review/ch*.csv` と `research/paper-coverage/external.csv` を、略号・arXiv 番号・文献名で照合した。この文献を指す行は確認できなかった。 BS19 8.10 は関連する完全構造層の経路を扱う。BS19 側 review の 8.10 行はこの文献番号を直接掲げておらず、経路 B の出典は ⑥ の 2h・2i 報告を参照。

## 本体の v 降下の依存（NB-W4）

[route-edges.csv](route-edges.csv) は、BS17・BM18・Rydh の review で状態が `none` でない 49 項目について、宣言から参照先へ向けた 112 辺を記録する。識別子は `bs17`・`bm18`・`rydh`。型・定義・証明にある明示参照を読み、番号の付かない補題を経る場合は `evidence` に参照箇所を順に並べた。同じ宣言が複数項目の根拠であるという理由だけでは辺を作らない。

2h の `cech_exact_of_vCover_perfect` は、Frobenius の順極限上の完全性を元の Čech 複体に戻す。2i の `cechExact_of_arcHom_perfect` は、付値 probe での二重 Čech 比較の入力 `bs17VCechInput` にこの v 降下を使う。従って本体の参照は **BM18 4.8 → BS17 4.1** の向きになる。合成の呼び出しは [ArcCoverCech.lean](../../SerrePositivity/AlgebraicGeometry/ArcRouteB/ArcCoverCech.lean#L75)、v 降下を渡す箇所は [ProbeComparison.lean](../../SerrePositivity/AlgebraicGeometry/ArcRouteB/ProbeComparison.lean#L24)。

BS17 4.1 を含めて 16 項目に到達する。以下の 33 項目は、この向きにたどって到達しない。経路 B の出口 BM18 4.8 もここに含む。

| 文献 | 到達しない項目 |
| --- | --- |
| BS17 | 2.5、2.6、2.12、3.1、3.8、3.16、6.3 |
| BM18 | 1.2、2.3、2.8、2.12、2.21、3.2、3.4、3.13、3.15、3.25、3.26、3.27、3.28、3.29、4.4、4.6、4.7、4.8、(6)、5.3、5.17 |
| Rydh | 3.2、3.4、3.7、A.2、B.1 |

静的照合の範囲は、対応する宣言とそれらの本体 import 閉包に現れる明示参照。型クラス探索やタクティク展開から生じる暗黙の依存は集計の範囲外。 [証拠目録](../../evidence/cited/nb-w4-route/manifest.json)。
