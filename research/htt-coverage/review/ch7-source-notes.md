# 第7章の原典の印刷上の注意

2017-04-09 版（PDF の SHA-256 は `toc.md`）の本文とページ画像を確認した。以下は原文を読み替えず、対応表では `none` とした。

| 番号 | 印刷頁 | 確認した表示 | 判定への影響 |
| --- | --- | --- | --- |
| 7.3.4.10 | 773–774 | `locally compact topological space` とあり、直前の 7.3.4.9 の `Hausdorff` は書かれていない。 | Hausdorff を追加した版でこの行を満たしたとは扱わない。K 層と開集合上の高次層との具体的な比較も未供給。 |
| 7.3.5.1 | 777 | pullback square は左上が F(U∩V)、右下が F(U∪V)、矢印は右・下へ向く。 | F が反変であるのに、通常の restriction square と向きが合わない。直後の証明（778頁）は F(X)→F(W1),F(W2)→F(W1∩W2) の通常の向きで議論している。本文の図を補正して通常の層条件に対応させない。 |
| 7.3.5.2 | 778 | 同じく左上が F₀(U∩V)、右下が F₀(U∪V) の右・下向きの図。 | ordinary coherent-site sheaf の binary gluing の型をこの印刷された条件と同じとしない。 |
| 7.3.6.1 | 780 | p_*:X→Y に対して `right adjoint p^*` と印刷されている。 | 通常の geometric morphism の p^* は p_* の左随伴であるが、読み替えて判定しない。本体にはこの cell-like higher geometric morphism の述語自体もない。 |

PDF のページ位置は印刷頁に 18 を加えた値（773頁は PDF 第791頁）。PDF とレンダリング画像はコミットしない。
