# P⁰ 閉包の未解決項目：モデル圏なしの出典調査（⑤a）

2026-11-16。基準は main `671f6eafe`、枝 `codex/p0-unresolved-sources`。
対象は同コミットの `item-closure/items.csv` で reason が `unresolved:` の
42 項目（HTT 28、HA 14）。方針は `p0-section-map.md` §9。

## 結果

[unresolved-sources.csv](../../research/p0-lurie/item-closure/unresolved-sources.csv)
に 42 行を記録した。**あり 12（全て HTT）、なし 30（HTT 16、HA 14）**。
「なし」は下記の調査範囲で、同じ一般性の全主張をモデル圏なしに証明した
出典を確認できなかったという意味で、非存在の主張ではない。

採用は HTT 2.3.4.18、3.2.2.12、4.1.1.8、4.3.1.7、4.3.1.9、
5.3.3.3、5.3.4.9、5.3.4.10、5.3.4.12、5.4.1.2、5.4.5.7、5.4.5.13。
複数の番号を合わせて元の全結論を覆う場合は全番号と対応を記載した。
反対双対・定義の展開以外に新しい定理の証明が要る候補は採用に数えていない。
原文のモデル同値・指定射・strict fiber の結論も黙って落としていない。

## 検収上の要点

- HTT 3.2.2.12 は [Kerodon 5.3.6.7 / 0470](https://kerodon.net/tag/0470)
  の反対双対。通常の関手圏だけでなく**相対指数**を扱い、基底も任意の
  単体集合なので、∞圏を基底とする場合に狭めない。
- コンパクト性の二基数表現は
  [Kerodon 9.2.5.14 / 064P](https://kerodon.net/tag/064P)
  が元の一基数の定義と比較している。同じ small の宇宙の境界を λ とする。
  κ は任意の小さい正則基数のままで、ω や特定の非可算基数には限定しない。
  9.2.7.14 の証明に使う二基数版 9.2.7.15 の条件も、この宇宙の境界で満たす。
- HTT 5.3.4.12 の余極限の存在・projection の保存は
  [7.1.9.10 / 06AM](https://kerodon.net/tag/06AM) で別に確認した。
  compactness の系だけで両結論が済んだとはしていない。
- HTT 5.4.5.7 は二結論を分ける。第 (1) 結論は
  [7.1.9.8 / 06AJ](https://kerodon.net/tag/06AJ) で底 Y の余完備性を要しない。
  第 (2) 結論の「Y の対象が κ-compact」は HTT Definition 5.3.4.5 により
  Y が κ-filtered colimit を持つことを前提とする。この段では
  [9.2.8.5 / 06EX](https://kerodon.net/tag/06EX) の仮定を満たす。
  原文への余完備性の仮定の追加ではない。
- HA の「任意の operad fibration」と「coCartesian なモノイダル標的」は
  区別した。自由代数の left adjoint や通常の Alg の極限の結果だけでは、
  Δⁿ 族・相対性・指定 module 模型・高次の充填を含む全主張を置換しなかった。
- 境界・horn の充填、trivial Kan fibration、minimal ∞-category という語だけを
  モデル圏の使用とは判定していない。原証明の具体的な Quillen 比較、
  projective cofibrancy、categorical-pattern のモデル構造などを区別して記録した。
  証明本体が組合せ的でも、引用先の構成を置換しきれていないものは保留した。

## 照合した文献と不採用の理由

原文は既存の閉包と同じ [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
・[HA](https://www.math.ias.edu/~lurie/papers/HA.pdf)（HTT 2017-04-09、HA 2017-09-18 版）。
Kerodon は 2026-11-16 閲覧、CSV には変わり得る番号に加えて恒久 tag の URL を記載した。
候補の主張と証明を読み、番号付きの関連項目まで比較した。

| 文献 | 確認した箇所・限界 |
| --- | --- |
| [Gepner–Haugseng–Nikolaus, Lax Colimits and Free Fibrations in ∞-Categories, arXiv:1501.02161v3](https://arxiv.org/abs/1501.02161v3) | §§3–5, 7, 9。Theorem 4.5 の補助 Lemma 4.9–4.10、Proposition 9.7 などは straightening・contravariant model structure の Quillen 比較を使用する。内在的な主張だけを見てモデル圏なしとは数えなかった。 |
| [Chu–Haugseng, Free algebras through Day convolution](https://arxiv.org/abs/2006.08269) | §§5–6, 8。Prop. 5.5 は HA 2.4.1.5 に対応し、2.4.1.8 の全一意性ではない。Cor. 8.13–8.14 / Rem. 8.15 の自由代数は HA 3.1.2.3 の任意の族・相対 fibration の全主張ではない。§6 の straightening の自然性にはモデル段階の比較もある。 |
| [Haugseng, The higher Morita category of E_n-algebras, arXiv:1412.8459v3](https://arxiv.org/abs/1412.8459v3) | §5、Appendix A。A.47/A.50 は HA 3.1.2.3 の証明を参照し、A.11/A.16 等には categorical-pattern/operad のモデル構造がある。別の非対称 module 模型が存在するだけでは Lurie の指定比較は埋まらない。 |
| [Hinich, Colimits in enriched ∞-categories and Day convolution, arXiv:2101.09538v2](https://arxiv.org/abs/2101.09538v2) | §§6, 8、特に Thm. 6.4.4。豊穣 Yoneda・モノイダルな余極限の結果を、任意の単体集合の指定 Yoneda 構成や任意の operad fibration の比較と同一視しなかった。 |
| [Cisinski, Higher categories and homotopical algebra, 著者 PDF 2026-07-30](https://cisinski.app.uni-regensburg.de/CatLR.pdf) | §§5.5–5.8, 6.4。Yoneda Thm. 5.8.13 は∞圏を域とし、その構成は bivariant model structure の比較を経る。§6.4 の cofinality については、モデル圏なしの Kerodon の出典を採用した。 |
| [Dugger–Isaksen, Hypercovers in topology](https://arxiv.org/abs/math/0111287) | Cor. 3.3、Thm. 4.3、Appendix A。一般の開被覆には対応するが、hocolim と実現の比較の証明が Strøm/Reedy model structure を使用するので HA A.3.2 の代替として採用しない。 |

## 変更・確認と停止

変更は CSV と本報告だけ。元の items.csv・閉包の辺・既存対応表は変更していない。
元の unresolved 42 キーと出力のキー集合の一致、重複なし、指定の六列、
判定数を Python で確認した。Lean の変更・ビルド・監査は行っていない。
報告のコミットで停止する。出典候補の採用や閉包の再展開は調整役に委ねる。
