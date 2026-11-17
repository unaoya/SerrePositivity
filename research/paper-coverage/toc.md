# 本論文の目次と採用版

- OpenAI, *Positivity of Serre’s Intersection Multiplicity*, **2026-09-23、31ページ**。
- 基準main：`c499fc236`。作業枝：`codex/paper-coverage`。照合日：2026-11-17。
- ローカル原典：[`paper/paper.pdf`](../../paper/paper.pdf)。取得元は [`paper/SOURCE.md`](../../paper/SOURCE.md)。
- 上流コミット：`adc7f1241b42e322a6451854ab7e4b4c146bf78a`。
- 上流パス：`preprints/Positivity-of-Serres-Intersection-Multiplicity-September-23-2026/paper.pdf`（openai/math、Apache-2.0）。
- PDF SHA256：`7985cfbc11547cf659efdd6abc076a0c0371e9a38e8026aa09b23cbb042af917`。
- ページは物理ページと印刷ページが一致する。`layout L` は `pdftotext -layout paper/paper.pdf` 出力の1始まりの行。

## §1〜§5の全見出し

| 節 | 原典の見出し | PDFページ | layout行 |
|---|---|---|---|
| 1 | Introduction | 1 | 13 |
| 1.1 | Background and significance | 1 | 37 |
| 1.2 | Proof strategy | 2 | 77 |
| 1.3 | Consequences | 3 | 139 |
| 1.4 | Conventions | 4 | 190 |
| 2 | Residue fields and normalized length | 4 | 203 |
| 2.1 | Extending the residue field | 5 | 214 |
| 2.2 | Regular bases and the tower length | 5 | 256 |
| 2.3 | Length algebras and parameter homology | 7 | 343 |
| 3 | Rational descent with closed supports | 10 | 481 |
| 3.1 | The truncating invariant and its supports | 10 | 521 |
| 3.2 | Descent for finite surjections | 11 | 580 |
| 3.3 | The geometric orbit argument | 13 | 639 |
| 3.4 | Comparison of ordinary and normalized Euler lengths | 14 | 715 |
| 4 | Supported asymptotic complexes | 16 | 828 |
| 4.1 | The rank quotient and its support condition | 16 | 850 |
| 4.2 | The supported subquotient | 17 | 885 |
| 4.3 | Nonnegative homology lengths | 18 | 922 |
| 4.4 | Scalar extension and nonlifting idempotents | 19 | 1014 |
| 4.5 | Connective coefficients and the norm comparison | 21 | 1117 |
| 5 | Proof of strict positivity | 22 | 1192 |
| 5.1 | Reduction and the first norm comparison | 23 | 1199 |
| 5.2 | A parameter quotient and its Tor groups | 24 | 1298 |
| 5.3 | Finite approximations preserving the actions | 26 | 1372 |
| 5.4 | Bounded complexes and their ordinary evaluation | 27 | 1453 |
| 5.5 | A positive normalized evaluation | 28 | 1519 |

## 番号つき項目の範囲

定理・補題・命題・系・Remark **27項目**と番号つき表示式 **47項目**を収録した。この版には番号つきDefinition・Exampleはない。番号つきの図1も1行で残し、計 **75行**。図を除く74項目と区別して集計する。節見出し26件はtocだけに置き、定理の番号と節の番号が同じ場合も混同しない。式は `(4.6)`、Lemmaは `4.6`、図は `Figure 1` としてキーを分ける。番号なしの証明部分を原典の新しい番号としては作らない。

| 章 | 番号つき環境 | 式 | 図 | 計 |
|---|---|---|---|---|
| 1 | 2 | 0 | 1 | 3 |
| 2 | 6 | 8 | 0 | 14 |
| 3 | 6 | 14 | 0 | 20 |
| 4 | 7 | 7 | 0 | 14 |
| 5 | 6 | 18 | 0 | 24 |

## 外部引用の略号と版

登録済みの略号は `research/bibliography.json` と同じものを使う。そこにない文献は、この表だけの局所略号を明示した（共通略号表は変更しない）。外部の番号・版は**本論文のReferencesに書かれた版**に従う。既存の別文献の対応表に別の版が採用されていても、番号や状態を自動移送しない。特にBS19は本論文ではarXiv v4、LTはv3、CLMSTはv4。

`edges.csv` の `depends_on` は `BS19 8.5`・`LT B.3`・`Stacks 0815` の形。原典が項目番号なしで文献全体を引く場合は略号だけとし、存在しない定理番号を補わない。`Main Theorem`・`Appendix 2`等は原典の識別子どおりに残す。

| 本論文の文献番号 | 略号 | 文献 | 本論文が指定する版・番号体系 | 略号の範囲 |
|---|---|---|---|---|
| 1 | BalmerSchlichting | Idempotent completion of triangulated categories | J. Algebra 236 (2001) | 共通略号表 |
| 2 | Berthelot | Altérations de variétés algébriques (Gabber) | Astérisque 241 (1997), Exp.815 | この対応表だけの局所略号 |
| 3 | BHM | Lim Cohen–Macaulay sequences of modules | arXiv:2410.18372v2 (2026-08-25) | この対応表だけの局所略号 |
| 4 | BS19 | Prisms and prismatic cohomology | arXiv:1905.08229v4 (2022-01-12) | 共通略号表 |
| 5 | BGT | A universal characterization of higher algebraic K-theory | arXiv:1001.2282v4 (2013-02-05) | 共通略号表 |
| 6 | CLMST | Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, and an application to local fundamental groups | arXiv:2209.04046v4 (2025-07-03) | この対応表だけの局所略号 |
| 7 | Drinfeld | DG quotients of DG categories | arXiv:math/0210114v7 (2008-02-17) | 共通略号表 |
| 8 | Dutta | A special case of positivity (II) | Proc. AMS 133 (2005) | この対応表だけの局所略号 |
| 9 | Faltings | Almost étale extensions | Astérisque 279 (2002), Appendix 2 | この対応表だけの局所略号 |
| 10 | GabberRamero | Foundations for almost ring theory | arXiv:math/0409584v13 (2018-09-29) | この対応表だけの局所略号 |
| 11 | GilletSoule | Intersection theory using Adams operations | Invent. Math.90 (1987) | この対応表だけの局所略号 |
| 12 | Goodwillie | Relative algebraic K-theory and cyclic homology | Ann. of Math.124 (1986), Main Theorem | 共通略号表 |
| 13 | IshiroShimomoto | δ-rings, perfectoid towers, and lim Cohen–Macaulay sequences | arXiv:2509.06527v3 (2026-05-31) | この対応表だけの局所略号 |
| 14 | Jannsen | Resolution of singularities for embedded curves | Saito–Sato, Ann. of Math.172 (2010), Appendix A | この対応表だけの局所略号 |
| 15 | KCSotoLevins | On liftings of modules of finite projective dimension | arXiv:2404.17572v2 (2024-11-05) | この対応表だけの局所略号 |
| 16 | KuranoRoberts | The positivity of intersection multiplicities and symbolic powers of prime ideals | Compositio Math.122 (2000) | この対応表だけの局所略号 |
| 17 | KuranoShimomoto | An elementary proof of Cohen–Gabber theorem in the equal characteristic p>0 case | Tohoku Math.J.70 (2018), Thm1.1 / arXiv:1510.03573 | この対応表だけの局所略号 |
| 18 | LT | On the K-theory of pullbacks | arXiv:1808.05559v3 (2019-11-08) | 共通略号表 |
| 19 | Ma17 | Lech’s conjecture in dimension three | arXiv:1609.00095v3 (2018-02-13) | この対応表だけの局所略号 |
| 20 | Monsky | The Hilbert–Kunz function | Math. Ann.263 (1983) | この対応表だけの局所略号 |
| 21 | Lech | Lech’s multiplicity conjecture | OpenAI release 2026-09-23 | この対応表だけの局所略号 |
| 22 | Roberts85 | The vanishing of intersection multiplicities of perfect complexes | Bull. AMS13 (1985) | この対応表だけの局所略号 |
| 23 | Roberts85Rennes | Intersection multiplicities in commutative algebra | Rennes (1985), fasc.4 | この対応表だけの局所略号 |
| 24 | Roberts89 | Intersection theorems | MSRI Publications15 (1989) | この対応表だけの局所略号 |
| 25 | Serre | Local Algebra | Springer (2000), Chapter V | この対応表だけの局所略号 |
| 26 | Skalit19 | Positivity of intersection multiplicity over a two-dimensional base | arXiv:1510.05146v2 (2018-07-31) | この対応表だけの局所略号 |
| 27 | Skalit15 | Intersection multiplicity of Serre in the unramified case | arXiv:1409.3616v2 (2014-12-10) | この対応表だけの局所略号 |
| 28 | Stacks | The Stacks Project | accessed 2026-09-23; 0815,03QH,0BRI,0BRJ | 共通略号表 |
| 29 | TT | Higher algebraic K-theory of schemes and of derived categories | Grothendieck Festschrift III (1990), original edition | 共通略号表 |
