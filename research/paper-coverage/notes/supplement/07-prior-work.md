# 先行研究との関係

<!-- NB-W4: 凍結解説から転記。 -->

<!-- source: exposition/ja/exposition-ja.tex:1710; block: paper-ja-L1710 -->
<a id="paper-ja-L1710"></a>

この付録では、§3、§4 の枠組み（長さ関数、長さ \(0\) の加群による Serre 商、長さ付きアーベル圏に値をとるホモロジー的評価）から、二つの先行研究がどう見えるかを整理する。一つは Cai–Lee–Ma–Schwede–Tucker（以下 CLMST、arXiv:2209.04046v4、Invent. Math. 244 (2026)）で、もう一つは Bhatt–Hochster–Ma（以下 BHM、arXiv:2410.18372、J. Reine Angew. Math. 835 (2026)）である。番号は CLMST は arXiv v4、BHM は arXiv v1 による（BHM の §6 の番号が Crelle 版でも同じかは未確認）。

<!-- source: exposition/ja/exposition-ja.tex:1712; block: paper-ja-L1712 -->
<a id="paper-ja-L1712"></a>

以下では、評価の係数（CM な対象）を次の三つの型に分けて呼ぶ。

<!-- source: exposition/ja/exposition-ja.tex:1714; block: paper-ja-L1714 -->
<a id="paper-ja-L1714"></a>

- 型 (i)：有限生成加群と普通の長さ（評価先は有限長加群の圏）。

<!-- source: exposition/ja/exposition-ja.tex:1715; block: paper-ja-L1715 -->
<a id="paper-ja-L1715"></a>

- 型 (ii)：巨大代数と長さ関数 \(\lambda\)（評価先は \(\mathcal{A}_\lambda\)）。CLMST の perfectoid 化や \(D_{\mathrm{perf}}\) がこれに当たる。

<!-- source: exposition/ja/exposition-ja.tex:1716; block: paper-ja-L1716 -->
<a id="paper-ja-L1716"></a>

- 型 (iii)：有限加群の列と正規化した長さ \(\lim_\mathcal{U}\ell(\cdot)/s_n\)（評価先は §6.2 の列の Serre 商）。

## 解説 §B.1 CLMST：入力の層

<!-- source: exposition/ja/exposition-ja.tex:1721; block: paper-ja-L1721 -->
<a id="paper-ja-L1721"></a>

CLMST は、混標数の完備局所整域 \(R\) と、その中の正則な基底 \(A = W(k)[[x_2,\dots,x_d]]\) について、perfectoid 化 \(C = R^{A_\infty}_{\mathrm{perfd}} = (R\otimes_A A_\infty)_{\mathrm{perfd}}\) を調べている（Notation 4.0.1）。解説で使うのは次の結果である。

<!-- source: exposition/ja/exposition-ja.tex:1723; block: paper-ja-L1723 -->
<a id="paper-ja-L1723"></a>

- **Def. 2.2.1、Prop. 2.2.3、2.2.6**：Faltings の正規化長さ \(\lambda_\infty\) を、\(A_\infty^{nc}\) 上の \(\mathfrak{m}_A\)-冪ねじれ加群の上に3段階（有限表示、有限生成、一般）で定義する。短完全列で加法的で、推移写像が単射（または全射で値が有限）の有向余極限と交換する。

<!-- source: exposition/ja/exposition-ja.tex:1724; block: paper-ja-L1724 -->
<a id="paper-ja-L1724"></a>

- **Thm. 4.0.3**：\(C\) は \(A\) 上 \(g\)-almost flat で、\(g\)-almost faithful。

<!-- source: exposition/ja/exposition-ja.tex:1725; block: paper-ja-L1725 -->
<a id="paper-ja-L1725"></a>

- **Cor. 4.0.4**：\(A_n\otimes_A R\) の任意のパラメータ系 \(\bar y\) について、\(H_i(\bar y; C)\)（\(i>0\)）は \((g)_{\mathrm{perfd}}\) で消える（almost CM）。

<!-- source: exposition/ja/exposition-ja.tex:1726; block: paper-ja-L1726 -->
<a id="paper-ja-L1726"></a>

- **Prop. 4.0.10**：almost で同型な加群は \(\lambda_\infty\) が等しく、特に almost zero な加群は \(\lambda_\infty = 0\)。CLMST はこれを「almost 加群に正規化長さが定義できる」と解釈している。逆は一般に成り立たず、\(\lambda_\infty = 0\) からは \(v\)-almost zero しか出ない（Lemma 4.0.13、Shimomoto）。

<!-- source: exposition/ja/exposition-ja.tex:1727; block: paper-ja-L1727 -->
<a id="paper-ja-L1727"></a>

- **Prop. 4.0.14**：\(\lambda_\infty(C/\bar yC) = p^{-nd}\,e(\bar y; A_n\otimes_A R)\)。特に \(\lambda_\infty(C/\mathfrak{m}_A C) = \operatorname{rank}_A R\)。

<!-- source: exposition/ja/exposition-ja.tex:1728; block: paper-ja-L1728 -->
<a id="paper-ja-L1728"></a>

- **Cor. 4.0.18**：perfectoid Hilbert–Kunz 重複度 \(e_{\mathrm{perfd}}(I) = \lambda_\infty(C/IC)\) は \(e(I)\) 以下で、\(I\) がパラメータイデアルなら等号。

<!-- source: exposition/ja/exposition-ja.tex:1730; block: paper-ja-L1730 -->
<a id="paper-ja-L1730"></a>

CLMST には、複体の Euler 特性、\(K_0\)、Dutta 重複度、lim CM 列は現れない。

## 概念の対応

<!-- source: exposition/ja/exposition-ja.tex:1733–1749; block: paper-ja-L1733 -->
<a id="paper-ja-L1733"></a>

| この解説 | CLMST | 関係 |
| --- | --- | --- |
| 長さ関数 \(\lambda\)（定義 4.1） | 正規化長さ \(\lambda_\infty\)（Def. 2.2.1） | \(\lambda_\infty\) はその一例 |
| 長さ \(0\) の加群による Serre 商 \(\mathcal{A}_\lambda\)（定義 4.5） | almost 加群の圏と、その上の正規化長さ（Prop. 4.0.10） | 商は「加群 \(\to\) almost 加群 \(\to\mathcal{A}_\lambda\)」と続く。後半の包含は真（Lemma 4.0.13） |
| 長さ付きアーベル圏（定義 3.1） | なし | CLMST は長さが almost 加群に降りることまで。忠実な長さをもつアーベル圏としての扱いと、ホモロジー的評価はこの解説の視点 |
| \(\lambda\)-平坦（定義 4.9） | almost flat（Thm. 4.0.3） | almost flat と Prop. 4.0.10 から \(\lambda\)-平坦 |
| \(\lambda\)-CM（定義 4.14） | almost CM（Cor. 4.0.4） | almost CM と Prop. 4.0.10 から \(\lambda\)-CM。定理 8.5 の混標数の場合はこの合成 |
| ランク、\(\lambda(C/xC) = e\) | Prop. 4.0.14、Cor. 4.0.18 | そのまま対応 |
| 弱い \(\lambda\)-CM（\(\lambda\)-重複度 \(=\) \(0\) 次の長さ） | パラメータイデアルで \(e_{\mathrm{perfd}} = e\)（Cor. 4.0.18） | 同じ現象 |
| 複体の評価、\(K_0\) 上の準同型、\(e_\lambda\) 公式、対称なノルム比較（命題 5.3、5.8、定理 5.9） | なし | 元論文 §3–§4 をこの解説で抽象化した層 |

## まとめ

<!-- source: exposition/ja/exposition-ja.tex:1752; block: paper-ja-L1752 -->
<a id="paper-ja-L1752"></a>

CLMST が与えるのは「\(\lambda\)-CM で、パラメータ商の長さが重複度に等しい長さ付き代数が存在する」という**入力の層**であり、そこへ至る論法（almost で消えるなら \(\lambda\) でも消える）も Prop. 4.0.10 に書かれている。長さ付きアーベル圏に値をとるホモロジー的評価と、その上の比較の一般論は、先行研究に対応するものが見当たらない。

## 解説 §B.2 BHM：lim CM 列

## BHM がやっていること

<!-- source: exposition/ja/exposition-ja.tex:1757; block: paper-ja-L1757 -->
<a id="paper-ja-L1757"></a>

BHM は、正則局所環 \(T\) 上の正値性を、両側の商整域 \(R = T/P\)、\(S = T/Q\) の「極限で CM な有限加群の列」に帰着する。

<!-- source: exposition/ja/exposition-ja.tex:1759; block: paper-ja-L1759 -->
<a id="paper-ja-L1759"></a>

- **lim CM 列**（Def. 1.1、4.2）：有限生成 \(R\) 加群の列 \((M_n)\) で、あるパラメータ系 \(x\) について \(\ell H_i(x;M_n) = o(\nu(M_n))\)（\(i\ge1\)）となるもの。\(\nu\) は極小生成元数。パラメータ系の取り方によらず（Thm. 4.6）、\(R\) が整域なら \(\nu\) を階数に替えてもよい（Thm. 4.17）。

<!-- source: exposition/ja/exposition-ja.tex:1760; block: paper-ja-L1760 -->
<a id="paper-ja-L1760"></a>

- **弱い lim CM**（§4.1）：\(\chi_1(x;M_n) = o(\nu(M_n))\)。lim CM なら弱い lim CM（Prop. 4.8）。弱い lim CM なら \(\lim\ell H_0(x;M_n)/\operatorname{rank} M_n = e(x;R)\)（Lemma 4.16）。

<!-- source: exposition/ja/exposition-ja.tex:1761; block: paper-ja-L1761 -->
<a id="paper-ja-L1761"></a>

- **存在**（Thm. 5.4）：標数 \(p\) で \(R\) が F-有限なら \(\{F^e_*R\}\) は lim CM。混標数での存在は限定的。

<!-- source: exposition/ja/exposition-ja.tex:1762; block: paper-ja-L1762 -->
<a id="paper-ja-L1762"></a>

- **正値性**（Thm. 6.1）：\(R\)、\(S\) がともに lim CM 列 \((M_n)\)、\((N_n)\) をもてば、\(\chi(R,S) = \lim\ell(M_n\otimes N_n)/(\operatorname{rank} M_n\cdot\operatorname{rank} N_n)\ge1\)。

<!-- source: exposition/ja/exposition-ja.tex:1764; block: paper-ja-L1764 -->
<a id="paper-ja-L1764"></a>

Thm. 6.1 の証明は3段である。

<!-- source: exposition/ja/exposition-ja.tex:1766; block: paper-ja-L1766 -->
<a id="paper-ja-L1766"></a>

1. 消滅定理と双加法性により、各 \(n\) で厳密に \(\chi(M_n,N_n) = \operatorname{rank} M_n\cdot\operatorname{rank} N_n\cdot\chi(R,S)\)。

<!-- source: exposition/ja/exposition-ja.tex:1767; block: paper-ja-L1767 -->
<a id="paper-ja-L1767"></a>

2. 両側のパラメータ系の Koszul 複体を同時に使う多重 Tor の評価で、\(i\ge1\) の \(\ell\operatorname{Tor}_i(M_n,N_n)\) は \(o(\operatorname{rank} M_n\cdot\operatorname{rank} N_n)\)。

<!-- source: exposition/ja/exposition-ja.tex:1768; block: paper-ja-L1768 -->
<a id="paper-ja-L1768"></a>

3. \(\ell(M_n\otimes N_n)\ge\nu(M_n)\nu(N_n)\ge\operatorname{rank} M_n\cdot\operatorname{rank} N_n\)（Rem. 6.2）。

<!-- source: exposition/ja/exposition-ja.tex:1770; block: paper-ja-L1770 -->
<a id="paper-ja-L1770"></a>

Galois 拡大や K 理論の降下は現れない。

## lim CM と \(\lambda\)-CM

<!-- source: exposition/ja/exposition-ja.tex:1774; block: paper-ja-L1774 -->
<a id="paper-ja-L1774"></a>

1. **lim CM は列の圏での \(\lambda\)-CM である。** §6.2 の列の Serre 商で、長さを \(L((V_n)) = \lim_\mathcal{U}\ell(V_n)/\nu(M_n)\) とおく。lim CM は \(L(H_i(x;M_n)) = 0\)（\(i\ge1\)）、すなわち列 \((M_n)\) がこの圏で \(\lambda\)-CM であることに当たり、全ての非単項超フィルターについて成り立つことと同値である。

<!-- source: exposition/ja/exposition-ja.tex:1776; block: paper-ja-L1776 -->
<a id="paper-ja-L1776"></a>

  - パラメータ商の長さの有限性は自動的である（\(\nu\le\ell H_0\le\ell(R/x)\,\nu\)、BHM Rem. 4.13）。

<!-- source: exposition/ja/exposition-ja.tex:1777; block: paper-ja-L1777 -->
<a id="paper-ja-L1777"></a>

  - \(\nu\) で正規化すると \(L((M_n/\mathfrak{m} M_n)) = 1\) で、非自明性も自動的である。BHM で正値性が \(\nu\ge\operatorname{rank}\) から出るのはこのためである。

<!-- source: exposition/ja/exposition-ja.tex:1778; block: paper-ja-L1778 -->
<a id="paper-ja-L1778"></a>

  - 弱い lim CM は弱い \(\lambda\)-CM（\(\lambda\)-重複度 \(=\) \(0\) 次の長さ）に当たる。\(\lambda\)-重複度は Serre の公式から自動的に \(\operatorname{rank}\cdot e(x;R)\) で、BHM Lemma 4.16 はこの形である。

<!-- source: exposition/ja/exposition-ja.tex:1780; block: paper-ja-L1780 -->
<a id="paper-ja-L1780"></a>

1. BHM の対象は代数ではなく加群の列だが、3 の一般論は \(C\) の代数構造をほとんど使わないので、この違いは問題にならない。

<!-- source: exposition/ja/exposition-ja.tex:1781; block: paper-ja-L1781 -->
<a id="paper-ja-L1781"></a>

2. **標数 \(p\) では同じものの二つの見方である。** 列として \(\{F^e_*R\}\) は lim CM（BHM Thm. 5.4）、極限として \(R_{\mathrm{perf}}\) と \(\lambda_\infty\) は \(\lambda\)-CM（Roberts の Frobenius ホモロジー定理、定理 8.5 の標数 \(p\) の場合）。正規化は BHM が \(\nu\)、\(\lambda_\infty\) が \(p^{ed}\) で、比は Hilbert–Kunz 重複度のような定数である（BHM Lemma 5.3）。

<!-- source: exposition/ja/exposition-ja.tex:1782; block: paper-ja-L1782 -->
<a id="paper-ja-L1782"></a>

3. **混標数では二つの見方が分かれる。** \(\lambda\)-CM 代数（型 (ii)）を lim CM 列（型 (iii)）に降ろすには、\(\lambda\) が \(D\) 上有限な段で計算できる必要がある。Ishiro–Shimomoto（arXiv:2509.06527、Thm. 3.17）は、\(D\) 上の perfectoid tower があればその段が lim CM 列になることを示した。CLMST の \(\lambda\)-CM 代数は正則な基底 \(A\) の塔で \(\lambda\) を測るので、\(D\) 上の lim CM 列には直接は降りない。

<!-- source: exposition/ja/exposition-ja.tex:1783; block: paper-ja-L1783 -->
<a id="paper-ja-L1783"></a>

4. **列の使い方が逆である。** BHM では列は係数（CM な対象）の側にあり、評価されるのは単一の有限加群どうしの Tor である。元論文の §6 では CM な対象は単一の \(\lambda\)-CM 代数 \(C_E\) で、列は評価される自由複体の側にある。§6.2 の列の Serre 商は、どちらの使い方も同じ形で扱える。元論文の有限近似で作る有限長 \(B\) 加群の列 \(M_n\) は \(D\) 上の lim CM 列ではなく、\(C_D\) の \(\lambda\)-CM 性をパラメータ商で \(B\) に移したもの（\(\lambda\) の意味で射影次元 \(\le l\)、補題 5.14）を列の側に映したものである。

## 正値性の二つの証明の対比

<!-- source: exposition/ja/exposition-ja.tex:1787–1800; block: paper-ja-L1787 -->
<a id="paper-ja-L1787"></a>

|  | BHM Thm. 6.1 | 元論文 |
| --- | --- | --- |
| CM な対象 | 両側の lim CM 列（有限加群、型 (iii)） | 両側の \(\lambda\)-CM 代数（有限でない、型 (ii)） |
| 存在 | 混標数では未知 | CLMST により無条件 |
| \(\chi(D,E)\) との比較 | 消滅定理だけで厳密に階数倍 | 有理 K 理論の降下（定理 5.9）と Galois 閉包、ランク無視の圏 |
| 高次の消滅 | 両側の Koszul を同時に使う多重 Tor | \(D\) 側の \(\lambda\) 版 Auslander–Buchsbaum と \(E\) 側の新交叉型の消滅 |
| 正値性 | \(\nu\ge\operatorname{rank}\) | 非自明性（系 8.7）と生成元数の下界 |

<!-- source: exposition/ja/exposition-ja.tex:1801; block: paper-ja-L1801 -->
<a id="paper-ja-L1801"></a>

CM な対象が有限加群なら、普通の長さで測れるので、二つの評価が基底から来る類で一致すること（定理 5.9 の仮定）は消滅定理から自動的に出る。巨大代数ではそうならないので、元論文は降下で補う。この意味で、元論文の主定理は「BHM Thm. 6.1 の \(\lambda\)-CM 代数版」と読める。BHM では入力（両側の lim CM 列）の存在が混標数で未知であるのに対し、元論文の入力（両側の \(\lambda\)-CM 代数）は CLMST により存在し、代償として比較に降下とランク無視の圏が要る。

## 確かめていないこと

<!-- source: exposition/ja/exposition-ja.tex:1805; block: paper-ja-L1805 -->
<a id="paper-ja-L1805"></a>

- BHM Thm. 4.6（パラメータ系への非依存性）の \(\lambda\)-CM 版が一般の \(\lambda\) で成り立つか。BHM の証明は有限加群の長さの評価を使う。解説では「任意のパラメータ系」を定義に入れているので影響はない。

<!-- source: exposition/ja/exposition-ja.tex:1806; block: paper-ja-L1806 -->
<a id="paper-ja-L1806"></a>

- lim CM 列から巨大 CM 加群が出ること（BHM §9、Dietz 閉包）の \(\lambda\)-CM 版。

<!-- source: exposition/ja/exposition-ja.tex:1807; block: paper-ja-L1807 -->
<a id="paper-ja-L1807"></a>

- BHM §6 の番号が Crelle 版でも同じか。

## 解説 §B.3 Lech の論文

<!-- source: exposition/ja/exposition-ja.tex:1812; block: paper-ja-L1812 -->
<a id="paper-ja-L1812"></a>

元論文と同日に、同じ方法を使う論文が二つ公開されている。OpenAI, *Lech's multiplicity conjecture* と、OpenAI, *A Complete Local Domain without a Small Cohen–Macaulay Module*（いずれも 2026-09-23、openai/math の `preprints/` 以下）である。前者も長さ付き代数とその Serre 商という同じ枠組みを使い、有限加群の列（Ma の弱い lim Ulrich 列）の代わりに \(\lambda\)-CM 代数と短い複体の一様な評価を使う。これらとの関係は、Lech の論文の解説（`exposition/ja/lech-ja.tex`、PDF は同じ場所）の「Serre の論文との関係」の節にまとめた。
