# \(\lambda\)-平坦を主役にした整理の検討

<!-- NB-W4: 凍結解説から転記。 -->

<!-- source: exposition/ja/exposition-ja.tex:2068; block: paper-ja-L2068 -->
<a id="paper-ja-L2068"></a>

この付録では、\(\lambda\)-CM の代わりに \(\lambda\)-平坦（almost flat の対応物）を基本の概念にして議論を整理できるかを検討する。結論を先に書くと、本文のほとんどの箇所は \(\lambda\)-平坦だけで足り、\(\lambda\)-CM が必要なのは \(D\) 側のパラメータ商の一箇所だけである。そこを \(\lambda\)-平坦から導けるかは未解決である。

## 解説 §D.1 現状の定義

<!-- source: exposition/ja/exposition-ja.tex:2072; block: paper-ja-L2072 -->
<a id="paper-ja-L2072"></a>

- \(\lambda\)-平坦（定義 4.9）：正則な基底 \(A\) の上で、全ての有限長 \(A\) 加群 \(V\) と \(i>0\) について \(\lambda\operatorname{Tor}_i^A(V,C)=0\)。\(k\) で判定でき（補題 4.10）、正則パラメータ系の条件と同値である（系 4.11）。

<!-- source: exposition/ja/exposition-ja.tex:2073; block: paper-ja-L2073 -->
<a id="paper-ja-L2073"></a>

- \(\lambda\)-CM（定義 4.14）：\(D\) の任意のパラメータ系 \(x\) について \(\lambda H_i(x;C)=0\)（\(i>0\)）。

<!-- source: exposition/ja/exposition-ja.tex:2074; block: paper-ja-L2074 -->
<a id="paper-ja-L2074"></a>

- \(\lambda\)-CM なら、\(D\) 上有限な正則部分環 \(A\) の上で \(\lambda\)-平坦である（命題 4.15）。逆は示していない。

<!-- source: exposition/ja/exposition-ja.tex:2076; block: paper-ja-L2076 -->
<a id="paper-ja-L2076"></a>

\(\lambda\)-平坦は、有限長 \(A\) 加群の圏から Serre 商 \(\mathcal{A}_\lambda\) への関手 \(V\mapsto q(V\otimes_A C)\) が完全関手になることと同じである（§4.3「$\lambda$-平坦性の意味」）。ランク \(r\) は \(\lambda\circ q(-\otimes_A C) = r\cdot\ell_A\) という条件である。3 の一般論（\(K_0\) への準同型、Euler 特性の比較）が使うのは、ほぼこの完全関手の性質だけである。CLMST の対応する結果は almost flat（Thm. 4.0.3）で、almost flat と Prop. 4.0.10 から \(\lambda\)-平坦が出る（§B.1）。

<!-- source: exposition/ja/exposition-ja.tex:2078; block: paper-ja-L2078 -->
<a id="paper-ja-L2078"></a>

古典的な対応は次のとおりである。

<!-- source: exposition/ja/exposition-ja.tex:2080; block: paper-ja-L2080 -->
<a id="paper-ja-L2080"></a>

- 有限生成加群 \(M\) が CM であることと、\(M\) が正則な基底 \(A\) の上で自由であることは同値である（Auslander–Buchsbaum）。CM 性は深さで決まり、パラメータ系の取り方によらない。

<!-- source: exposition/ja/exposition-ja.tex:2081; block: paper-ja-L2081 -->
<a id="paper-ja-L2081"></a>

- 巨大加群では、正則な基底の上で平坦であることと、基底から来るパラメータ系が正則列であることは同値である。しかし任意のパラメータ系について正則列になる（balanced）とは限らず、balanced にするには完備化が要る（Bartijn–Strooker、Griffith。文献の主張の正確な形は未確認）。

<!-- source: exposition/ja/exposition-ja.tex:2083; block: paper-ja-L2083 -->
<a id="paper-ja-L2083"></a>

\(\lambda\)-平坦と \(\lambda\)-CM の差は、後者の「基底によらない」部分にある。

## 解説 §D.2 本文でどちらの条件を使っているか

<!-- source: exposition/ja/exposition-ja.tex:2086–2097; block: paper-ja-L2086 -->
<a id="paper-ja-L2086"></a>

| 使う場所 | 必要な条件 |
| --- | --- |
| §5 の比較、§6 のランク無視の圏 | \(A\) 上の \(\lambda\)-平坦とランク \(r\) |
| 新交叉型の消滅（補題 5.10、補題 6.11。\(E\) 側） | \(A_E\) 上の \(\lambda\)-平坦（\(A_E\) のパラメータ系だけを使う） |
| パラメータ商と次数の上界（補題 5.14 とその修正版、§5.5。\(D\) 側） | **\(\lambda\)-CM**：\(R\) の元 \(x\) で像が \(D\) のパラメータ系になるものについて、全ての \(v\) で \(\lambda H_q(x^v;C)=0\)（\(q>0\)） |

<!-- source: exposition/ja/exposition-ja.tex:2098; block: paper-ja-L2098 -->
<a id="paper-ja-L2098"></a>

\(D\) 側で使う \(x\) は \(R\) から来るもので、正則な基底 \(A_D\) の元とは限らない。\(\lambda\)-平坦だけでは足りないのはここだけである。補題 5.14 と §5.5 では \(R\) 上の分解の長さを使い、\(B=R/(x)\) の正則性は仮定しない。\(D\) 側に必要なのは、ここでも \(x\) とその冪に対する Koszul 消滅である。

## 解説 §D.3 隙間を埋める方法の候補

<!-- source: exposition/ja/exposition-ja.tex:2102; block: paper-ja-L2102 -->
<a id="paper-ja-L2102"></a>

1. **\(x\) を含むように基底を選ぶ。** 等標数なら \(k[[x]]\subseteq D\) は正則で、\(D\) はその上で有限である。しかし構成には生成的な分離性（Cohen–Gabber、補題 8.4）が要り、混標数では \(p\) を基底のパラメータに含める必要がある。任意の \(x\) では使えない。

<!-- source: exposition/ja/exposition-ja.tex:2103; block: paper-ja-L2103 -->
<a id="paper-ja-L2103"></a>

2. **「ある \(A\) の上で \(\lambda\)-平坦なら \(\lambda\)-CM」を補題として示す。** 有限加群なら自明だが、巨大加群の古典版では完備化が要る。一方、CLMST は almost flat の定理（Thm. 4.0.3）の系として almost CM（Cor. 4.0.4、\(A_n\otimes_A D\) の任意のパラメータ系）を出している。この論法が \(\lambda\) に移るなら、\(\lambda\)-平坦を主役にできる。

<!-- source: exposition/ja/exposition-ja.tex:2104; block: paper-ja-L2104 -->
<a id="paper-ja-L2104"></a>

3. **\(\lambda\)-CM を「\(\lambda\)-平坦と、パラメータ系への非依存性」として定義し直す。** 古典版の「CM \(\Leftrightarrow\) 正則な基底の上で自由」との対応が最も見えやすい形である。ただし 2 を示さない限り、仮定を言い換えているだけである。

## 解説 §D.4 CM は絶対的、平坦は相対的

<!-- source: exposition/ja/exposition-ja.tex:2109; block: paper-ja-L2109 -->
<a id="paper-ja-L2109"></a>

CM は相対的な概念ではない。有限加群 \(M\) について depth \(M = \dim M\) という条件で、\(R\to D\) が有限な局所準同型なら深さも次元も \(R\) 上と \(D\) 上で同じなので、「\(R\) 上 CM」「\(D\) 上 CM」「\(A\) 上 CM」は全て同じ意味である。一方、平坦（自由）や射影次元は、どの環の上で見るかによる相対的な概念である。

<!-- source: exposition/ja/exposition-ja.tex:2111; block: paper-ja-L2111 -->
<a id="paper-ja-L2111"></a>

\(D\) が正則局所環 \(S\) の上で有限なら、Auslander–Buchsbaum により \(\operatorname{pd}_S D = \dim S - \operatorname{depth}D\ge\dim S-\dim D\) で、等号は \(D\) が CM であることと同値である。一つの絶対的な性質が、基底によって次のように見える。

<!-- source: exposition/ja/exposition-ja.tex:2112–2122; block: paper-ja-L2112 -->
<a id="paper-ja-L2112"></a>

| 基底 \(S\) | \(\dim S\) | CM の現れ方 |
| --- | --- | --- |
| \(A\)（\(D\) の中の正則な基底） | \(h\) | \(\operatorname{pd}_A D = 0\)、すなわち \(A\) 上自由（平坦） |
| \(R\)（\(D = R/P\)） | \(d>h\) | \(\operatorname{pd}_R D = d-h\)（perfect）、すなわち \(R\) 上の Tor を計算する複体が短い |

<!-- source: exposition/ja/exposition-ja.tex:2123; block: paper-ja-L2123 -->
<a id="paper-ja-L2123"></a>

\(D\) は \(R\) の商なので \(R\) 上で平坦になることはなく、Serre の Euler 特性で問題になるのは \(R\) 上の射影次元である。

<!-- source: exposition/ja/exposition-ja.tex:2125–2129; block: paper-ja-L2125 -->
<a id="paper-ja-L2125"></a>

欠陥の層も \(D\) に内在的で、基底によって添字がずれるだけである。正則な \(A\) と \(R\) の上の局所双対から

\[
H^j_\mathfrak{m}(D)^\vee\cong\operatorname{Ext}^{h-j}_A(D,A)\cong\operatorname{Ext}^{d-j}_R(D,R),\qquad\text{すなわち}\quad \operatorname{Ext}^c_A(D,A)\cong\operatorname{Ext}^{c+(d-h)}_R(D,R)
\]

となる。§C.5 の \(E^c\) は、\(R\) の側から見れば \(d-h\) を超える次数の Ext であり、平坦でない場所 \(W\)（CM でない場所）も同じである。

<!-- source: exposition/ja/exposition-ja.tex:2131; block: paper-ja-L2131 -->
<a id="paper-ja-L2131"></a>

\(\lambda\) 版では、この絶対性が自動的には成り立たない。\(C_D\) は \(D\) 上有限でないからである。巨大加群の古典版でも、巨大 CM 加群はもともと「あるパラメータ系が正則列になる」という相対的な定義で、任意のパラメータ系について正則列になる（balanced）には完備化が要る。\(\lambda\)-CM（定義 4.14）は balanced に当たる絶対的な条件として定義し、\(\lambda\)-平坦（定義 4.9）は基底 \(A\) に相対的な条件である。有限加群なら両者は同値だが、有限でない対象では「相対的な条件から絶対的な条件が出るか」が問題として残る。これが上の隙間の正体である。

## 解説 §D.5 なぜ両側を取り替えるのか

<!-- source: exposition/ja/exposition-ja.tex:2135; block: paper-ja-L2135 -->
<a id="paper-ja-L2135"></a>

「\(\lambda\)-CM が必要なのは \(D\) 側だけ」というのは、両側の CM 性の強さが違うという意味であり、\(E\) 側に CM 的な性質が要らないという意味ではない。

## 古典版での役割分担

<!-- source: exposition/ja/exposition-ja.tex:2138; block: paper-ja-L2138 -->
<a id="paper-ja-L2138"></a>

\(D\)、\(E\) がともに CM なら \(\operatorname{Tor}^R_i(D,E) = 0\)（\(i>0\)）である。この議論は二つに分かれる。

<!-- source: exposition/ja/exposition-ja.tex:2140; block: paper-ja-L2140 -->
<a id="paper-ja-L2140"></a>

1. **\(D\) が CM なら複体が短い。** \(D\) の \(R\) 上の自由分解 \(G\) は長さ \(\operatorname{pd}_R D = d-h = l\) で、\(\operatorname{Tor}^R(D,E)\) は長さ \(l = \dim E\) の複体 \(G\otimes E\) のホモロジーである。

<!-- source: exposition/ja/exposition-ja.tex:2141; block: paper-ja-L2141 -->
<a id="paper-ja-L2141"></a>

2. **\(E\) が CM なら短い複体の高次が消える。** \(G\otimes E\) は \(E\) 上の長さ \(\dim E\) の有限自由複体で、ホモロジーは有限長である。\(E\) が CM なら、Peskine–Szpiro の acyclicity lemma（新交叉型の議論）により正の次数のホモロジーは消える。

<!-- source: exposition/ja/exposition-ja.tex:2143; block: paper-ja-L2143 -->
<a id="paper-ja-L2143"></a>

\(D\) が CM でなければ複体の長さが \(\dim E\) を超え、新交叉型の議論は何も言わない。\(E\) が CM でなければ、短い複体でも高次が消える保証はない（新交叉定理は「長さが \(\dim\) 以上でなければホモロジーは \(0\) にならない」という下からの評価で、消滅は \(E\) の深さから来る）。二つの \(l\) が噛み合うのは \(h+l = d\) による。BHM Thm. 6.1 が両側に lim CM 列を要求するのも同じ理由である。

## 片側の平坦性で Tor が消えるのはいつか

<!-- source: exposition/ja/exposition-ja.tex:2146; block: paper-ja-L2146 -->
<a id="paper-ja-L2146"></a>

片側が平坦なら Tor は消えるが、それは平坦性が Tor を計算する環の上で成り立つときに限る。\(D\)、\(E\) は \(R\) の商なので \(R\) 上で平坦にはならず、手元にあるのは別の環 \(A_D\) の上の平坦性である。それを \(R\) 上の情報に翻訳すると「\(R\) 上の Tor の複体が短い」ことしか出ない（§D.4 の表）。

<!-- source: exposition/ja/exposition-ja.tex:2148; block: paper-ja-L2148 -->
<a id="paper-ja-L2148"></a>

片側が最良でも消えない例：\(D = R/(x_1,\dots,x_l)\)（\(x\) は \(R\) 正則列で \(l = d-h\)、\(E\) の上でパラメータ系になるもの）とする。\(D\) は完全交叉で CM（正則にもできる）だが、\(\operatorname{Tor}^R_i(D,E) = H_i(x;E)\) であり、\(E\) が CM でなければ高次の Koszul ホモロジーは消えない。この例では \(\chi = e(x;E) > 0\) なので正値性は重複度として別の理由で成り立つが、「高次を消して \(0\) 次だけ残す」方法は片側だけでは動かない。

## 元論文での対応

<!-- source: exposition/ja/exposition-ja.tex:2151–2161; block: paper-ja-L2151 -->
<a id="paper-ja-L2151"></a>

|  | 古典版 | 元論文 |
| --- | --- | --- |
| \(D\) 側 | \(\operatorname{pd}_R D = d-h\) | \(\lambda\) 版 Auslander–Buchsbaum（補題 5.14、修正版は §5.5）：\(i>d-h\) で \(\lambda\operatorname{Tor}^R_i(C_D,L) = 0\)。\(R\) から来る \(x\) を使うので \(D\) に内在的な \(\lambda\)-CM が要る |
| \(E\) 側 | \(E\) が CM なら長さ \(l\) の複体は acyclic | \(C_E\) が \(A_E\) 上 \(\lambda\)-平坦なら新交叉型の消滅（補題 5.10、補題 6.11）。\(A_E\) のパラメータで測れる形に持っていけるので、基底に相対的な \(\lambda\)-平坦で足りる |

<!-- source: exposition/ja/exposition-ja.tex:2162; block: paper-ja-L2162 -->
<a id="paper-ja-L2162"></a>

片側の平坦性だけで Tor を消す使い方も元論文にある。それは Tor が基底 \(A\) の上で計算される場面で、\(\lambda\)-平坦の定義そのもの（有限長 \(A\) 加群 \(V\) について \(\lambda\operatorname{Tor}^A_i(V,C) = 0\)）や、§5 の perfect 複体での比較とランクの計算がそうである。\(R\) 上の Euler 特性の高次を消すには両側が要る。二つの基底 \(A_D\)、\(A_E\) は別々なので、どちらか一方の上で全体を平坦にすることはできない。

<!-- source: exposition/ja/exposition-ja.tex:2164; block: paper-ja-L2164 -->
<a id="paper-ja-L2164"></a>

取り替えるたびに Euler 特性はランク倍になり、その回収に K 理論の降下と Galois 閉包を使う。本文ではこれが置き換え 1（\(D\to C_D\)、§5 の命題 7.5）と置き換え 2（\(E\to C_E\)、§6 の漸近版）に分かれている。論文の後半が \(D\) 側と \(E\) 側でほぼ同じ構造を二回繰り返すのは、それぞれの側で「CM 化」と「Euler 特性の回収」を一度ずつ行っているからである。

## 解説 §D.6 局所コホモロジーを経由する方法（見込み）

<!-- source: exposition/ja/exposition-ja.tex:2168; block: paper-ja-L2168 -->
<a id="paper-ja-L2168"></a>

上の候補 2 について、CLMST が almost の世界で使っている論法（Cor. 4.0.4 の証明）が、長さ関数 \(\lambda\) の一般論にも移せる見込みがある。以下は推測で、細部は確かめていない。

## CLMST の論法

<!-- source: exposition/ja/exposition-ja.tex:2171–2179; block: paper-ja-L2171 -->
<a id="paper-ja-L2171"></a>

almost 平坦性（Thm. 4.0.3）から直接得られるのは、基底 \(A\) のパラメータ系 \(x\) についての消滅だけである。CLMST はそれを一度局所コホモロジー

\[
H^i_\mathfrak{m}(C) \cong \varinjlim_t H^i(x^t;C) \cong \varinjlim_t \operatorname{Tor}^A_{d-i}\bigl(A/(x^t),C\bigr)
\]

に移し（\(i<d\) で almost zero）、スペクトル系列

\[
E_2 = H_{i+j}\bigl(y;H^j_\mathfrak{m}(C)\bigr)\ \Longrightarrow\ H_i(y;C)
\]

で任意のパラメータ系 \(y\) に戻している。\(i>0\) のとき、\(j = d\) の項は \(i+j>d\) なので \(0\)、\(j<d\) の項は \(H^j_\mathfrak{m}\) が almost zero なので almost zero である。局所コホモロジーはパラメータ系の取り方によらない量なので、この経由で「基底に相対的な消滅」が「任意のパラメータ系での消滅」になる。

## \(\lambda\) で同じことをする際の問題

<!-- source: exposition/ja/exposition-ja.tex:2182; block: paper-ja-L2182 -->
<a id="paper-ja-L2182"></a>

almost zero は任意の加群について意味をもつが、抽象的な `NormalizedLength.len` は全加群に値を持つが、加法法則は \(\mathfrak{m}_A\) の固定した冪で消される加群にしか要求しない（定義 4.1）。\(H^j_\mathfrak{m}(C)\) は \(\mathfrak{m}\) 冪ねじれだが一つの冪で消えるとは限らないので、「\(H^j_\mathfrak{m}\) の \(\lambda\) が \(0\)」はそのままでは言えない。これが almost のほうが \(\lambda\) より強い唯一の点で、この付録の隙間の正体だと考えられる。

## \(\lambda\) の定義域を延ばす

<!-- source: exposition/ja/exposition-ja.tex:2185–2189; block: paper-ja-L2185 -->
<a id="paper-ja-L2185"></a>

正規化長さの定義（有限生成部分加群の上限）は、\(\mathfrak{m}_A\) 冪ねじれ（固定した冪とは限らない）の加群 \(M\) にもそのまま延ばせる。\(M\) の有限生成部分加群はどれも一つの冪で消えるからである。

\[
\lambda^{\mathrm{ext}}(M) := \sup\{\lambda(N)\mid N\subseteq M\text{ は有限生成}\}.
\]

これは Lück が von Neumann 次元を任意の加群へ延ばしたのと同じ方法である。次が期待される。

<!-- source: exposition/ja/exposition-ja.tex:2191; block: paper-ja-L2191 -->
<a id="paper-ja-L2191"></a>

1. \(\lambda^{\mathrm{ext}}\) は元の定義域では \(\lambda\) に一致し、部分商で単調で、\(\lambda^{\mathrm{ext}} = 0\) は部分商で保たれる。

<!-- source: exposition/ja/exposition-ja.tex:2192; block: paper-ja-L2192 -->
<a id="paper-ja-L2192"></a>

2. \(\lambda\) の各段が \(0\) なら、帰納極限の \(\lambda^{\mathrm{ext}}\) も \(0\)：有限生成部分加群 \(N\subseteq\varinjlim_t M_t\) は、ある段の有限生成部分加群の像なので \(\lambda(N)\le\lambda(M_t\text{ の部分加群}) = 0\)。

## 期待される主張

<!-- source: exposition/ja/exposition-ja.tex:2197; block: paper-ja-L2197 -->
<a id="paper-ja-L2197"></a>

> \((C,\lambda)\) が \(A\) 上 \(\lambda\)-平坦なら、\(D\)（あるいは \(A_n\otimes_A D\)）の任意のパラメータ系 \(y\) について \(\lambda H_i(y;C) = 0\)（\(i>0\)）。すなわち \(\lambda\)-平坦 \(\Rightarrow\) \(\lambda\)-CM。

## 証明の筋書き

<!-- source: exposition/ja/exposition-ja.tex:2201; block: paper-ja-L2201 -->
<a id="paper-ja-L2201"></a>

1. \(\lambda\)-平坦性から、\(i<d\) で \(\lambda H^i(x^t;C) = \lambda\operatorname{Tor}^A_{d-i}(A/(x^t),C) = 0\)（全ての \(t\)）。2 により \(\lambda^{\mathrm{ext}}H^i_\mathfrak{m}(C) = 0\)。

<!-- source: exposition/ja/exposition-ja.tex:2202; block: paper-ja-L2202 -->
<a id="paper-ja-L2202"></a>

2. \(H_i(y;C)\) は \((y)\) で消されるので、\(K(y;C)\simeq K(y;\mathbf{R}\Gamma_\mathfrak{m} C)\) からスペクトル系列 \(H_{i+j}(y;H^j_\mathfrak{m}(C))\Rightarrow H_i(y;C)\) を得る（CLMST Cor. 4.0.4 の証明と同じ）。

<!-- source: exposition/ja/exposition-ja.tex:2203; block: paper-ja-L2203 -->
<a id="paper-ja-L2203"></a>

3. \(E_2\) の項 \(H_k(y;H^j_\mathfrak{m}(C))\) は \(H^j_\mathfrak{m}(C)\) の有限直和の部分商で \((y)\) で消されるので、元の \(\lambda\) の定義域に入り、1 と期待 1 により \(j<d\) で \(\lambda = 0\)。\(j = d\) の項は \(i>0\) で \(0\)。

<!-- source: exposition/ja/exposition-ja.tex:2204; block: paper-ja-L2204 -->
<a id="paper-ja-L2204"></a>

4. 収束先 \(H_i(y;C)\) は有限個の \(E_\infty\) の項（\(E_2\) の部分商）でフィルトレーションされるので、加法性から \(\lambda H_i(y;C) = 0\)。

## 確かめるべきこと

<!-- source: exposition/ja/exposition-ja.tex:2209; block: paper-ja-L2209 -->
<a id="paper-ja-L2209"></a>

- \(\lambda^{\mathrm{ext}}\) が矛盾なく定まり、元の \(\lambda\) と一致し、部分商で単調であること（有限生成の段での単調性は CLMST Lemma 2.2.4 から出るはず）。

<!-- source: exposition/ja/exposition-ja.tex:2210; block: paper-ja-L2210 -->
<a id="paper-ja-L2210"></a>

- \(K(y;C)\simeq K(y;\mathbf{R}\Gamma_\mathfrak{m} C)\) と、スペクトル系列の構成が、\(C\) が非ネーター的な場合にも使えること（\(\mathfrak{m}_A\) は有限生成なので、Čech 複体による局所コホモロジーの記述は使える）。

<!-- source: exposition/ja/exposition-ja.tex:2211; block: paper-ja-L2211 -->
<a id="paper-ja-L2211"></a>

- \(D\) のパラメータ系だけでなく、Serre の論文の補題 5.14 で使う「\(R\) の元で像が \(D\) のパラメータ系になるもの」でも同じ議論が通ること（像だけで Koszul 複体が決まるので、通るはず）。

<!-- source: exposition/ja/exposition-ja.tex:2213; block: paper-ja-L2213 -->
<a id="paper-ja-L2213"></a>

これが成り立てば、\(\lambda\)-CM（定義 4.14）を仮定から外し、\(\lambda\)-平坦（定義 4.9）だけを基本にできる。命題 4.15 の逆が成り立ち、二つの概念は同値になる。

## 解説 §D.7 次にすること

<!-- source: exposition/ja/exposition-ja.tex:2217; block: paper-ja-L2217 -->
<a id="paper-ja-L2217"></a>

- CLMST Cor. 4.0.4 の証明を読み、almost flat から任意のパラメータ系の almost CM 性を出す論法が、長さ関数 \(\lambda\) の一般論に移るかを確かめる。移るなら、\(\lambda\)-平坦を基本の定義にし、\(\lambda\)-CM を系とする書き直し案をこの付録に書く。

<!-- source: exposition/ja/exposition-ja.tex:2218; block: paper-ja-L2218 -->
<a id="paper-ja-L2218"></a>

- 移らない場合は、本文の \(D\) 側の入力を「\(R\) の元 \(x\) についての Koszul 消滅」として明示的な仮定にし、定理 8.5 がそれを供給する、という形に分ける（形式化でも仮定の形を合わせる）。

<!-- source: exposition/ja/exposition-ja.tex:2219; block: paper-ja-L2219 -->
<a id="paper-ja-L2219"></a>

- 補題 5.14 の修正（§5.5 の形への置き換え）と同時に行う。

## \(\lambda\)-エタール

<!-- source: exposition/ja/exposition-ja.tex:2223; block: paper-ja-L2223 -->
<a id="paper-ja-L2223"></a>

分岐（エタール性）の側も \(\lambda\) で測る概念を導入して別の問題に使えないか、という検討は、別のノート（`research/lambda-etale/lambda-etale-ja.tex`）にまとめた。
