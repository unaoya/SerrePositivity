# K 理論の降下の構造（定理 7.3・補題 7.7）

<!-- NB-W4: 凍結解説から転記。 -->

<!-- source: exposition/ja/exposition-ja.tex:2227; block: paper-ja-L2227 -->
<a id="paper-ja-L2227"></a>

定理 7.3 と補題 7.7 について、何を主張し、どの既知の結果の上に立ち、なぜこの形で必要になるのかをここにまとめる。元論文 §1.2・§3・§4・§5 と Kerz–Strunk–Tamme（Invent. Math. 211 (2018)、以下 KST）を読んだ整理である。「推測」「未確認」と書いた箇所は原典で確かめていない。形式化の経路の検討は `formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md`、研究上の問いは `research/k-spectral/k-spectral-ja.tex` §5 にある。

## 解説 §E.1 K 理論が使われる場所

<!-- source: exposition/ja/exposition-ja.tex:2230; block: paper-ja-L2230 -->
<a id="paper-ja-L2230"></a>

定理 7.3 は二回使われる。

<!-- source: exposition/ja/exposition-ja.tex:2232; block: paper-ja-L2232 -->
<a id="paper-ja-L2232"></a>

- **置き換え 1**（命題 7.5、元論文 Lemma 3.5・5.2）：\(H=A\)。底は正則な \(A_D\)、上は Galois 閉包 \(D'\)。比べるのは \(E'\) の自由分解を \(D'\) に延ばした有限 perfect 複体の類である。

<!-- source: exposition/ja/exposition-ja.tex:2233; block: paper-ja-L2233 -->
<a id="paper-ja-L2233"></a>

- **置き換え 2**（定理 7.9）：\(H\) は補題 7.7 のもの。底は \(A_E\)、上は \(E'\)。比べるのはランク無視の圏 \(P^J_{E'}\) の対象である。

<!-- source: exposition/ja/exposition-ja.tex:2235; block: paper-ja-L2235 -->
<a id="paper-ja-L2235"></a>

どちらも双線形形式 \(\chi^R(-,-)\) を展開するのではない。片方を固定した類に二つの準同型 \(\chi_{\mathrm{ord}},\chi_C\) を当て、底から来る類での一致（底公式）を、降下によって共役和に移す（命題 3.6）。

## 解説 §E.2 perfectoid 代数は K の類か

<!-- source: exposition/ja/exposition-ja.tex:2239; block: paper-ja-L2239 -->
<a id="paper-ja-L2239"></a>

- 置き換え 1 では \(C_D\) は類ではなく、評価 \(\chi_{C_D}\) を定める試験対象である。使うのは Koszul 条件だけで、\(C_D\) がネーターかどうかは関係しない。

<!-- source: exposition/ja/exposition-ja.tex:2240; block: paper-ja-L2240 -->
<a id="paper-ja-L2240"></a>

- 置き換え 2 で初めて \(C_D\)（正確には \(U=C_D/I_\sigma C_D\)）を類にする。\(U\) は有限生成でないので、有限近似列 \(M_n\)（§6.5）の極小分解を次数 \(l\) で打ち切って \(E'\) に底変換した列を、ランク無視の圏の対象にする。打ち切りの誤差と台の条件は、階数 \(o(s_n)\) の商で初めて処理される。

<!-- source: exposition/ja/exposition-ja.tex:2241; block: paper-ja-L2241 -->
<a id="paper-ja-L2241"></a>

- \(C_E\) は最後まで評価の側にとどまる。

<!-- source: exposition/ja/exposition-ja.tex:2243; block: paper-ja-L2243 -->
<a id="paper-ja-L2243"></a>

K 理論をとる場所（降下の場）は一貫して \(A\) 上有限型でネーターである。非ネーター性は係数 \(H\) の側（非可換、\(A\) 上有限でなく、正の次数で有界でもないが、連結）に集約される。perfectoid 化は K の降下に入らない。

## 解説 §E.3 係数つき K 理論

<!-- source: exposition/ja/exposition-ja.tex:2246; block: paper-ja-L2246 -->
<a id="paper-ja-L2246"></a>

\(A\) 上のスキーム \(Y\) と連結な \(A\) 代数 \(H\) に対し \(K(Y;H)=K(\operatorname{Perf}(H\otimes^L_A\mathcal O_Y))\) とおく。アフィンなら環 \(H\otimes^L_AB\) の K 理論である。幾何（\(Y\) を動かし、降下を考える側）と係数（\(H\) を固定して運ぶ側）の役割分担であり、降下は前層 \(Y\mapsto K(Y;H)\) の性質として述べる。例えば \(H=M_n(A)\) なら森田同値で \(K(Y)\) に戻り、Azumaya 代数ならひねり K 理論になる。

<!-- source: exposition/ja/exposition-ja.tex:2248; block: paper-ja-L2248 -->
<a id="paper-ja-L2248"></a>

定理 7.3 を最初から一般の連結係数で述べているのは、置き換え 2 で現れるランク無視の圏がどのスキームの \(\operatorname{Perf}\) でもないからである。補題 7.7 でこの圏を「係数つき \(\operatorname{Perf}\)」の一例として書き直し、降下定理をそのまま適用する。降下を新しい圏に合わせて作り直すのではなく、新しい圏を既知の形に帰着させる方針である。何が一般論で何が構成に固有かは注意 7.8。

## 解説 §E.4 降下という主張の型

<!-- source: exposition/ja/exposition-ja.tex:2251; block: paper-ja-L2251 -->
<a id="paper-ja-L2251"></a>

被覆 \(U\to X\) について \(F\) が降下を満たすとは、\(F(X)\) が \(F\) の Cech 図式の極限、つまり「\(U\) 上のデータと重なりでの貼り合わせ」に一致することである。

<!-- source: exposition/ja/exposition-ja.tex:2253; block: paper-ja-L2253 -->
<a id="paper-ja-L2253"></a>

- **Galois 降下**：\(U=\operatorname{Spec} L\to X=\operatorname{Spec} K\) なら \(U\times_XU\cong G\times U\) で、極限は \(F(L)^{hG}\)。貼り合わせデータは \(G\) 作用である。

<!-- source: exposition/ja/exposition-ja.tex:2254; block: paper-ja-L2254 -->
<a id="paper-ja-L2254"></a>

- **cdh 降下**：Nisnevich 四角形と抽象爆発四角形（\(Y\to X\) 固有、閉集合 \(Z\) の外で同型、\(E=Y\times_XZ\)）について \(F(X)\simeq F(Y)\times_{F(E)}F(Z)\)。重なりの情報が \(E\) に集約されるので Cech 条件が四角形に縮む（Voevodsky の cd 構造）。形は Zariski の Mayer–Vietoris と同じで、固有な修正に対する切除である。局所化的不変量では Nisnevich 降下は Thomason–Trobaugh により自動的で、本質は抽象爆発の切除である。帰結として冪零不変性（\(Z=X_{\mathrm{red}}\), \(Y=\emptyset\)）と閉被覆の Mayer–Vietoris が得られ、中心の次元について帰納法が回せる。

<!-- source: exposition/ja/exposition-ja.tex:2255; block: paper-ja-L2255 -->
<a id="paper-ja-L2255"></a>

- **構成可能的・連接的**：捲れ係数のエタールコホモロジーは固有底変換から cdh 降下を満たす。KH、truncating 不変量も満たす。一方 K、HH、HC、\(R\Gamma(-,\mathcal O)\) は冪零に敏感で、爆発に対しては pro でしか降下しない（形式関数定理、KST Thm. A）。\(E=\operatorname{fib}(K_\mathbb{Q}\to K[1/p]_\mathbb{Q})\) をとるのは K を前者の側へ移す操作と読める。

<!-- source: exposition/ja/exposition-ja.tex:2256; block: paper-ja-L2256 -->
<a id="paper-ja-L2256"></a>

- **圏の降下と不変量の降下**：エタールな Galois 被覆について \(\operatorname{Perf}(K)\simeq\operatorname{Perf}(L)^{hG}\) は成り立つが、K 理論は圏の極限と可換でないので \(K(K)\simeq K(L)^{hG}\) は整数係数では一般に成り立たない（Quillen–Lichtenbaum の問題）。定理 7.3 は不変量の水準の降下である。

<!-- source: exposition/ja/exposition-ja.tex:2258; block: paper-ja-L2258 -->
<a id="paper-ja-L2258"></a>

\(\operatorname{Spec} T\to\operatorname{Spec} A\) は一般に cdh 被覆ではない。cdh 被覆は completely decomposed（各点が剰余体を変えずに持ち上がる）であり、次数 \(>1\) の Galois 被覆はこれを満たさない。有限全射が被覆になるのは h 位相からである。

## 解説 §E.5 定理 7.3 の証明の構造

<!-- source: exposition/ja/exposition-ja.tex:2262; block: paper-ja-L2262 -->
<a id="paper-ja-L2262"></a>

1. **cdh 降下（既存の入力）**：\(I=\operatorname{fib}(K_\mathbb{Q}\to\mathrm{HN}(-\otimes\mathbb{Q}/\mathbb{Q}))\) は truncating（Goodwillie）。二つの \(\mathrm{HN}\) の項が打ち消し合うので \(E(U)\simeq\operatorname{fib}(I(U)\to I(U[1/p]))\) も truncating（元論文 (3.4)）。Land–Tamme Thm. A.2・B.3 で係数つき cdh 降下。truncating なので係数については \(\pi_0(H\otimes^L_AB)=\pi_0H\otimes_A\pi_0B\) しか効かず、任意の連結な \(H\) が扱える。台 \(V(J)\subset V(p)\) で切ると実際の台つき有理 K 理論 \(L\) になる（(3.6)）。

<!-- source: exposition/ja/exposition-ja.tex:2263; block: paper-ja-L2263 -->
<a id="paper-ja-L2263"></a>

2. **有限忠実平坦な被覆の降下（Lemma 3.2）**：転送との合成が局所的に階数 \(a\) 倍なので、有理係数では \(a^{-1}\mathrm{trf}\) がレトラクトを与え、分裂した Cech 降下に帰着する。転送をもつ有理係数の前層で標準的な議論である。整数係数では成り立たない。

<!-- source: exposition/ja/exposition-ja.tex:2264; block: paper-ja-L2264 -->
<a id="paper-ja-L2264"></a>

3. **\(\tau\) 降下（Lemma 3.3）**：\(\tau\) は cdh 被覆と有限忠実平坦な被覆で生成される位相で、ほぼ h 位相である。生成する族で層なら \(\tau\) 層であり（形式的で hyperdescent は要らない）、有限全射が \(\tau\) 被覆であることは平坦化爆発と次元の帰納法で示す（幾何的）。整な \(Y\) 上で有限全射は稠密開集合上で平坦であり、そこで同型な平坦化爆発 \(Y'\to Y\) で strict transform が有限平坦になる。中心は次元が下がる。

<!-- source: exposition/ja/exposition-ja.tex:2265; block: paper-ja-L2265 -->
<a id="paper-ja-L2265"></a>

4. **\(hG\) との同一視（§3.3）**：両辺が \(\tau\) 層なので、被覆が切断をもつ場合に帰着する。切断の \(G\) 移動が一致する軌跡の上で抽象爆発四角形を使い、cdh 降下をもう一度使う。自明に作用する安定化群の \(hG\) は有理係数なので普通の不変部分である。

<!-- source: exposition/ja/exposition-ja.tex:2267; block: paper-ja-L2267 -->
<a id="paper-ja-L2267"></a>

平坦な場合でも (4) で cdh 降下が要る。転送から得られるのは \(L(A)\) が \(L(T)\) のレトラクトであることまでで、それが \(G\) 不変部分と一致するには \(f^*\circ\mathrm{trf}=\sum_gg^*\) が要る。これは \(T\otimes_AT\cong\prod_GT\) となるエタールな Galois 被覆では成り立つが、分岐していると崩れる。軌道の議論は「\(X\times_SX\) は cdh 局所的に、冪零を除いて \(G\) 個のコピーの非交和とみなせる」ことを示しており、cdh 降下は分岐した被覆を Galois 被覆として扱うために使われている。また平坦でない場合は実際に現れる：正則な \(A\) 上の有限拡大 \(D'\) が平坦であることは \(D'\) が CM であることと同値であり、Galois 閉包は一般に CM ではない。このとき \(K_\mathbb{Q}\) そのものは降下しない（標数 \(0\) で \(\operatorname{Spec} k\to\operatorname{Spec} k[\varepsilon]\) について \(K_1(k[\varepsilon])_\mathbb{Q}=k^\times_\mathbb{Q}\oplus k\neq K_1(k)_\mathbb{Q}\)）ので、cdh 局所な \(L\) に取り替える必要がある。

## 解説 §E.6 分岐の吸収

<!-- source: exposition/ja/exposition-ja.tex:2270; block: paper-ja-L2270 -->
<a id="paper-ja-L2270"></a>

元論文は平坦性も tame 分岐も仮定しない。分岐は二か所で別の仕組みで吸収される。

<!-- source: exposition/ja/exposition-ja.tex:2272; block: paper-ja-L2272 -->
<a id="paper-ja-L2272"></a>

- **K 理論の側**：有理化（\(|G|\) と階数が可逆）と cdh 降下（非平坦性と分岐の軌跡を次元の低い問題へ押し込む）。整数係数では惰性群が \(p\) 群となる野生分岐で群コホモロジーが残る。幾何ファイバー上の推移性（元論文 §5.1）はノルムと冪等元で示され、不変部分と底変換の可換性（野生分岐で崩れうる）を使わない。

<!-- source: exposition/ja/exposition-ja.tex:2273; block: paper-ja-L2273 -->
<a id="paper-ja-L2273"></a>

- **長さの側**：判別式型の \(g\in A\) で \(A[1/g]\to D[1/g]\) は有限エタールである。混標数では正の次数の Koszul ホモロジーが almost イデアル \((g)_{\mathrm{perfd}}\) で消され（CLMST Cor. 4.0.4）、正規化長さ \(0\) になる（Prop. 4.0.10）。正標数では trace の分母 \(g\) による誤差が \(O(q^{-1})\) で消える。分岐は \(\lambda\) で見えない。

<!-- source: exposition/ja/exposition-ja.tex:2275; block: paper-ja-L2275 -->
<a id="paper-ja-L2275"></a>

Galois 降下が要る理由は perfectoid 化そのものより「\(D\) が正則でない」ことにある。\(\lambda\) は正則な底 \(A\) の塔で測る物差しであり、普通の長さとの一致が保証されるのは \(A\) から来る類だけである。正標数（\(C_D=D_{\mathrm{perf}}\)）でも同じ構造になる。

## 解説 §E.7 新しさについて（推測）

<!-- source: exposition/ja/exposition-ja.tex:2279; block: paper-ja-L2279 -->
<a id="paper-ja-L2279"></a>

- \(H=A\) の場合は既知の理論から導ける可能性が高い（推測）。\(E\) は cdh 局所なので \(L_{\mathrm{cdh}}K\simeq\mathrm{KH}\)（KST Thm. 6.3）から \(E(U)\simeq\operatorname{fib}(\mathrm{KH}(U)_\mathbb{Q}\to\mathrm{KH}(U[1/p])_\mathbb{Q})\) となるはずであり、有理 KH は Beilinson モチーフで表現され h 降下をもつ（Cisinski–Déglise、未確認）。

<!-- source: exposition/ja/exposition-ja.tex:2280; block: paper-ja-L2280 -->
<a id="paper-ja-L2280"></a>

- 元論文が新しい点として挙げるのは「任意の連結な結合的係数での有限全射降下」（§1.2 末）である。係数 \(H\) はスキーム上の層の代数ではなく、モチーフの六関手の枠に載らないので、既知の議論をそのままは流用できない。論文全体の新しさは §6 のランク無視の圏での評価（商の後でのみ台をもつ対象や持ち上がらない冪等元の扱い）にある。

## 解説 §E.8 有理化と TC・シントミック

<!-- source: exposition/ja/exposition-ja.tex:2284; block: paper-ja-L2284 -->
<a id="paper-ja-L2284"></a>

有理化と \(E\) をとる操作で、TC・\(\mathrm{HN}\)（de Rham・シントミックの側）は打ち消し合う。したがって定理 7.3 にシントミックコホモロジーは現れない。整数・\(p\) 進係数へ精密化すればこの打ち消しは起きず、Bouis の混標数モチーフ的コホモロジー（arXiv:2412.06635、2507.16501）で次数 \(\le i\) の \(\mathbb{Z}/p^k(i)^{\mathrm{mot}}\simeq\mathbb{Z}/p^k(i)^{\mathrm{syn}}\) としてシントミックが本質的に現れる。そのとき K の降下の側にも perfectoid（非ネーター）が入ってくる。この方向の問いは `research/k-spectral` にある。
