# 拡大すると高次の項が消える理由（直感的な説明）

<!-- NB-W4: 凍結解説から転記。 -->

<!-- source: exposition/ja/exposition-ja.tex:1817; block: paper-ja-L1817 -->
<a id="paper-ja-L1817"></a>

この付録は、定理 8.5 の \(\lambda\)-CM 性がなぜ成り立つのかを、直感的な水準で説明する。議論はまだ精密ではなく、確かめていない主張を含む。精密化すべき点は最後にまとめる。

## 解説 §C.1 何が消え、何が残るのか

<!-- source: exposition/ja/exposition-ja.tex:1821; block: paper-ja-L1821 -->
<a id="paper-ja-L1821"></a>

\(D = R/P\)、\(E = R/Q\) は一般には CM でなく、\(\operatorname{Tor}_i^R(D,E)\)（\(i>0\)）が残りうる。そのため、\(\chi(D,E)\) の各項を見ても正値性はわからない。元論文の証明は、この状況を次の二つに分けて扱う。

<!-- source: exposition/ja/exposition-ja.tex:1823; block: paper-ja-L1823 -->
<a id="paper-ja-L1823"></a>

1. **残る部分**：Euler 特性。\(D\)、\(E\) を \(\lambda\)-CM 代数 \(C_D\)、\(C_E\) に拡大して \(\lambda\) で測ると、Euler 特性はランク倍 \(r_D r_E\,\chi(D,E)\) になる。\(C_D\) は \(R\) 上有限でないので、この等式に K 理論の降下と有限近似（§5–§6）が要る。

<!-- source: exposition/ja/exposition-ja.tex:1824; block: paper-ja-L1824 -->
<a id="paper-ja-L1824"></a>

2. **消える部分**：拡大した側の高次ホモロジー。\(C_D\)、\(C_E\) が \(\lambda\)-CM なので、新交叉型の消滅（補題 5.10）と \(\lambda\) 版 Auslander–Buchsbaum（補題 5.14）により、正の次数のホモロジーは \(\lambda\) が \(0\) になる。\(0\) 次の項は非自明性（系 8.7）から正である。

<!-- source: exposition/ja/exposition-ja.tex:1826; block: paper-ja-L1826 -->
<a id="paper-ja-L1826"></a>

消えるのは「\(\lambda\) で測ると \(0\)」という意味であり、群として \(0\) になるわけではない。また、元の \(\operatorname{Tor}_i^R(D,E)\) が消えるわけでもない。元の側に戻すのは Euler 特性という不変量だけである。

<!-- source: exposition/ja/exposition-ja.tex:1828; block: paper-ja-L1828 -->
<a id="paper-ja-L1828"></a>

以下では、2 の前提である「拡大すると \(\lambda\)-CM になる」ことを三つの見方で説明する。

## 解説 §C.2 見方 1：CM でないことは、正則な基底の上で平坦でないこと

<!-- source: exposition/ja/exposition-ja.tex:1832; block: paper-ja-L1832 -->
<a id="paper-ja-L1832"></a>

\(A\) を \(D\) の中の正則な基底（Cohen–Gabber）とし、\(D\) は \(A\) 上有限とする。

<!-- source: exposition/ja/exposition-ja.tex:1834; block: paper-ja-L1834 -->
<a id="paper-ja-L1834"></a>

- Auslander–Buchsbaum により、\(D\) が CM であることと、\(D\) が \(A\) 上自由であることは同値である。

<!-- source: exposition/ja/exposition-ja.tex:1835; block: paper-ja-L1835 -->
<a id="paper-ja-L1835"></a>

- \(A\) のパラメータ系 \(t\) について \(H_i(t;D) = \operatorname{Tor}^A_i(A/t, D)\) なので、高次 Koszul ホモロジーは \(D\) が \(A\) 上平坦でない度合いを測っている。

<!-- source: exposition/ja/exposition-ja.tex:1837; block: paper-ja-L1837 -->
<a id="paper-ja-L1837"></a>

したがって、拡大の目標は「\(D\) を \(A\) の塔の上でほぼ平坦にすること」と言い換えられる。CLMST の Thm. 4.0.3（\(C\) は \(A\) 上 \(g\)-almost flat）はまさにこの形の主張である。補題 5.14 は、この見方を \(\lambda\) の側で逆向きに使ったもの（\(\lambda\)-CM なら \(\lambda\) の意味で平坦）と読める。

## 解説 §C.3 見方 2：欠陥は低次元にあり、主要項に比べて小さい

<!-- source: exposition/ja/exposition-ja.tex:1841–1845; block: paper-ja-L1841 -->
<a id="paper-ja-L1841"></a>

標数 \(p\) では、増大度の比較として理解できる。例として Macaulay の曲線

\[
D = k[[s^4, s^3t, st^3, t^4]]
\]

を考える。\(\dim D = 2\)、\(\operatorname{depth} D = 1\) で、\(H^1_\mathfrak{m}(D)\cong k\) である。

<!-- source: exposition/ja/exposition-ja.tex:1847; block: paper-ja-L1847 -->
<a id="paper-ja-L1847"></a>

- パラメータ系 \(z\) を \(q\) 乗すると、主要項は \(\ell(D/z^{[q]})\approx q^2 e(z;D)\) と \(q^2\) の速さで増える。

<!-- source: exposition/ja/exposition-ja.tex:1848; block: paper-ja-L1848 -->
<a id="paper-ja-L1848"></a>

- 一方、高次の項 \(\ell H_1(z^{[q]};D)\) は \(q\) によらず有界である（一般化 CM 環で、局所コホモロジー \(H^1_\mathfrak{m}(D)\) の長さで抑えられる。この例での計算は未確認）。

<!-- source: exposition/ja/exposition-ja.tex:1849; block: paper-ja-L1849 -->
<a id="paper-ja-L1849"></a>

- \(D^{1/q}\) の段で \(\lambda = \ell/q^h\) と正規化すると、主要項は \(e(z;D)\) に収束し、欠陥は \(O(q^{-2})\to 0\) となる。

<!-- source: exposition/ja/exposition-ja.tex:1851; block: paper-ja-L1851 -->
<a id="paper-ja-L1851"></a>

一般の場合も、Roberts の Frobenius ホモロジー定理 \(\ell H_i(z^{[q]};D) = o(q^h)\)（\(i>0\)）が同じことを言っている。CM でない欠陥はパラメータを深くしても主要項ほど速くは増えない。\(D^{1/q}\) に移ることは「パラメータを深くして体積で割る」操作であり、\(\lambda\) はこの割り算を極限まで済ませた量である。この意味で、\(D_{\mathrm{perf}}\) の \(\lambda\)-CM 性は \(\{F^e_*D\}\) が lim CM 列であること（BHM Thm. 5.4、§B.2）の極限版である。

<!-- source: exposition/ja/exposition-ja.tex:1853; block: paper-ja-L1853 -->
<a id="paper-ja-L1853"></a>

ここで効いているのは \(D\) のすべての元の \(q\) 乗根をとること（\(D^{1/q}\)）であって、基底 \(A\) のパラメータの \(q\) 乗根を足すこと（\(D\otimes_A A^{1/q}\)）ではない。後者は平坦な基底変換で、それだけでは欠陥は減らない（§C.8）。

## 解説 §C.4 見方 2 の補足：ホモロジーの次数ごとの増大度

<!-- source: exposition/ja/exposition-ja.tex:1857; block: paper-ja-L1857 -->
<a id="paper-ja-L1857"></a>

見方 2 で起きていることを、次数ごとに分けて書く。以下は標数 \(p\) の話である。

## 固定したパラメータが、塔の上では深い冪になる

<!-- source: exposition/ja/exposition-ja.tex:1860–1864; block: paper-ja-L1860 -->
<a id="paper-ja-L1860"></a>

\(D^{1/q}\) は Frobenius によって環として \(D\) と同型であり、この同型で \(D\) の元 \(z\) は \(z^q\) に対応する。言い換えると、\(D^{1/q}\) のパラメータ系 \(z^{1/q}\) から見れば、最初に固定したパラメータ系 \(z\) は \(q\) 乗という深い冪である。したがって

\[
\lambda H_i(z; D^{1/q}) = q^{-h}\,\ell_D H_i(z^{[q]}; D)
\]

であり、\(\lambda\) を計算することは「同じ形の環で、パラメータ系をどんどん深い冪にして Koszul ホモロジーの長さを測り、体積 \(q^h\) で割る」ことである。基底の塔 \(A^{1/q}\) でも同じで、\(A\) のパラメータ \(t_j\) は \(A^{1/q}\) の上では \((t_j^{1/q})^q\) である。

## 次数ごとの増大度

<!-- source: exposition/ja/exposition-ja.tex:1867–1877; block: paper-ja-L1867 -->
<a id="paper-ja-L1867"></a>

| 次数 | 対応する局所コホモロジー | \(\ell_D H_i(z^{[q]};D)\) の増大度 | \(q^{-h}\) で割ると |
| --- | --- | --- | --- |
| \(i = 0\) | \(H^h_\mathfrak{m}(D)\)（最上次。双対は次元 \(h\)） | \(\approx e(z;D)\,q^h\) | \(e(z;D)\) |
| \(i\ge 1\) | \(H^{h-i}_\mathfrak{m}(D)\)（最上次より下。双対は次元 \(\le h-i\)） | \(o(q^h)\)（Roberts）。目安は \(O(q^{h-i})\)（未確認） | \(0\) |

<!-- source: exposition/ja/exposition-ja.tex:1878; block: paper-ja-L1878 -->
<a id="paper-ja-L1878"></a>

表の「対応する局所コホモロジー」は次の意味である。Koszul 複体は自己双対で \(H_i(z;D)\cong H^{h-i}(z;D)\) であり、\(H^j_\mathfrak{m}(D) = \varinjlim_t H^j(z^t;D)\) である。したがって、パラメータを深くしたときの \(H_i(z^t;D)\) は \(H^{h-i}_\mathfrak{m}(D)\) を近似している。局所双対により、\(H^j_\mathfrak{m}(D)\) の Matlis 双対の次元は \(j\) 以下である。

<!-- source: exposition/ja/exposition-ja.tex:1880; block: paper-ja-L1880 -->
<a id="paper-ja-L1880"></a>

- \(i = 0\) の項は最上次の \(H^h_\mathfrak{m}(D)\) に対応し、\(D\) の次元 \(h\) をそのまま感じる。だから \(q^h\) の速さで増える。

<!-- source: exposition/ja/exposition-ja.tex:1881; block: paper-ja-L1881 -->
<a id="paper-ja-L1881"></a>

- \(i\ge 1\) の項は、それより下の \(H^{h-i}_\mathfrak{m}(D)\) に対応する。これは「次元 \(h-i\) 以下のもの」で、パラメータの \(q\) 乗で切り取ると、目安として \(q^{h-i}\) 程度にしか増えない。次数が上がるほど増大度は小さくなる。

<!-- source: exposition/ja/exposition-ja.tex:1883; block: paper-ja-L1883 -->
<a id="paper-ja-L1883"></a>

CM であることは \(H^j_\mathfrak{m}(D) = 0\)（\(j<h\)）、つまり最上次以外の局所コホモロジーが消えることだった。正規化した長さ \(\lambda\) で見ることは、最上次（次元 \(h\)）だけを残し、それより下を無視することに当たる。だから \(\lambda\) で見ると「CM のように振る舞う」。

<!-- source: exposition/ja/exposition-ja.tex:1885; block: paper-ja-L1885 -->
<a id="paper-ja-L1885"></a>

Macaulay の曲線（\(h = 2\)）では、\(H^1_\mathfrak{m}(D)\cong k\) は有限長（双対の次元 \(0\)）なので、\(\ell H_1(z^{[q]};D)\) は有界である。これは目安 \(O(q^{h-1}) = O(q)\) よりさらに小さい。

## 混標数では仕組みが違う

<!-- source: exposition/ja/exposition-ja.tex:1888; block: paper-ja-L1888 -->
<a id="paper-ja-L1888"></a>

混標数で塔の段 \(A_n\otimes_A D\) に移るだけなら、これは平坦な基底変換なので、\(\ell H_i(z;A_n\otimes_A D)\) と体積 \(p^{nh}\) は同じ割合で増え、正規化した欠陥は減らない（§C.8）。混標数では、増大度の差ではなく、perfectoid 化による分岐の希釈（見方 3）が欠陥を消している。上の次数ごとの描像は、そのままでは標数 \(p\) の話である。

## 解説 §C.5 平坦でない場所と Frobenius：Koszul、局所コホモロジー、\(W\) の関係

<!-- source: exposition/ja/exposition-ja.tex:1892; block: paper-ja-L1892 -->
<a id="paper-ja-L1892"></a>

この小節では、見方 1（平坦性）と見方 2（増大度）を一つの描像にまとめ、Koszul 複体による見方、局所コホモロジーによる見方、平坦でない場所 \(W\) による見方がどう対応するかを書く。標数 \(p\) で、\(A\subseteq D\) を正則な基底、\(t\) を \(A\) の正則パラメータ系、\(r = \operatorname{rank}_A D\) とする。剰余体は perfect とする。

## 何で割っているのか

<!-- source: exposition/ja/exposition-ja.tex:1895–1899; block: paper-ja-L1895 -->
<a id="paper-ja-L1895"></a>

これまで「体積で割る」と書いたが、正確には次のとおりである。\(F^n_*A = A^{1/q}\) は \(A\) 上ランク \(q^h\) の自由加群である（Kunz）。\(D^{1/q} = F^n_*D\) を \(A\) 加群として見て、その Betti 数

\[
\beta_i^A(F^n_*D) = \ell\,\operatorname{Tor}_i^A(k, F^n_*D) = \ell\,H_i(t; D^{1/q}) = \ell\,H_i(t^{[q]}; D)
\]

を、\(F^n_*A\) のランク \(q^h\) を単位として測る。\(\lambda\) はこの正規化の極限である。

<!-- source: exposition/ja/exposition-ja.tex:1901; block: paper-ja-L1901 -->
<a id="paper-ja-L1901"></a>

- \(i = 0\)：\(\beta_0^A(F^n_*D)/q^h = \ell(D/t^{[q]}D)/q^h\to e(t;D) = r\)。

<!-- source: exposition/ja/exposition-ja.tex:1902; block: paper-ja-L1902 -->
<a id="paper-ja-L1902"></a>

- \(i\ge 1\)：\(\beta_i^A(F^n_*D)/q^h\to 0\)（Roberts）。

<!-- source: exposition/ja/exposition-ja.tex:1904; block: paper-ja-L1904 -->
<a id="paper-ja-L1904"></a>

つまり \(F^n_*D\) は、\(A\) 上で「ランク \(r q^h\) の自由加群に、相対的に小さい誤差を加えたもの」に近づいていく。これが \(\lambda\)-平坦でランク \(r\)（定義 4.9）の中身であり、BHM の言葉では \(\{F^n_*D\}\) が \(A\) 上の lim CM 列であることに当たる。

## 基底の根と、全ての元の根の違い

<!-- source: exposition/ja/exposition-ja.tex:1908; block: paper-ja-L1908 -->
<a id="paper-ja-L1908"></a>

- 基底の根だけを足すと、\(A\) 加群として \(D\otimes_A A^{1/q}\cong D^{\oplus q^h}\) である。主要項も欠陥も同じく \(q^h\) 倍になるので、比は変わらない。

<!-- source: exposition/ja/exposition-ja.tex:1909; block: paper-ja-L1909 -->
<a id="paper-ja-L1909"></a>

- 全ての元の根をとる \(F^n_*\) は、各部分をその次元に応じて拡大する。次元 \(w\) の素イデアル \(\mathfrak{p}\) について、\(F^n_*(A/\mathfrak{p})\) の \(A/\mathfrak{p}\) 上の階数は \(q^w\) である（剰余体が perfect なので、超越次数 \(w\) の体の \(q\) 乗根拡大の次数は \(q^w\)）。

<!-- source: exposition/ja/exposition-ja.tex:1911; block: paper-ja-L1911 -->
<a id="paper-ja-L1911"></a>

\(F^n_*\) は次元 \(h\) の部分を \(q^h\) 倍に、次元 \(w<h\) の部分を \(q^w\) 倍にする。欠陥がより低い次元にあれば、ランク \(q^h\) を単位として測ったときに消えていく。

## 平坦でない場所 \(W\) と、その層別

<!-- source: exposition/ja/exposition-ja.tex:1914; block: paper-ja-L1914 -->
<a id="paper-ja-L1914"></a>

\(D\) は \(A\) 上有限なので、\(A\) 上の有限な自由分解をもつ。\(E^c = \operatorname{Ext}^c_A(D,A)\) とおく。

<!-- source: exposition/ja/exposition-ja.tex:1916; block: paper-ja-L1916 -->
<a id="paper-ja-L1916"></a>

- \(D_\mathfrak{p}\) が \(A_\mathfrak{p}\) 上自由であることと、全ての \(c>0\) で \(E^c_\mathfrak{p} = 0\) であることは同値である。したがって平坦でない場所は \(W = \bigcup_{c>0}\operatorname{Supp}E^c\) で、Auslander–Buchsbaum によりこれは \(D\) が CM でない場所の像である。

<!-- source: exposition/ja/exposition-ja.tex:1917; block: paper-ja-L1917 -->
<a id="paper-ja-L1917"></a>

- \(E^c_\mathfrak{p}\neq0\) なら \(\operatorname{pd}D_\mathfrak{p}\ge c\) で、\(\operatorname{pd}D_\mathfrak{p}\le\operatorname{ht}\mathfrak{p}\) なので \(\operatorname{ht}\mathfrak{p}\ge c\) である。よって \(\dim\operatorname{Supp}E^c\le h-c\)。\(c\) は「平坦でない度合いの次数」で、次数が高いほど小さい場所に住む。

<!-- source: exposition/ja/exposition-ja.tex:1918; block: paper-ja-L1918 -->
<a id="paper-ja-L1918"></a>

- \(D\) は整域なので生成点で平坦であり、\(\dim W<h\) である。\(D\) が \(S_2\)（例えば正規）なら、高さ \(2\) 以下の素イデアルで CM なので、\(\dim W\le h-3\) である。

## 局所コホモロジーとの関係

<!-- source: exposition/ja/exposition-ja.tex:1922–1926; block: paper-ja-L1922 -->
<a id="paper-ja-L1922"></a>

正則な \(A\) 上の局所双対により、\(j<h\) について

\[
H^j_\mathfrak{m}(D)^\vee\cong\operatorname{Ext}_A^{h-j}(D,A) = E^{h-j}
\]

である（\(\mathfrak{m}\)-冪ねじれは \(\mathfrak{m}_A\)-冪ねじれと同じなので、\(H^j_\mathfrak{m}(D) = H^j_{\mathfrak{m}_A}(D)\)）。つまり、\(j<h\) の局所コホモロジーは、次数 \(c = h-j\) の平坦でない部分 \(E^c\) の Matlis 双対である。§C.4 の \(K^j\) は \(E^{h-j}\) のことで、\(\dim K^j\le j\) は上の \(\dim\operatorname{Supp}E^c\le h-c\) と同じ主張である。CM であること（\(H^j_\mathfrak{m}(D) = 0\)、\(j<h\)）と、\(A\) 上自由であること（\(E^c = 0\)、\(c>0\)）が同値であることも、この対応から読める。

## Koszul 複体との関係

<!-- source: exposition/ja/exposition-ja.tex:1929–1937; block: paper-ja-L1929 -->
<a id="paper-ja-L1929"></a>

\(K(t;A)\) は \(k\) の自由分解なので、\(H_i(t;D) = \operatorname{Tor}^A_i(k,D)\) は閉点での平坦性の判定である。Auslander–Buchsbaum により、\(H_i(t;D)\neq0\) となる最大の \(i\) は \(h-\operatorname{depth}D\) で、これは \(0\) でない最小の局所コホモロジー \(H^{\operatorname{depth}D}_\mathfrak{m}(D)\) に対応する。より一般に、有限長加群 \(V\) について \(\operatorname{Tor}_i^A(V,D)^\vee\cong\operatorname{Ext}^i_A(D,V^\vee)\) を \(\mathbf{R}\!\operatorname{Hom}_A(D,A)\otimes^{\mathbf{L}}_A V^\vee\) で計算すると、スペクトル系列

\[
\operatorname{Tor}^A_{c-i}(E^c, V^\vee)\ \Longrightarrow\ \operatorname{Tor}_i^A(V,D)^\vee
\]

が得られる。\(V = A/t^{[q]}\)（Gorenstein なので \(V^\vee\cong V\)）とすると

\[
H_{c-i}(t^{[q]};E^c)\ \Longrightarrow\ H_i(t^{[q]};D)^\vee \qquad (c\ge i)
\]

で、§C.4 のスペクトル系列は、この形で書くと \(W\) の層別と直接つながる。Koszul の次数 \(i\) に寄与するのは \(c\ge i\) の \(E^c\) だけ、すなわち次元 \(h-i\) 以下の場所に住む欠陥だけである。「Koszul の次数が上がるほど、効く欠陥の住む場所が小さくなる」というのが、次数と増大度の対応の正体である。

<!-- source: exposition/ja/exposition-ja.tex:1939; block: paper-ja-L1939 -->
<a id="paper-ja-L1939"></a>

Koszul 複体を深い冪 \(t^{[q]}\) にとることは、局所コホモロジー（\(H^j_\mathfrak{m}(D) = \varinjlim_t H^j(t^t;D)\)、\(H_i(t;D)\cong H^{h-i}(t;D)\)）に近づくことでもある。元論文は局所コホモロジーを表に出さず Koszul 複体で計算しているが、上のスペクトル系列は、Koszul 複体の計算が実質的に「\(E^c\) を箱 \(A/t^{[q]}\) で切り取った量」を数えていることを示している。

## 三つの見方の対応

<!-- source: exposition/ja/exposition-ja.tex:1942–1954; block: paper-ja-L1942 -->
<a id="paper-ja-L1942"></a>

| 見方 | 欠陥を表すもの | \(F^n_*\)（\(D^{1/q}\)）での振る舞い |
| --- | --- | --- |
| Koszul 複体 | \(H_i(t;D) = \operatorname{Tor}^A_i(k,D)\)（\(i\ge1\)） | \(H_i(t^{[q]};D) = \beta_i^A(F^n_*D)\) |
| 平坦でない場所 | \(E^c = \operatorname{Ext}^c_A(D,A)\)（\(c\ge1\)）、台は \(W\)、\(\dim\le h-c\) | 次元の分だけ拡大：おおよそ \(q^{\dim E^c}\) 倍 |
| 局所コホモロジー | \(H^j_\mathfrak{m}(D) = (E^{h-j})^\vee\)（\(j<h\)） | Frobenius 作用で同じく拡大 |
| 対応 | 次数 \(i\) に効くのは \(c\ge i\)、すなわち \(j\le h-i\) | 増大度は目安 \(q^{h-i}\)、正規化すると \(O(q^{-i})\) |

## まとめ

<!-- source: exposition/ja/exposition-ja.tex:1958; block: paper-ja-L1958 -->
<a id="paper-ja-L1958"></a>

1. 平坦なら高次の Koszul ホモロジーは消える。

<!-- source: exposition/ja/exposition-ja.tex:1959; block: paper-ja-L1959 -->
<a id="paper-ja-L1959"></a>

2. \(D\) は平坦ではないが、平坦でない部分 \(E^c\) は低次元の場所 \(W\) にあり、次数 \(c\) が高いほど小さい場所にある。\(E^c\) の双対が局所コホモロジーである。

<!-- source: exposition/ja/exposition-ja.tex:1960; block: paper-ja-L1960 -->
<a id="paper-ja-L1960"></a>

3. \(F^n_*\) は各部分をその次元の分だけ拡大するので、平坦な主要部分（次元 \(h\)）に比べて \(E^c\) は相対的に小さくなる。

<!-- source: exposition/ja/exposition-ja.tex:1961; block: paper-ja-L1961 -->
<a id="paper-ja-L1961"></a>

4. \(F^n_*A\) のランク \(q^h\) を単位として測ると、\(F^n_*D\) はランク \(r\) の自由加群に近づく。Koszul の次数 \(i\) の欠陥は次元 \(h-i\) 以下の部分から来るので、\(O(q^{-i})\) で消える。

<!-- source: exposition/ja/exposition-ja.tex:1963; block: paper-ja-L1963 -->
<a id="paper-ja-L1963"></a>

基底の根だけを足すこと（\(D\otimes_A A^{1/q}\)）では全体が一様に \(q^h\) 倍になるだけで、何も起きない（§C.8）。

## \(W\) は小さくならない

<!-- source: exposition/ja/exposition-ja.tex:1966; block: paper-ja-L1966 -->
<a id="paper-ja-L1966"></a>

冪根をとっても、平坦でない場所 \(W\) そのものは変わらない。

<!-- source: exposition/ja/exposition-ja.tex:1968; block: paper-ja-L1968 -->
<a id="paper-ja-L1968"></a>

- \(D^{1/q}\) は環として \(D\) と同型で、Frobenius は \(\operatorname{Spec}\) の上で同相なので、\(D^{1/q}\) が CM でない場所は \(D\) と同じである。\(F^n_*D\) は \(A\) 上有限なので、Auslander–Buchsbaum により \(A\) 上平坦でない場所も同じ \(W\) である。

<!-- source: exposition/ja/exposition-ja.tex:1969; block: paper-ja-L1969 -->
<a id="paper-ja-L1969"></a>

- 極限の \(D_{\mathrm{perf}}\) も、\(W\) の点では平坦にならない。\(\lambda\)-平坦は本当の平坦ではない（\(\lambda\) で \(0\) でも群として \(0\) ではない、と同じこと）。

<!-- source: exposition/ja/exposition-ja.tex:1971; block: paper-ja-L1971 -->
<a id="paper-ja-L1971"></a>

変わるのは場所ではなく相対的な大きさだけである。平坦な主要部分は \(q^h\) 倍、\(W\) の上の欠陥は \(q^{\dim W}\) 倍程度にしかならないので、ランク \(q^h\) を単位として測ると欠陥の割合が \(0\) に近づく。測度論で言えば、正方形の中の曲線は空でなくても面積 \(0\) である、という状況に近い。\(\lambda\) は「次元 \(h\) の大きさ」を測る量で、Frobenius の塔はその測り方を有限段で近似している。

## 確かめていないこと

<!-- source: exposition/ja/exposition-ja.tex:1975; block: paper-ja-L1975 -->
<a id="paper-ja-L1975"></a>

- 「\(F^n_*\) が次元 \(w\) の部分をおおよそ \(q^w\) 倍にする」ことを、高次の Tor（Betti 数）について正確な評価にすること。\(0\) 次（生成元数）は Hilbert–Samuel から出るが、高次は §C.4 のステップ 2 と同じ問題である。

<!-- source: exposition/ja/exposition-ja.tex:1976; block: paper-ja-L1976 -->
<a id="paper-ja-L1976"></a>

- スペクトル系列の添字の正確な形（CM の場合と一般化 CM の場合で整合することは確認した）。

<!-- source: exposition/ja/exposition-ja.tex:1977; block: paper-ja-L1977 -->
<a id="paper-ja-L1977"></a>

- 混標数で perfectoid 化が \(p\) を法として \(F_*\) の役をする（tilt）とき、同じ描像がどこまで成り立つか。

## 解説 §C.6 定理 2.5 の証明との対応

<!-- source: exposition/ja/exposition-ja.tex:1982; block: paper-ja-L1982 -->
<a id="paper-ja-L1982"></a>

ここまでの直感的な議論は、元論文 Theorem 2.5（定理 8.5）の標数 \(p\) の場合の証明に当たる。証明の各ステップと対応を並べる。設定は次のとおり。基底は Lemma 2.2 の \(A = k[[t_1,\dots,t_h]]\subseteq D\)（有限、生成的に分離的、剰余体は同じ）、塔は \(A_n = A^{1/q}\)、\(\Lambda = \varinjlim A_n\)。長さは Lemma 2.3 の \(\lambda_\infty\) で、有限段の \(A_n\) 加群 \(V_n\) について \(\lambda_\infty(V_n\otimes\Lambda) = p^{-nh}\,\ell_{A_n}(V_n)\)（(2.2)）。\(p^{nh}\) は \(A_n\) の \(A\) 上の階数である。

<!-- source: exposition/ja/exposition-ja.tex:1984–1999; block: paper-ja-L1984 -->
<a id="paper-ja-L1984"></a>

|  | 証明のステップ | 直感的な議論との対応 |
| --- | --- | --- |
| (1) | \(C_D = D_{\mathrm{perf}}\)。\(B_q = \Lambda\otimes_{A^{1/q}}D^{1/q}\) は \(C_D\) に入り（生成的分離性による線形無関性）、\(q\) とともに増えて \(C_D\) に至る | 「全ての元の根」は \(D^{1/q}\) の部分。\(B_q\) は \((A^{1/q}\subset D^{1/q})\cong(A\subset D)\) を \(\Lambda\) へ平坦に基底変換したもので、「基底の根」は測るための土台としてだけ入る |
| (2) | 有限段の公式 \(\lambda_\infty(B_q/HB_q) = q^{-h}\,\ell_D(D/H^{[q]})\) | ランク \(q^h\) を単位にする（(2.2) の \(p^{-nh}\)）。Frobenius 同型 \(D^{1/q}\cong D\) で、固定した \(H\) が \(H^{[q]}\)（深い冪）に移る |
| (3) | トレースの分母 \(g\)（\(A[1/g]\to D[1/g]\) が有限エタール）による制御 (2.7)：\(g^{1/q}C_D\subseteq B_q\)。\(B_q/H\to C_D/H\) の核は \(g^{1/q}\) で消され、\(\lambda\le q^{-h}\ell(D/(H^{[q]},g)) = O(q^{-1})\) | 分岐から来る誤差。\(V(g)\)（次元 \(h-1\)）に住むので \(q^{h-1}\) でしか増えない。「\(F_*\) は次元の分だけ拡大する」原理が論文中で明示的に（Hilbert–Samuel として）使われている箇所。\(W\subseteq V(g)\)（エタールなら平坦） |
| (4) | Hilbert–Kunz の極限と Lemma 2.4 から (2.8)：\(\lambda(C_D/HC_D) = e_{\mathrm{HK}}(H,D)\) | \(0\) 次の主要項（\(\beta_0/q^h\) の極限） |
| (5) | パラメータ系 \(z\) について \(\lambda_\infty H_i(z;B_q) = q^{-h}\ell_D H_i(z^{[q]};D)\)。Roberts により \(i>0\) で \(0\) に近づく | CM でないことから来る誤差。高次 Koszul \(=\) 高次 Betti 数で、\(W\) 上の \(E^c\) から来る（§C.5）。論文は \(o(q^h)\) だけを使い、次数ごとの速さ、\(W\)、局所コホモロジーは表に出さない |
| (6) | \(H_i(z;C_D) = \varinjlim H_i(z;B_q)\)。共通の消去イデアル \((z)\) があるので、Lemma 2.4（\(\lambda(V_a)\to0\) なら余極限の \(\lambda\) は \(0\)。単射性は不要）から (2.4) | 「\(W\) は消えないが \(\lambda\) では \(0\)」の正確な形。有限段で比が \(0\) に近づくことを、極限での \(\lambda = 0\) に変える |
| (7) | Koszul の Euler 特性 \(\sum(-1)^i\ell H_i(z^{[q]};D) = q^h e\) と (2.8) から (2.5)。\(e((t),D) = \operatorname{rank}_A D\) から (2.6) | \(F^n_*D\) が「ランク \(r q^h\) の自由加群」に近づくことの \(r\) の部分 |

## 読み取れること

<!-- source: exposition/ja/exposition-ja.tex:2003; block: paper-ja-L2003 -->
<a id="paper-ja-L2003"></a>

1. 誤差は二種類あり、どちらも有限段で数えている。分岐から来る誤差（ステップ (3)）は \(V(g)\) の次元による \(O(q^{-1})\) で、論文に明示されている。CM でないことから来る誤差（ステップ (5)）は Roberts の \(o(q^h)\) に任されている。

<!-- source: exposition/ja/exposition-ja.tex:2004; block: paper-ja-L2004 -->
<a id="paper-ja-L2004"></a>

2. トレースの制御が要るのは \(0\) 次だけである。一般の \(H\) で \(\lambda(C_D/HC_D)\) の値を正確に出すには、有限段から極限への写像の核を抑える必要がある。高次は \(0\) になることだけ言えばよいので、Lemma 2.4 により単射性なしで済む。

<!-- source: exposition/ja/exposition-ja.tex:2005; block: paper-ja-L2005 -->
<a id="paper-ja-L2005"></a>

3. \(W\)、\(E^c\)、局所コホモロジー、次数ごとの速さは論文に出てこない。これらは Roberts の定理の中身を開いたときの描像で、論文の証明はそれらを使わずに完結している。

<!-- source: exposition/ja/exposition-ja.tex:2007; block: paper-ja-L2007 -->
<a id="paper-ja-L2007"></a>

混標数では、論文はステップ (1)–(7) を CLMST の Cor. 4.0.4、Prop. 4.0.10、4.0.14 でまとめて置き換えている（定理 8.5）。

## 解説 §C.7 見方 3：混標数では分岐が薄まる（almost purity）

<!-- source: exposition/ja/exposition-ja.tex:2011; block: paper-ja-L2011 -->
<a id="paper-ja-L2011"></a>

混標数には Frobenius がないので、見方 2 の代わりに次の仕組みが働く。

<!-- source: exposition/ja/exposition-ja.tex:2013; block: paper-ja-L2013 -->
<a id="paper-ja-L2013"></a>

- \(A[1/g]\to D[1/g]\) が有限エタールとなる \(g\neq0\) をとる。\(g\) の外では \(D\) は \(A\) 上平坦であり、平坦でない部分は分岐の場所 \(V(g)\) に集中している。

<!-- source: exposition/ja/exposition-ja.tex:2014; block: paper-ja-L2014 -->
<a id="paper-ja-L2014"></a>

- パラメータの \(p\) 冪根をすべて添加した塔 \(A_\infty\) への基底変換 \(D\otimes_A A_\infty\) は平坦なので、それだけでは平坦でない度合いは変わらない。効くのはその後の perfectoid 化で、これは \(D/p\) 上の Frobenius を全射にする操作、つまり「\(D\) のすべての元の、\(p\) を法とした \(p\) 乗根を足す」ことに当たる。これによって分岐は \(g^{1/p^n}\) 程度にまで薄まる（almost purity）。原型は、\(\mathbb{Q}_p\) に \(p\) の冪根を添加していくと分岐がほぼ消える、という Tate の現象である。

<!-- source: exposition/ja/exposition-ja.tex:2015; block: paper-ja-L2015 -->
<a id="paper-ja-L2015"></a>

- その結果、平坦でない部分は「任意の \(n\) について \(g^{1/p^n}\) で消える」大きさに押し込められる。これが almost zero である（CLMST Cor. 4.0.4）。群としては残りうるが、体積を測る \(\lambda\) では \(0\) になる（CLMST Prop. 4.0.10）。

## 解説 §C.8 冪根の次数が剰余標数と一致することの意味

<!-- source: exposition/ja/exposition-ja.tex:2020; block: paper-ja-L2020 -->
<a id="paper-ja-L2020"></a>

見方 2、3 で添加する冪根の次数は、剰余標数 \(p\) と一致していなければならない。理由を以下に述べる。

## トレースによる分裂

<!-- source: exposition/ja/exposition-ja.tex:2023; block: paper-ja-L2023 -->
<a id="paper-ja-L2023"></a>

\(D\) を正規整域、\(D'\) をその次数 \(d\) の有限拡大とする。\(d\) が \(D\) で可逆なら、\((1/d)\operatorname{Tr}\colon D'\to D\) は \(D\) 線形な分裂を与えるので、\(H^i_\mathfrak{m}(D)\) は \(H^i_\mathfrak{m}(D')\) の直和因子になる。したがって、次数が \(p\) と素な拡大では、CM でない欠陥は群として必ず残る。

<!-- source: exposition/ja/exposition-ja.tex:2025; block: paper-ja-L2025 -->
<a id="paper-ja-L2025"></a>

- 剰余標数 \(0\) では全ての有限拡大がこれに当たる。このため \(R^+\) は（次元 \(3\) 以上で）CM にならない。

<!-- source: exposition/ja/exposition-ja.tex:2026; block: paper-ja-L2026 -->
<a id="paper-ja-L2026"></a>

- 欠陥を群として消せる可能性があるのは、次数が \(p\) で割り切れる拡大だけである。Bhatt による \(R^+\) の CM 性や perfectoid 化の almost CM 性は、この分裂が壊れることを利用している。

## 平坦な基底変換は正規化した欠陥を変えない

<!-- source: exposition/ja/exposition-ja.tex:2030; block: paper-ja-L2030 -->
<a id="paper-ja-L2030"></a>

\(\lambda\) で測る場合も、\(p\) と素な冪根は役に立たない。\(\ell\neq p\) とし、\(A_n = A[t^{1/\ell^n}]\) とおくと、\(A_n\) は \(A\) 上自由で、\(D\otimes_A A_n\) は \(D\) の平坦な基底変換である。\(A_n\) 上で平坦でない度合いは \(D\) と同じで、Koszul ホモロジーの長さもランクも同じ割合 \(\ell^{nh}\) 倍になるので、正規化した欠陥は減らない。同じことは \(p\) 冪根でも、基底 \(A\) のパラメータに根を足すだけなら成り立つ。

## すべての元の根をとれるのは \(p\) のときだけ

<!-- source: exposition/ja/exposition-ja.tex:2033; block: paper-ja-L2033 -->
<a id="paper-ja-L2033"></a>

効いているのは \(D\) のすべての元の根をとる操作である。

<!-- source: exposition/ja/exposition-ja.tex:2035; block: paper-ja-L2035 -->
<a id="paper-ja-L2035"></a>

- 標数 \(p\) では \(D^{1/q}\) がそれに当たり、\(D\otimes_A A^{1/q}\to D^{1/q}\)（相対 Frobenius）は基底変換ではない。環として \(D^{1/q}\cong D\) なので、Koszul ホモロジーは \(H_i(z^{[q]};D)\) になり、Roberts の定理が使える。

<!-- source: exposition/ja/exposition-ja.tex:2036; block: paper-ja-L2036 -->
<a id="paper-ja-L2036"></a>

- これは \(x\mapsto x^p\) が環準同型であることによる。\(x\mapsto x^\ell\)（\(\ell\neq p\)）は加法的でないので、すべての元の \(\ell\) 乗根を添加するとランクを制御できない巨大な環になる。

<!-- source: exposition/ja/exposition-ja.tex:2037; block: paper-ja-L2037 -->
<a id="paper-ja-L2037"></a>

- 混標数でも、perfectoid 化は \(D/p\) 上の Frobenius を全射にする操作で、\(x\mapsto x^p\) が環準同型になるのは \(p\) を法としたときだけである。したがって \(p\) は剰余標数でなければならない。塔 \(A_\infty\) でも、\(t_1 = p\) そのものの冪根 \(p^{1/p^n}\) を添加している。

## 分岐の言葉で

<!-- source: exposition/ja/exposition-ja.tex:2041; block: paper-ja-L2041 -->
<a id="paper-ja-L2041"></a>

馴分岐（\(p\) と素な部分）は、\(\ell\) 冪根を添加すれば Abhyankar の補題で厳密に消える。しかしそのとき起きているのは平坦な基底変換で、CM でない欠陥には効かない。野生分岐（\(p\) の部分）は \(p\) 冪根を添加しても厳密には消えず、almost にしか消えない（Tate、Faltings）。それでも、欠陥を \(\lambda\) で見えなくする仕組みはこれしかない。剰余標数 \(0\) の場合を直接示せず、正標数に帰着するしかないのも同じ理由による（Lech の論文 §7 の帰着はその例である）。

## 解説 §C.9 まとめと、他の構成との関係

<!-- source: exposition/ja/exposition-ja.tex:2045; block: paper-ja-L2045 -->
<a id="paper-ja-L2045"></a>

元の \(D\) で高次の項が生きているのは、\(D\) が正則な基底の上で平坦でないからである。その欠陥は低次元の場所や分岐の場所に集中している。基底に冪根を足す（平坦な基底変換）だけではこの欠陥は変わらないが、Frobenius や perfectoid 化で \(D\) のすべての元の \(p\) 乗根をとると、主要項だけが大きくなり、体積で正規化すれば欠陥は見えなくなる。標数 \(p\) では見方 2（増大度）が、混標数では見方 3（分岐の希釈）が、同じ結論を与える。

<!-- source: exposition/ja/exposition-ja.tex:2047; block: paper-ja-L2047 -->
<a id="paper-ja-L2047"></a>

この説明からわかるように、perfectoid 化が担っているのは次の二つを同時に満たすことである。

<!-- source: exposition/ja/exposition-ja.tex:2049; block: paper-ja-L2049 -->
<a id="paper-ja-L2049"></a>

- **CM 性**：欠陥を \(\lambda\) で見えなくする（見方 3）。

<!-- source: exposition/ja/exposition-ja.tex:2050; block: paper-ja-L2050 -->
<a id="paper-ja-L2050"></a>

- **大きさの有限性**：\(C\) は \(A_\infty\) 上でほぼランク \(r\) なので、\(\lambda(C/zC) = e\) が有限である。\(R^+\) のような本物の巨大 CM 代数は \(A_\infty\) 上で無限ランクなので、\(\lambda(R^+/zR^+)\) が無限大になり、そのままでは使えない。

<!-- source: exposition/ja/exposition-ja.tex:2052; block: paper-ja-L2052 -->
<a id="paper-ja-L2052"></a>

原理的には、この二つを満たす長さ付き代数なら perfectoid である必要はない。\(D\)、\(E\) が小さな CM 加群をもてば、型 (i) の議論（Hochster）で済み、K 理論の降下は不要になる。しかし一般の \(D\) について混標数でこれを供給する方法は、現在のところ perfectoid 化しか知られていないと思われる。perfectoid 化は常に存在する（Bhatt–Scholze）が、\(R\) 上有限ではない。元論文の後半（K 理論の降下、Galois 閉包、ランク無視の圏、有限近似）は、この「有限でない」ことの帰結である。

## 解説 §C.10 精密化すべき点

<!-- source: exposition/ja/exposition-ja.tex:2056; block: paper-ja-L2056 -->
<a id="paper-ja-L2056"></a>

- 見方 1 は \(A\) のパラメータ系についての説明である。\(\lambda\)-CM（定義 4.14）は \(D\) の任意のパラメータ系を要求する。\(A\) 上の（almost）平坦性から \(D\) の任意のパラメータ系の消滅が出る仕組みを確認する（CLMST Cor. 4.0.4 は \(A_n\otimes_A D\) の任意のパラメータ系を扱う）。

<!-- source: exposition/ja/exposition-ja.tex:2057; block: paper-ja-L2057 -->
<a id="paper-ja-L2057"></a>

- 見方 2 の例で \(\ell H_1(z^{[q]};D)\) が有界であることを計算で確かめる。一般化 CM 環での評価の正確な形を文献で確認する。

<!-- source: exposition/ja/exposition-ja.tex:2058; block: paper-ja-L2058 -->
<a id="paper-ja-L2058"></a>

- 標数 \(p\) で、\(H_i(z;D_{\mathrm{perf}})\)（\(i>0\)）が群として \(0\) でない例があるか。almost zero になるか（混標数と同じ形か）を確認する。

<!-- source: exposition/ja/exposition-ja.tex:2059; block: paper-ja-L2059 -->
<a id="paper-ja-L2059"></a>

- 見方 3 の almost purity の正確な主張（どの塔の上で、どのイデアルについて almost か）と、CLMST Thm. 4.0.3 の証明の中での使われ方を確認する。Tate の例は比喩として正確な形に直す。

<!-- source: exposition/ja/exposition-ja.tex:2060; block: paper-ja-L2060 -->
<a id="paper-ja-L2060"></a>

- §C.8 のトレースによる分裂の議論は群としての消滅についてのもので、正規化した欠陥については平坦な基底変換の議論しかしていない。\(p\) と素な次数の、基底変換でない有限拡大の列で正規化した欠陥が \(0\) に近づかないことは確かめていない。Abhyankar の補題の適用（どの環で、どの分岐因子について）も正確な形にする。

<!-- source: exposition/ja/exposition-ja.tex:2061; block: paper-ja-L2061 -->
<a id="paper-ja-L2061"></a>

- 「混標数で一般の \(D\) に \(\lambda\)-CM 代数を供給する方法は perfectoid 化しかない」という主張は、文献調査に基づくものではない。

<!-- source: exposition/ja/exposition-ja.tex:2062; block: paper-ja-L2062 -->
<a id="paper-ja-L2062"></a>

- §C.4 の目安 \(\ell H_i(z^{[q]};D) = O(q^{h-i})\) は確かめていない。\(H_i(z^t;D)\) と \(H^{h-i}_\mathfrak{m}(D)\) の関係（推移写像の像と核）を正確に追い、文献（Frobenius 関手と有限長ホモロジーの複体の増大度の評価）を確認する。混標数の perfectoid 化について、次数ごとの描像に当たるものがあるかも確認する。
