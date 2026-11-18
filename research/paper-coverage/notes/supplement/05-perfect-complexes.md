# perfect 複体での評価（解説 §5 の補足）

<!-- NB-W4: 凍結解説から転記。 -->

## 解説 §5.1 設定と評価関手

## 設定

<!-- source: exposition/ja/exposition-ja.tex:636; block: paper-ja-L636 -->
<a id="paper-ja-L636"></a>

**Lean:** 評価元は `SupportedPerfectHomotopy`、評価は `LengthAlgebra.perfectEulerK0`。局所環上で `K0Supported` と同型になり、`chiOrdHom`・`chiLamHom_of_finite` との一致は `LengthAlgebra.EulerCompatibility`。

## 解説 §5.3 消滅と下界：補題 3.11、3.12 の適用

<!-- source: exposition/ja/exposition-ja.tex:782; block: paper-ja-L782 -->
<a id="paper-ja-L782"></a>

ここでは、補題 3.11 の仮定（台の条件と Koszul 振幅の条件）と、補題 3.12 の全射を perfect 複体について確かめ、補題 5.10、5.11 を得る。\(z\) に台をもつことは、ホモロジーの幾何学的な台の条件と補題 5.1 から、Koszul 振幅の条件は次の段落の項によるフィルトレーションから、全射は極小性から出る。

<!-- source: exposition/ja/exposition-ja.tex:784; block: paper-ja-L784 -->
<a id="paper-ja-L784"></a>

\(P\) が \(0\) 次から \(m\) 次に有限射影項をもつなら、\(K_v\otimes P\otimes C\) の項によるフィルトレーションの各段は、\(K(z^v;C)\) の有限直和のシフトの直和因子である。正次数の Koszul ホモロジーが商で零であれば、各段はその項の次数だけに集中し、長完全列から Koszul 振幅の条件が出る。台の条件は台の条件と補題 5.1 から出るので、補題 3.11 が使える。

<!-- source: exposition/ja/exposition-ja.tex:786–790; block: paper-ja-L786 -->
<a id="paper-ja-L786"></a>

一方、\(S=T\) が局所環で \(P\) の \(0\) 次の項が \(T^{\oplus\beta_0}\)、\(d_1\) の成分が \(\mathfrak{m}_T\) に入れば

\[
H_0(P\otimes C)\twoheadrightarrow(C/\mathfrak{m}_T C)^{\oplus\beta_0}.
\]

この全射と長さの単調性は \(\lambda\)-平坦性を使わない。\(\lambda\)-平坦性による高次の消滅と組み合わせて初めて、\(m=e\) のとき Euler 評価の下界になる。

## 補題 5.10（新交叉型の消滅）

<!-- source: exposition/ja/exposition-ja.tex:793–797; block: paper-ja-L793 -->
<a id="paper-ja-L793"></a>

\(e\) を列 \(z\) の長さとし、全ての \(v\ge1\) と \(j>0\) で \(\lambda H_j(z^v;C)=0\) とする。\(P\in\mathcal{K}_T\) が \(0\) 次から \(m\) 次に有限射影な項をもつ複体で表されるなら、

\[
\lambda H_i(P\otimes_T C) = 0 \qquad (i > m - e).
\]

特に \(m = e\) なら \(\chi_C(P) = \lambda H_0(P\otimes_T C)\)。

## 証明

<!-- source: exposition/ja/exposition-ja.tex:800; block: paper-ja-L800 -->
<a id="paper-ja-L800"></a>

台から \(z_j^v\) の零ホモトピーを選び、台の条件を得る。\(P\) の項によるフィルトレーションの各段は \(K(z^v;C)\) の有限直和のシフトである。正次数の Koszul ホモロジーの長さは零なので、評価先では各段のホモロジーはその項の次数に集中する。長完全列から \(H_n^C(K_v\otimes P)=0\)（\(n\notin[0,m]\)）、すなわち Koszul 振幅の条件が従う。あとは共通の補題 3.11 により零対象としての消滅を得て、その長さをとればよい。

<!-- source: exposition/ja/exposition-ja.tex:802; block: paper-ja-L802 -->
<a id="paper-ja-L802"></a>

\(A\) が正則局所環、\(z\) が正則パラメータ系で \((C,\lambda)\) が \(\lambda\)-平坦なら、\(e=\dim A\) で、Koszul ホモロジーの仮定は系 4.11 から出る。この補題は §5.5 で \((A,z,T)=(R,x,R)\) として使う。そこでは列の長さ \(e=h\) と \(\dim R\) が異なるので、\(e\) を列の長さとして述べておく。

<!-- source: exposition/ja/exposition-ja.tex:804; block: paper-ja-L804 -->
<a id="paper-ja-L804"></a>

古典的には、\(B\) を巨大 CM 代数、\(F\) を長さ \(m\) で有限長ホモロジーの有限自由複体とすると、同じ議論で \(H_i(F\otimes B) = 0\)（\(i>m-e\)）となる。\(m = e\) で \(\mathfrak{m} B\ne B\) と合わせると、Hochster による新交叉定理の証明になる（cf. Iyengar–Ma–Schwede–Walker, *Maximal Cohen–Macaulay complexes and their uses*, Thm. 2.4 とその前後）。

<!-- source: exposition/ja/exposition-ja.tex:805; block: paper-ja-L805 -->
<a id="paper-ja-L805"></a>

**Lean:** `LengthAlgebra.PerfectVanishing` の `lambdaHomology_projective_vanishing`（Koszul 消滅を入力として\(e\) は列の長さで、有限射影項でも成立し、消滅自体は Koszul 有限性を使わない）。

## 補題 5.11（\(0\) 次の下界）

<!-- source: exposition/ja/exposition-ja.tex:808–811; block: paper-ja-L808 -->
<a id="paper-ja-L808"></a>

補題 5.10 の \(P\) の \(0\) 次の項を \(T^{\oplus\beta_0}\) とし、\(P\) が \(1\) 次で極小（\(d_1\) の成分が \(\mathfrak{m}_T\) に入る）とする。このとき

\[
\lambda H_0(P\otimes_T C) \;\ge\; \beta_0\cdot\lambda(C/\mathfrak{m}_T C).
\]

## 証明

<!-- source: exposition/ja/exposition-ja.tex:814; block: paper-ja-L814 -->
<a id="paper-ja-L814"></a>

\(H_0(P\otimes C) = C^{\oplus\beta_0}/\operatorname{im}(d_1\otimes C)\) は極小性により \((C/\mathfrak{m}_T C)^{\oplus\beta_0}\) に全射する。

<!-- source: exposition/ja/exposition-ja.tex:816; block: paper-ja-L816 -->
<a id="paper-ja-L816"></a>

**Lean:** `LengthAlgebra.PerfectMinimalLowerBound`（極小性から全射を構成し、共通下界を適用）。

<!-- source: exposition/ja/exposition-ja.tex:818; block: paper-ja-L818 -->
<a id="paper-ja-L818"></a>

普通の評価についても準同型と共役和の比較はあるが、この消滅の入力は一般には満たさない。

## 解説 §5.4 \(\lambda\)-平坦な代数での適用

## 系 5.12（\(\lambda\)-平坦な代数での比較・消滅・下界）

<!-- source: exposition/ja/exposition-ja.tex:827; block: paper-ja-L827 -->
<a id="paper-ja-L827"></a>

- (c) **消滅と下界**：補題 5.10、5.11 が成り立つ。

## 証明

<!-- source: exposition/ja/exposition-ja.tex:831; block: paper-ja-L831 -->
<a id="paper-ja-L831"></a>

系 4.11 により Koszul 有限性、正次数の Koszul ホモロジーの長さ零、\(e_\lambda(z;C)=r\) が得られる。(a) は命題 5.8、(b) は定理 5.9、(c) は補題 5.10、5.11 にこれらを入れたものである。

<!-- source: exposition/ja/exposition-ja.tex:833; block: paper-ja-L833 -->
<a id="paper-ja-L833"></a>

\(\lambda\)-CM 代数についても、命題 4.15 を通して同じである。

<!-- source: exposition/ja/exposition-ja.tex:834; block: paper-ja-L834 -->
<a id="paper-ja-L834"></a>

**Lean:** `LengthAlgebra.FlatRealization` の `perfectEuler_conjSum_eq_of_flat`、`lambdaHomology_projective_vanishing_of_flat`、`perfectEuler_minimal_lower_bound_of_flat`（基底の Koszul 分解と降下を明示した形）。
