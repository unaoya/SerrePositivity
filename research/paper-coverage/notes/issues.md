# 本論文の原稿の所見と保留本文

## TeX から Markdown への変換

- **番号の二系統。** たとえば原典 Theorem 3.1 の原稿に入るのは解説の定理 7.3。ファイル名は原典の番号、見出しと参照の表示は解説の番号。式は原典の目録どおり括弧つきのファイル名とした。解説で番号が付いている表示式は解説内の番号を式に残した。
- **行送りと数式。** インライン・独立式を `\( \)`・`\[ \]` に統一し、局所マクロ `\Tor`・`\m`・`\Q` などだけ定義通りに展開した。たとえば解説の反復錐の分裂と第二比較は、それぞれ独立式を含む一つの本文ブロックである。生成時に TeX のバックスラッシュを通常文と同じ方法でエスケープすると式が壊れる。
- **表・箇条書き。** 解説 §7 冒頭など6個の `tabularx` は列見出しごと Markdown に移し、配置指定を外した。列内の式と表示された参照を保持した。原稿が分かれた箇条書きは解説での (a)・(b) 等を各項に明示した。表、リストとその追跡用アンカーが Verso でどう表示されるかは静的照合の範囲外。
- **参照と実装注記。** `\ref`・`\eqref` は凍結 TeX の連番から表示文言へ展開した。例として原典 4.6 に置いた解説の補題 7.7 を指す参照は「補題 7.7」と表示する。付録など転記範囲外への参照にも表示文言を残した。元の `\lean` の文は「Lean:」の注記として保存し、`\ld` の名前は変えずバッククォートで囲んだ。注記に書かれた実装状態は原稿の一部で、現在の対応状態は review を参照する。
- **複数項目にまたがる説明。** 解説 9.3 のパラメータ商では、選択の主張を `(5.4).md`、長さ・消去冪を `(5.5).md`・`(5.6).md` に分けた。仮定・式・直後の指示語が一文をなすときは段落をまとめて残した。

## 保留本文

元の段落を全文保存し、変換後の本文の直前に保留理由を置いた。

## 解説 §4.1 長さ関数と長さ付き代数

## 例 4.2

<!-- source: exposition/ja/exposition-ja.tex:421; block: paper-ja-L421 -->
<a id="paper-ja-L421"></a>

**保留理由**　通常長の定義名と実装名の対比、および付録への案内。特定の論文項目の説明先が定まらない。

**Lean:** `NormalizedLength`（`PerfectComplex.NormalizedLength`）、普通の長さは `NormalizedLength.ordinary`（\(J = \bot\)）。Lean の名前は元論文に合わせて「正規化長さ」のまま（付録 A.4）。

## 定義 4.3（長さ付き代数）

<!-- source: exposition/ja/exposition-ja.tex:424; block: paper-ja-L424 -->
<a id="paper-ja-L424"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

\(A\) を可換環、\(z=(z_1,\dots,z_e)\) をその元の有限列とし、\(z^v=(z_1^v,\dots,z_e^v)\) と書く。**長さ付き \(A\) 代数**とは、可換 \(A\) 代数 \(C\) と、\(J=(z)C\) のある冪で加群全体が消される \(C\) 加群の上の長さ関数 \(\lambda\) の組 \((C,\lambda)\) のことである。

<!-- source: exposition/ja/exposition-ja.tex:426; block: paper-ja-L426 -->
<a id="paper-ja-L426"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

\(A\) がネーター局所環で \(\sqrt{(z)}=\mathfrak{m}_A\) なら、\((z)C\)-冪ねじれと \(\mathfrak{m}_A C\)-冪ねじれは同じ条件である。実際、\(\mathfrak{m}_A\) のある冪が \((z)\) に入り、この包含を \(C\) に移せばよい。§4.2 と定義 4.8 では \(A\) のネーター性は仮定せず、有限列 \(z\) を固定して使う。

## 解説 §4.2 評価先：長さ付きアーベル圏の構成

## 命題 4.7（有限な商と大きな商の有限部分）

<!-- source: exposition/ja/exposition-ja.tex:474; block: paper-ja-L474 -->
<a id="paper-ja-L474"></a>

**保留理由**　有限な Serre 商を使う実装の対応。原典の単一項目に対応する記述として分離できない。

**Lean:** `LengthAlgebra.FiniteQuotientEquivalence` の `finiteQuotientEquivalence`。ホモロジー、零対象、Euler 数と \(K_0\) 評価への接続は `PerfectHomologyComparison`（証明済み）。

## 解説 §5.1 設定と評価関手

## 設定

<!-- source: exposition/ja/exposition-ja.tex:636; block: paper-ja-L636 -->
<a id="paper-ja-L636"></a>

**保留理由**　二つの実装入口をまとめて説明しており、特定の定理・式に割り振れない。

**Lean:** 評価元は `SupportedPerfectHomotopy`、評価は `LengthAlgebra.perfectEulerK0`。局所環上で `K0Supported` と同型になり、`chiOrdHom`・`chiLamHom_of_finite` との一致は `LengthAlgebra.EulerCompatibility`。

## 解説 §5.3 消滅と下界：補題 3.11、3.12 の適用

<!-- source: exposition/ja/exposition-ja.tex:782; block: paper-ja-L782 -->
<a id="paper-ja-L782"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

ここでは、補題 3.11 の仮定（台の条件と Koszul 振幅の条件）と、補題 3.12 の全射を perfect 複体について確かめ、補題 5.10、5.11 を得る。\(z\) に台をもつことは、ホモロジーの幾何学的な台の条件と補題 5.1 から、Koszul 振幅の条件は次の段落の項によるフィルトレーションから、全射は極小性から出る。

<!-- source: exposition/ja/exposition-ja.tex:784; block: paper-ja-L784 -->
<a id="paper-ja-L784"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

\(P\) が \(0\) 次から \(m\) 次に有限射影項をもつなら、\(K_v\otimes P\otimes C\) の項によるフィルトレーションの各段は、\(K(z^v;C)\) の有限直和のシフトの直和因子である。正次数の Koszul ホモロジーが商で零であれば、各段はその項の次数だけに集中し、長完全列から Koszul 振幅の条件が出る。台の条件は台の条件と補題 5.1 から出るので、補題 3.11 が使える。

<!-- source: exposition/ja/exposition-ja.tex:786–790; block: paper-ja-L786 -->
<a id="paper-ja-L786"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

一方、\(S=T\) が局所環で \(P\) の \(0\) 次の項が \(T^{\oplus\beta_0}\)、\(d_1\) の成分が \(\mathfrak{m}_T\) に入れば

\[
H_0(P\otimes C)\twoheadrightarrow(C/\mathfrak{m}_T C)^{\oplus\beta_0}.
\]

この全射と長さの単調性は \(\lambda\)-平坦性を使わない。\(\lambda\)-平坦性による高次の消滅と組み合わせて初めて、\(m=e\) のとき Euler 評価の下界になる。

## 補題 5.10（新交叉型の消滅）

<!-- source: exposition/ja/exposition-ja.tex:793–797; block: paper-ja-L793 -->
<a id="paper-ja-L793"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

\(e\) を列 \(z\) の長さとし、全ての \(v\ge1\) と \(j>0\) で \(\lambda H_j(z^v;C)=0\) とする。\(P\in\mathcal{K}_T\) が \(0\) 次から \(m\) 次に有限射影な項をもつ複体で表されるなら、

\[
\lambda H_i(P\otimes_T C) = 0 \qquad (i > m - e).
\]

特に \(m = e\) なら \(\chi_C(P) = \lambda H_0(P\otimes_T C)\)。

## 証明

<!-- source: exposition/ja/exposition-ja.tex:800; block: paper-ja-L800 -->
<a id="paper-ja-L800"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

台から \(z_j^v\) の零ホモトピーを選び、台の条件を得る。\(P\) の項によるフィルトレーションの各段は \(K(z^v;C)\) の有限直和のシフトである。正次数の Koszul ホモロジーの長さは零なので、評価先では各段のホモロジーはその項の次数に集中する。長完全列から \(H_n^C(K_v\otimes P)=0\)（\(n\notin[0,m]\)）、すなわち Koszul 振幅の条件が従う。あとは共通の補題 3.11 により零対象としての消滅を得て、その長さをとればよい。

<!-- source: exposition/ja/exposition-ja.tex:802; block: paper-ja-L802 -->
<a id="paper-ja-L802"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

\(A\) が正則局所環、\(z\) が正則パラメータ系で \((C,\lambda)\) が \(\lambda\)-平坦なら、\(e=\dim A\) で、Koszul ホモロジーの仮定は系 4.11 から出る。この補題は §5.5 で \((A,z,T)=(R,x,R)\) として使う。そこでは列の長さ \(e=h\) と \(\dim R\) が異なるので、\(e\) を列の長さとして述べておく。

<!-- source: exposition/ja/exposition-ja.tex:804; block: paper-ja-L804 -->
<a id="paper-ja-L804"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

古典的には、\(B\) を巨大 CM 代数、\(F\) を長さ \(m\) で有限長ホモロジーの有限自由複体とすると、同じ議論で \(H_i(F\otimes B) = 0\)（\(i>m-e\)）となる。\(m = e\) で \(\mathfrak{m} B\ne B\) と合わせると、Hochster による新交叉定理の証明になる（cf. Iyengar–Ma–Schwede–Walker, *Maximal Cohen–Macaulay complexes and their uses*, Thm. 2.4 とその前後）。

<!-- source: exposition/ja/exposition-ja.tex:805; block: paper-ja-L805 -->
<a id="paper-ja-L805"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

**Lean:** `LengthAlgebra.PerfectVanishing` の `lambdaHomology_projective_vanishing`（Koszul 消滅を入力として証明済み。\(e\) は列の長さで、有限射影項でも成立し、消滅自体は Koszul 有限性を使わない）。

## 補題 5.11（\(0\) 次の下界）

<!-- source: exposition/ja/exposition-ja.tex:808–811; block: paper-ja-L808 -->
<a id="paper-ja-L808"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

補題 5.10 の \(P\) の \(0\) 次の項を \(T^{\oplus\beta_0}\) とし、\(P\) が \(1\) 次で極小（\(d_1\) の成分が \(\mathfrak{m}_T\) に入る）とする。このとき

\[
\lambda H_0(P\otimes_T C) \;\ge\; \beta_0\cdot\lambda(C/\mathfrak{m}_T C).
\]

## 証明

<!-- source: exposition/ja/exposition-ja.tex:814; block: paper-ja-L814 -->
<a id="paper-ja-L814"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

\(H_0(P\otimes C) = C^{\oplus\beta_0}/\operatorname{im}(d_1\otimes C)\) は極小性により \((C/\mathfrak{m}_T C)^{\oplus\beta_0}\) に全射する。

<!-- source: exposition/ja/exposition-ja.tex:816; block: paper-ja-L816 -->
<a id="paper-ja-L816"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

**Lean:** `LengthAlgebra.PerfectMinimalLowerBound`（極小性から全射を構成し、共通下界を適用。証明済み）。

<!-- source: exposition/ja/exposition-ja.tex:818; block: paper-ja-L818 -->
<a id="paper-ja-L818"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

普通の評価についても準同型と共役和の比較はあるが、この消滅の入力は一般には満たさない。

## 解説 §5.4 \(\lambda\)-平坦な代数での適用

## 系 5.12（\(\lambda\)-平坦な代数での比較・消滅・下界）

<!-- source: exposition/ja/exposition-ja.tex:827; block: paper-ja-L827 -->
<a id="paper-ja-L827"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

- (c) **消滅と下界**：補題 5.10、5.11 が成り立つ。

## 証明

<!-- source: exposition/ja/exposition-ja.tex:831; block: paper-ja-L831 -->
<a id="paper-ja-L831"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

系 4.11 により Koszul 有限性、正次数の Koszul ホモロジーの長さ零、\(e_\lambda(z;C)=r\) が得られる。(a) は命題 5.8、(b) は定理 5.9、(c) は補題 5.10、5.11 にこれらを入れたものである。

<!-- source: exposition/ja/exposition-ja.tex:833; block: paper-ja-L833 -->
<a id="paper-ja-L833"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

\(\lambda\)-CM 代数についても、命題 4.15 を通して同じである。

<!-- source: exposition/ja/exposition-ja.tex:834; block: paper-ja-L834 -->
<a id="paper-ja-L834"></a>

**保留理由**　perfect 複体一般での消滅・下界の補助論。論文の 5.6 は有限近似から作る漸近複体列の評価で、この段落の直接の行き先が定まらない。

**Lean:** `LengthAlgebra.FlatRealization` の `perfectEuler_conjSum_eq_of_flat`、`lambdaHomology_projective_vanishing_of_flat`、`perfectEuler_minimal_lower_bound_of_flat`（基底の Koszul 分解と降下を明示した形で証明済み）。

## 解説 §6.2 評価関手

<!-- source: exposition/ja/exposition-ja.tex:935; block: paper-ja-L935 -->
<a id="paper-ja-L935"></a>

**保留理由**　段ごとの Serre 商と列の商を比較する補足。原典の単一項目の記述としては対応が定まらない。

段ごとの長さ \(0\) は正規化超極限の長さ \(0\) を含意するが、逆は成り立たない。「段ごとに商をとり、次に列の商をとる」という説明を圏同値として使うには、射の分数表示の持ち上げと一様な制御を確かめる必要がある。ここではその同値を使わず、元の加群列から直接 Serre 商を作る。
