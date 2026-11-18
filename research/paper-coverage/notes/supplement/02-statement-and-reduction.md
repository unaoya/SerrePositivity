# 主張と帰着

<!-- NB-W4: 凍結解説から転記。 -->

## 定理 1.2（核の場合）

## 帰着（Lemma 5.1）

<!-- source: exposition/ja/exposition-ja.tex:112; block: paper-ja-L112 -->
<a id="paper-ja-L112"></a>

消滅定理はここと補題 9.2（Lemma 5.2）の2か所で使う。

## 注意 1.3（消滅定理の証明：巡回 Adams 作用素）

<!-- source: exposition/ja/exposition-ja.tex:115; block: paper-ja-L115 -->
<a id="paper-ja-L115"></a>

元論文は消滅定理を引用するが、形式化では Gillet–Soulé の Adams 作用素の方法で証明した。Chow 群・局所 Chern 指標・Riemann–Roch は使わない。\(R\) を次元 \(d\) の正則局所環とし、閉集合 \(Z\subseteq\operatorname{Spec} R\) に台をもつ有界な有限射影複体の Grothendieck 群を \(K_0^Z(R)\) と書く。テンソル積がカップ積 \(K_0^Y\times K_0^Z\to K_0^{Y\cap Z}\) を与え、\(\chi(M,N)\) は分解の類 \([F_M]\in K_0^{\operatorname{Supp} M}\)、\([F_N]\in K_0^{\operatorname{Supp} N}\) の積の Euler 標数である。

<!-- source: exposition/ja/exposition-ja.tex:117; block: paper-ja-L117 -->
<a id="paper-ja-L117"></a>

1. **巡回 Adams 作用素。** 素数 \(p\) と、\(1/p\) と \(1\) の原始 \(p\) 乗根 \(\zeta\) を含む係数体 \(E\) をとる。巡回群 \(C_p\) はテンソル冪 \(X^{\otimes p}\) に Koszul 符号つきで作用する。その \(\zeta^j\) 固有部分を使い \(\psi^p[X]=\sum_j\zeta^j[(X^{\otimes p})^{(\zeta^j)}]\) と定める。これは (A1) 加法的、(A2) カップ積と乗法的、(A3) 平坦な底変換と可換、(A4) 長さ \(1\) の Koszul 複体で \(\psi^p[K(a)]=p\,[K(a)]\) を満たす。加法性は、射影複体の擬同型がホモトピー同値であることと、短完全列の次数ごとの分裂から得る（混合項は \(C_p\) が自由に作用するので寄与しない）。

<!-- source: exposition/ja/exposition-ja.tex:118; block: paper-ja-L118 -->
<a id="paper-ja-L118"></a>

2. **重みの評価。** \(Z\) の余次元が \(c\) なら、\(K_0^Z(R)_E\) 上の \(\psi^p\) の固有値は \(p^c,\dots,p^d\) に限る。高さ \(c\) の生成点全体で半局所化し、台つき局所化の完全列（\(K_0^Z\cong G_0^Z\) との比較から証明）と Koszul 複体による生成を使って、余次元についての下降帰納法で示す。閉点では \(K_0^{\{\mathfrak{m}\}}(R)_E\cong E\) が純粋に重み \(d\) である。

<!-- source: exposition/ja/exposition-ja.tex:119; block: paper-ja-L119 -->
<a id="paper-ja-L119"></a>

3. **結論。** 正則局所環では \(\operatorname{ht}P=d-\dim R/P\) なので、\([F_M]\) は重み \(\ge d-\dim M\)、\([F_N]\) は重み \(\ge d-\dim N\) の部分にある。(A2) により積の重みは \(\ge 2d-\dim M-\dim N>d\) となるが、積は閉点に台をもち重み \(d\) しかないので零。よって \(\chi(M,N)=0\)。

<!-- source: exposition/ja/exposition-ja.tex:121; block: paper-ja-L121 -->
<a id="paper-ja-L121"></a>

素数は、剰余標数が \(2\) でなければ \(p=2\)（\(\zeta=-1\) なので係数拡大は不要）、剰余標数が \(2\) なら \(p=3\) とし、\(1\) の原始 \(3\) 乗根を添加した平坦局所拡大の上で同じ議論を行う。拡大で正則性・台の次元・\(\chi\) が保たれることも証明している。原典は Gillet–Soulé、巡回 Adams 作用素の構成と公理の証明は Brown–Miller–Thompson–Walker（*Cyclic Adams operations*, arXiv:1601.05072）による。

<!-- source: exposition/ja/exposition-ja.tex:122; block: paper-ja-L122 -->
<a id="paper-ja-L122"></a>

**Lean:** `IntersectionMultiplicity.AdamsVanishingAll` の `intersectionVanishing_of_adams`。剰余標数 \(2\) 以外は `intersectionVanishing_of_residue_two_ne_zero`（`KTheory.Adams.CyclicTwo`）、剰余標数 \(2\) は `intersectionVanishing_of_residue_two_eq_zero`（`KTheory.Adams.CyclicThree`）。作用素の公理の束は `Adams.LocalizationAdamsFamily`、重みの評価は `KTheory.Adams.SemilocalPureWeight`、カップ積の消滅は `KTheory.Adams.CupVanishing`。

## 先行結果と位置づけ

<!-- source: exposition/ja/exposition-ja.tex:128; block: paper-ja-L128 -->
<a id="paper-ja-L128"></a>

等標数と不分岐の場合（完備 DVR 上の冪級数環を含む）は Serre による。Roberts、Gillet–Soulé は \(\dim M+\dim N<\dim R\) での消滅を、Gabber は一般の非負性を示した。正値性の部分的な結果として、Skalit（2 次元正則局所環上 essentially smooth な場合）、KC–Soto Levins（Serre の持ち上げ条件をみたす加群）、Bhatt–Hochster–Ma（両方の商整域に lim Cohen–Macaulay 列があれば正、付録 B.2）がある。元論文の新しい部分は剰余標数 \(p>0\) の混標数の場合で、不分岐も分岐も一様に扱う。等標数は Lemma 5.1 で Serre を引用するだけで、別証明はしていない（形式化では、主定理が使う剰余標数零の場合を対角線論法で証明した。付録 A.1）。元論文の脚注 1 には、同じ主張（素イデアル商の形）が 2025 年 12 月に公開ポストされていることが記録されている。

## 系（この解説では扱わない）

<!-- source: exposition/ja/exposition-ja.tex:131; block: paper-ja-L131 -->
<a id="paper-ja-L131"></a>

元論文は定理 1.1 から二つの系を導く。分岐する混標数の正則局所環で \(\sqrt{P+Q}=\mathfrak{m}\)、\(\operatorname{ht}P+\operatorname{ht}Q=\dim R\) なら、\(r\ge1\) で \(P\cap Q^{(r)}\subseteq\mathfrak{m}^{r+1}\)（Kurano–Roberts の「正値性から記号的冪へ」の定理の適用）。また strict transform の交点についての不等式 \(\chi_A(A/P,A/Q)\ge e(A/P)\,e(A/Q)\)（Corollary 1.2、Skalit の爆発公式に正値性を入れたもの）。どちらも定理 1.1 の帰結であり、形式化の対象にしていない。
