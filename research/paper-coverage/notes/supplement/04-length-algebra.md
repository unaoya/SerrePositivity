# 長さ付き代数（解説 §4 の補足）

<!-- NB-W4: 凍結解説から転記。 -->

## 解説 §4.1 長さ関数と長さ付き代数

## 例 4.2

<!-- source: exposition/ja/exposition-ja.tex:421; block: paper-ja-L421 -->
<a id="paper-ja-L421"></a>

**Lean:** `NormalizedLength`（`PerfectComplex.NormalizedLength`）、普通の長さは `NormalizedLength.ordinary`（\(J = \bot\)）。Lean の名前は元論文に合わせて「正規化長さ」のまま（付録 A.4）。

## 定義 4.3（長さ付き代数）

<!-- source: exposition/ja/exposition-ja.tex:424; block: paper-ja-L424 -->
<a id="paper-ja-L424"></a>

\(A\) を可換環、\(z=(z_1,\dots,z_e)\) をその元の有限列とし、\(z^v=(z_1^v,\dots,z_e^v)\) と書く。**長さ付き \(A\) 代数**とは、可換 \(A\) 代数 \(C\) と、\(J=(z)C\) のある冪で加群全体が消される \(C\) 加群の上の長さ関数 \(\lambda\) の組 \((C,\lambda)\) のことである。

<!-- source: exposition/ja/exposition-ja.tex:426; block: paper-ja-L426 -->
<a id="paper-ja-L426"></a>

\(A\) がネーター局所環で \(\sqrt{(z)}=\mathfrak{m}_A\) なら、\((z)C\)-冪ねじれと \(\mathfrak{m}_A C\)-冪ねじれは同じ条件である。実際、\(\mathfrak{m}_A\) のある冪が \((z)\) に入り、この包含を \(C\) に移せばよい。§4.2 と定義 4.8 では \(A\) のネーター性は仮定せず、有限列 \(z\) を固定して使う。

## 解説 §4.2 評価先：長さ付きアーベル圏の構成

## 命題 4.7（有限な商と大きな商の有限部分）

<!-- source: exposition/ja/exposition-ja.tex:474; block: paper-ja-L474 -->
<a id="paper-ja-L474"></a>

**Lean:** `LengthAlgebra.FiniteQuotientEquivalence` の `finiteQuotientEquivalence`。ホモロジー、零対象、Euler 数と \(K_0\) 評価への接続は `PerfectHomologyComparison`。
