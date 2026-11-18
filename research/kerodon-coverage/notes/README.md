# Kerodon の本文原稿（NB-W1・NB-W2）

## 原稿の規則

- `<項目番号>.md` の先頭に題・item-tags.csv の Tag へのリンク・既存 review の照合先を置く。照合先は本文外に記す。状態の正本は review。
- `<節番号>.md` は導入・つなぎ。独立した項目への対応が明確な第5章以降の段落も番号別に置く。
- 本文は凍結中の解説 t-01〜t-15 の文言・旧番号・数式の \( \) と \[ \] を保存する。原典からは Tag を引く。環境見出しは `##`、Lean 宣言名はバッククォートで記す。
- HTML コメントに元ページと行、各ブロックの前に移設用アンカーを置く。元リンクの表示文言を保存し、リンク先は移設後のファイル・アンカーに更新する。
- p・li・表のデータ tr をブロックとして数える。環境見出しと表の列見出しはブロック数に含めない。式だけの p も数える。保留本文と配置上の所見は [issues.md](issues.md) に置く。

## review に行のない項目原稿

- [1.1.0.9.md](1.1.0.9.md)（Tag 04Z6）
- [1.1.0.14.md](1.1.0.14.md)（Tag 000P）
- [4.3.3.16.md](4.3.3.16.md)（Tag 016Z）
- [4.3.5.2.md](4.3.5.2.md)（Tag 017X）

## 段落の行き先

### t-01-definitions.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 26 / `t01-conv-universe-1` | `第 III 部を通して、Grothendieck 宇宙 \(\mathbb U\) を一つ固定する。\(\m` | [1.1](1.1.md#t01-conv-universe-1) |
| 33 / `t01-def-delta-1` | `\(n\ge0\) について、\([n]=\{0,1,\dots,n\}\) に通常の大小関係 \(0<1<` | [1.1.0.2](1.1.0.2.md#t01-def-delta-1) |
| 35 / `t01-def-delta-2` | `対象：\([n]\)（\(n\ge0\)）。` | [1.1.0.2](1.1.0.2.md#t01-def-delta-2) |
| 36 / `t01-def-delta-3` | `射：\(\mathrm{Hom}_\Delta([m],[n])\) は、順序を保つ写像 \(\theta\` | [1.1.0.2](1.1.0.2.md#t01-def-delta-3) |
| 37 / `t01-def-delta-4` | `合成：写像の合成。恒等射：恒等写像。` | [1.1.0.2](1.1.0.2.md#t01-def-delta-4) |
| 45 / `t01-def-sset-1` | `単体的集合とは関手 \(X\colon\Delta^{\mathrm{op}}\to\mathrm{Set}` | [1.1.0.6](1.1.0.6.md#t01-def-sset-1) |
| 52 / `t01-def-simplex-1` | `\(\Delta^n\) を \([n]\) が表現する関手 \(\Delta^n=\mathrm{Hom}` | [1.1.0.9](1.1.0.9.md#t01-def-simplex-1) |
| 59 / `t01-def-subsset-1` | `単体的集合 \(X\) の部分単体的集合とは、各 \([m]\) について部分集合 \(A([m])\sub` | [1.1.0.14](1.1.0.14.md#t01-def-subsset-1) |
| 66 / `t01-def-union-1` | `単体的集合 \(X\) の部分単体的集合の族 \((A_j)_{j\in J}\) について、その和 \(\` | [1.1.0.14](1.1.0.14.md#t01-def-union-1) |
| 67 / `t01-def-union-2` | `\[\Bigl(\bigcup_{j\in J}A_j\Bigr)([m])=\bigcup_{j\in J` | [1.1.0.14](1.1.0.14.md#t01-def-union-2) |
| 68 / `t01-def-union-3` | `で定める。これは \(X\) の部分単体的集合である。` | [1.1.0.14](1.1.0.14.md#t01-def-union-3) |
| 75 / `t01-def-face-1` | `\(0\le j\le n\) について、\(\Delta^n\) の部分単体的集合 \(\partial_` | [1.2.4](1.2.4.md#t01-def-face-1) |
| 76 / `t01-def-face-2` | `\[\partial_j\Delta^n([m])=\{\theta\colon[m]\to[n]\mid ` | [1.2.4](1.2.4.md#t01-def-face-2) |
| 77 / `t01-def-face-3` | `で定め、\(\Delta^n\) の \(j\) 番目の面という。` | [1.2.4](1.2.4.md#t01-def-face-3) |
| 84 / `t01-def-horn-1` | `\(n\ge1\)、\(0\le i\le n\) とする。\(\Delta^n\) の部分単体的集合 \(` | [1.2.4.1](1.2.4.1.md#t01-def-horn-1) |
| 86 / `t01-def-horn-2` | `部分単体的集合として直接：\(\Lambda^n_i([m])=\{\theta\colon[m]\to[n` | [1.2.4.1](1.2.4.1.md#t01-def-horn-2) |
| 87 / `t01-def-horn-3` | `面の和として：\(\Lambda^n_i=\bigcup_{j\ne i}\partial_j\Delta^` | [1.2.4.1](1.2.4.1.md#t01-def-horn-3) |
| 89 / `t01-def-horn-4` | `両者は一致する。\(\theta([m])\cup\{i\}\ne[n]\) は、\(\theta([m])` | [1.2.4.1](1.2.4.1.md#t01-def-horn-4) |
| 96 / `t01-def-quasicategory-1` | `単体的集合 \(X\) が quasicategory であるとは、すべての \(0<i<n\) について、` | [1.4.0.1](1.4.0.1.md#t01-def-quasicategory-1) |
| 103 / `t01-def-kan-1` | `単体的集合 \(X\) が Kan 複体であるとは、すべての \(0\le i\le n\) について、任意` | [1.2.5.1](1.2.5.1.md#t01-def-kan-1) |

### t-02-kan-category.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 27 / `t02-def-product-1` | `単体的集合 \(X,Y\) の積 \(X\times Y\) を` | [1.5.3](1.5.3.md#t02-def-product-1) |
| 28 / `t02-def-product-2` | `\[(X\times Y)([m])=X([m])\times Y([m]),\qquad (X\times` | [1.5.3](1.5.3.md#t02-def-product-2) |
| 29 / `t02-def-product-3` | `で定める（\(\theta\colon[m]\to[m']\)）。射影 \(X\times Y\to X\)` | [1.5.3](1.5.3.md#t02-def-product-3) |
| 36 / `t02-def-fun-1` | `\(\theta\colon[m]\to[n]\) について、\(\theta_*\colon\Delta^` | [1.5.3.1](1.5.3.1.md#t02-def-fun-1) |
| 37 / `t02-def-fun-2` | `\[\mathrm{Fun}(X,Y)([n])=\mathrm{Hom}_{\mathrm{sSet}}(` | [1.5.3.1](1.5.3.1.md#t02-def-fun-2) |
| 38 / `t02-def-fun-3` | `で定める。` | [1.5.3.1](1.5.3.1.md#t02-def-fun-3) |
| 45 / `t02-def-postcomposition-1` | `単体的集合 \(K\) と射 \(q\colon X\to S\) について、射 \(q_*\colon\m` | [1.5.3](1.5.3.md#t02-def-postcomposition-1) |
| 52 / `t02-thm-adjunction-1` | `単体的集合 \(X\) を固定すると、単体的集合 \(Z,Y\) について自然な全単射` | [1.5.3.2](1.5.3.2.md#t02-thm-adjunction-1) |
| 53 / `t02-thm-adjunction-2` | `\[\mathrm{Hom}_{\mathrm{sSet}}(Z\times X,Y)\cong\mathr` | [1.5.3.2](1.5.3.2.md#t02-thm-adjunction-2) |
| 54 / `t02-thm-adjunction-3` | `がある。すなわち \((-)\times X\) は \(\mathrm{Fun}(X,-)\) の左随伴で` | [1.5.3.2](1.5.3.2.md#t02-thm-adjunction-3) |
| 61 / `t02-def-composition-1` | `単体的集合 \(X,Y,Z\) について、合成 \(\circ\colon\mathrm{Fun}(Y,Z)` | [1.5.3](1.5.3.md#t02-def-composition-1) |
| 62 / `t02-def-composition-2` | `\[g\circ f\colon X\times\Delta^n\xrightarrow{(f,\ \mat` | [1.5.3](1.5.3.md#t02-def-composition-2) |
| 63 / `t02-def-composition-3` | `で定める。恒等射 \(\mathrm{id}_X\) は、射影 \(X\times\Delta^0\to X` | [1.5.3](1.5.3.md#t02-def-composition-3) |
| 70 / `t02-thm-composition-1` | `定義 2.5 の合成は単体的集合の射であり、結合的で、\(\mathrm{id}\) を単位とする。` | [1.5.3](1.5.3.md#t02-thm-composition-1) |
| 77 / `t02-def-scat-1` | `単体的圏とは、対象の集合と、対象 \(x,y\) ごとの単体的集合 \(\mathcal C(x,y)\)、` | [2.4.1.1](2.4.1.1.md#t02-def-scat-1) |
| 84 / `t02-def-kan-category-1` | `単体的圏 \(\mathcal Kan\) を次で定める。` | [3.1.6.1](3.1.6.1.md#t02-def-kan-category-1) |
| 86 / `t02-def-kan-category-2` | `対象：小さい Kan 複体（定義 1.9、冒頭の規約）。` | [3.1.6.1](3.1.6.1.md#t02-def-kan-category-2) |
| 87 / `t02-def-kan-category-3` | `射の単体的集合：\(\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)\)（定義 2.2` | [3.1.6.1](3.1.6.1.md#t02-def-kan-category-3) |
| 88 / `t02-def-kan-category-4` | `合成と恒等射：定義 2.5。` | [3.1.6.1](3.1.6.1.md#t02-def-kan-category-4) |
| 90 / `t02-def-kan-category-5` | `定理 2.6 によりこれは単体的圏である。` | [3.1.6.1](3.1.6.1.md#t02-def-kan-category-5) |
| 97 / `t02-thm-kan-hom-kan-1` | `Kan 複体 \(X,Y\) について、\(\mathcal Kan(X,Y)=\mathrm{Fun}(X` | [3.1.3.4](3.1.3.4.md#t02-thm-kan-hom-kan-1) |

### t-03-coherent-nerve.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t03-def-sfunctor-1` | `単体的圏 \(\mathcal C,\mathcal D\) の間の単体的関手 \(F\colon\math` | [2.4.1.11](2.4.1.11.md#t03-def-sfunctor-1) |
| 35 / `t03-def-poset-nerve-1` | `半順序集合 \(P\) について、単体的集合 \(N(P)\) を、\(N(P)([m])\) を順序を保つ` | [1.3.1.1](1.3.1.1.md#t03-def-poset-nerve-1) |
| 42 / `t03-def-path-category-1` | `\(n\ge0\) について、単体的圏 \(\mathfrak C[\Delta^n]\) を次で定める。` | [2.4.3.1](2.4.3.1.md#t03-def-path-category-1) |
| 44 / `t03-def-path-category-2` | `対象：\(0,1,\dots,n\)。` | [2.4.3.1](2.4.3.1.md#t03-def-path-category-2) |
| 45 / `t03-def-path-category-3` | `射の単体的集合：\(i\le j\) なら \(\mathfrak C[\Delta^n](i,j)=N(P` | [2.4.3.1](2.4.3.1.md#t03-def-path-category-3) |
| 46 / `t03-def-path-category-4` | `合成：和集合 \(P_{jk}\times P_{ij}\to P_{ik}\)、\((T,S)\mapst` | [2.4.3.1](2.4.3.1.md#t03-def-path-category-4) |
| 48 / `t03-def-path-category-5` | `\(\theta\colon[m]\to[n]\) について、単体的関手 \(\mathfrak C[\th` | [2.4.3.1](2.4.3.1.md#t03-def-path-category-5) |
| 55 / `t03-def-hc-nerve-1` | `単体的圏 \(\mathcal C\) について、単体的集合 \(N^{hc}(\mathcal C)\) ` | [2.4.3.5](2.4.3.5.md#t03-def-hc-nerve-1) |
| 56 / `t03-def-hc-nerve-2` | `\[N^{hc}(\mathcal C)([n])=\mathrm{Hom}_{\mathrm{sCat}}` | [2.4.3.5](2.4.3.5.md#t03-def-hc-nerve-2) |
| 57 / `t03-def-hc-nerve-3` | `で定める。` | [2.4.3.5](2.4.3.5.md#t03-def-hc-nerve-3) |
| 64 / `t03-thm-hc-functor-1` | `単体的関手 \(F\colon\mathcal C\to\mathcal D\) に後合成 \(\sigma` | [2.4.3](2.4.3.md#t03-thm-hc-functor-1) |
| 71 / `t03-rem-size-scat-1` | `定理 3.5 の \(\mathrm{sCat}\) と \(\mathrm{sSet}\) は、大きさを制` | [2.4.3](2.4.3.md#t03-rem-size-scat-1) |
| 78 / `t03-thm-hc-quasicategory-1` | `単体的圏 \(\mathcal C\) のすべての射の単体的集合 \(\mathcal C(x,y)\) が` | [2.4.5.1](2.4.5.1.md#t03-thm-hc-quasicategory-1) |
| 85 / `t03-def-spaces-1` | `\(\mathcal S=N^{hc}(\mathcal Kan)\) と定める（\(\mathcal Ka` | [3.1.6.1](3.1.6.1.md#t03-def-spaces-1) |
| 92 / `t03-rem-size-spaces-1` | `\(\mathcal Kan\) の対象は小さい Kan 複体で、その全体は \(\mathbb U\) の` | [3.1.6](3.1.6.md#t03-rem-size-spaces-1) |

### t-04-join-slice.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t04-def-extension-lin-1` | `有限な全順序集合 \(I\)（空でもよい）について、\(I\) が空でなければ \(&#124;I&#124;=n+1\) とし` | [4.3.3](4.3.3.md#t04-def-extension-lin-1) |
| 29 / `t04-def-extension-lin-2` | `\[X^+(I)=\begin{cases}X([n])&(I\ne\varnothing)\\ \{\as` | [4.3.3](4.3.3.md#t04-def-extension-lin-2) |
| 30 / `t04-def-extension-lin-3` | `とおく。順序を保つ写像 \(\alpha\colon I\to J\) について、\(I\ne\varnot` | [4.3.3](4.3.3.md#t04-def-extension-lin-3) |
| 37 / `t04-def-initial-segment-1` | `全順序集合 \(J\) の部分集合 \(I\) が始切片であるとは、\(i\in I\)、\(j\le i\` | [4.3.3.1](4.3.3.1.md#t04-def-initial-segment-1) |
| 44 / `t04-def-join-1` | `単体的集合 \(K,L\) の join \(K\star L\) を` | [4.3.3.13](4.3.3.13.md#t04-def-join-1) |
| 45 / `t04-def-join-2` | `\[(K\star L)([n])=\bigsqcup_{I\sqsubseteq[n]}K^+(I)\ti` | [4.3.3.13](4.3.3.13.md#t04-def-join-2) |
| 46 / `t04-def-join-3` | `で定める（\(K^+\)、\(L^+\) は定義 4.1、始切片は定義 4.2）。\(\theta\colo` | [4.3.3.13](4.3.3.13.md#t04-def-join-3) |
| 47 / `t04-def-join-4` | `\[\bigl(K^+(\theta&#124;_{I'})(\sigma),\ L^+(\theta&#124;_{[m]\s` | [4.3.3.13](4.3.3.13.md#t04-def-join-4) |
| 48 / `t04-def-join-5` | `に送る。ここで \(\theta&#124;_{I'}\colon I'\to I\)、\(\theta&#124;_{[m]\` | [4.3.3.13](4.3.3.13.md#t04-def-join-5) |
| 55 / `t04-rem-join-formula-1` | `\([n]\) の始切片は \(\varnothing\)、\(\{0,\dots,p\}\)（\(0\le` | [4.3.3](4.3.3.md#t04-rem-join-formula-1) |
| 56 / `t04-rem-join-formula-2` | `\[(K\star L)([n])=L([n])\ \sqcup\bigsqcup_{p+1+q=n}K([` | [4.3.3](4.3.3.md#t04-rem-join-formula-2) |
| 57 / `t04-rem-join-formula-3` | `となる（Kerodon Remark 4.3.3.19）。\(I=\varnothing\) の成分が \(` | [4.3.3](4.3.3.md#t04-rem-join-formula-3) |
| 64 / `t04-def-join-functor-1` | `単体的集合の射 \(f\colon K\to K'\)、\(g\colon L\to L'\) について、\` | [4.3.3.16](4.3.3.16.md#t04-def-join-functor-1) |
| 65 / `t04-def-join-functor-2` | `\[\iota_K\colon K\to K\star L,\quad\sigma\mapsto(\sigm` | [4.3.3.16](4.3.3.16.md#t04-def-join-functor-2) |
| 66 / `t04-def-join-functor-3` | `を定める。` | [4.3.3.16](4.3.3.16.md#t04-def-join-functor-3) |
| 73 / `t04-def-slice-1` | `単体的集合 \(X,K\) と射 \(p\colon K\to X\) について、単体的集合 \(X_{/p` | [4.3.5.1](4.3.5.1.md#t04-def-slice-1) |
| 74 / `t04-def-slice-2` | `\[X_{/p}([n])=\{\sigma\colon\Delta^n\star K\to X\mid\s` | [4.3.5.1](4.3.5.1.md#t04-def-slice-2) |
| 75 / `t04-def-slice-3` | `で定め、\(\theta\colon[m]\to[n]\) はそれぞれ \(\theta_*\star\ma` | [4.3.5.1](4.3.5.1.md#t04-def-slice-3) |
| 82 / `t04-def-identity-vertex-1` | `単体的集合 \(B\) の頂点 \(b\colon\Delta^0\to B\) について、合成 \(\De` | [4.3.5](4.3.5.md#t04-def-identity-vertex-1) |
| 89 / `t04-def-slice-projection-1` | `単体的集合の射 \(X_{/p}\to X\) を、\(n\) 単体 \(\sigma\colon\Delt` | [4.3.5.2](4.3.5.2.md#t04-def-slice-projection-1) |
| 96 / `t04-rem-size-slice-1` | `定義 4.5 は \(X\)、\(K\) の大きさを問わず、\(X_{/p}([n])\) は集合 \(\m` | [4.3.5](4.3.5.md#t04-rem-size-slice-1) |
| 103 / `t04-thm-slice-quasicategory-1` | `\(X\) を quasicategory（定義 1.8）、\(K\) を単体的集合、\(p\colon K` | [4.3.6.1](4.3.6.1.md#t04-thm-slice-quasicategory-1) |

### t-05-fibrations.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t05-def-boundary-1` | `\(n\ge0\) について、\(\Delta^n\) の部分単体的集合 \(\partial\Delta^` | [1.1.4.10](1.1.4.10.md#t05-def-boundary-1) |
| 35 / `t05-def-lifting-1` | `単体的集合の射 \(q\colon E\to B\) が部分単体的集合の包含 \(A\subseteq A'` | [1.5.4.3](1.5.4.3.md#t05-def-lifting-1) |
| 42 / `t05-def-fibrations-1` | `単体的集合の射 \(q\colon E\to B\) が、次の表の包含のすべてに対して右持ち上げ性質（定義 ` | [1.5](1.5.md#t05-def-fibrations-1) |
| 45 / `t05-def-fibrations-3` | `Kan fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(n\ge1\` | [3.1.1.1](3.1.1.1.md#t05-def-fibrations-3) |
| 46 / `t05-def-fibrations-4` | `inner fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(0<i<` | [4.1.1.1](4.1.1.1.md#t05-def-fibrations-4) |
| 47 / `t05-def-fibrations-5` | `左 fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(0\le i<n` | [4.2.1.1](4.2.1.1.md#t05-def-fibrations-5) |
| 48 / `t05-def-fibrations-6` | `右 fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(0<i\le n` | [4.2.1.1](4.2.1.1.md#t05-def-fibrations-6) |
| 49 / `t05-def-fibrations-7` | `trivial Kan fibration\(\partial\Delta^n\subseteq\Delta` | [1.5.5.1](1.5.5.1.md#t05-def-fibrations-7) |
| 57 / `t05-rem-fibration-point-1` | `\(\Delta^0\) は各段が一点の単体的集合で、任意の単体的集合 \(X\) から唯一の射 \(X\t` | [1.2.5](1.2.5.md#t05-rem-fibration-point-1) |
| 64 / `t05-def-contractible-1` | `単体的集合 \(X\) が可縮であるとは、\(X\to\Delta^0\) が trivial Kan fi` | [1.5.5.8](1.5.5.8.md#t05-def-contractible-1) |

### t-06-fiber-products.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t06-def-fiber-product-1` | `単体的集合の射 \(f\colon X\to Z\)、\(g\colon Y\to Z\) について、単体的` | [1.5](1.5.md#t06-def-fiber-product-1) |
| 29 / `t06-def-fiber-product-2` | `\[(X\times_ZY)([m])=\{(x,y)\in X([m])\times Y([m])\mid` | [1.5](1.5.md#t06-def-fiber-product-2) |
| 30 / `t06-def-fiber-product-3` | `で定め、\(\theta\) は成分ごとに作用させる。これは積 \(X\times Y\)（定義 2.1）の` | [1.5](1.5.md#t06-def-fiber-product-3) |
| 37 / `t06-rem-fiber-product-pullback-1` | `\(X\times_ZY\) と二つの射影は、単体的集合の圏における \(f\) と \(g\) の引き戻し` | [1.5](1.5.md#t06-rem-fiber-product-pullback-1) |
| 44 / `t06-def-fiber-1` | `単体的集合 \(B\) の頂点とは \(B([0])\) の元のことであり、米田の補題により射 \(\Del` | [4.2.1](4.2.1.md#t06-def-fiber-1) |
| 45 / `t06-def-fiber-2` | `\[E_b=E\times_B\Delta^0\]` | [4.2.1](4.2.1.md#t06-def-fiber-2) |
| 46 / `t06-def-fiber-3` | `を \(q\) の \(b\) 上のファイバーという。` | [4.2.1](4.2.1.md#t06-def-fiber-3) |
| 53 / `t06-rem-fiber-subset-1` | `\(\Delta^0\) は各段が一点なので、\(c_m\colon[m]\to[0]\) を唯一の射として` | [4.2.1](4.2.1.md#t06-rem-fiber-subset-1) |
| 54 / `t06-rem-fiber-subset-2` | `\[E_b([m])=\{e\in E([m])\mid q(e)=B(c_m)(b)\}\]` | [4.2.1](4.2.1.md#t06-rem-fiber-subset-2) |
| 55 / `t06-rem-fiber-subset-3` | `と同一視できる。` | [4.2.1](4.2.1.md#t06-rem-fiber-subset-3) |

### t-07-mapping-spaces.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t07-def-pinched-hom-1` | `単体的集合 \(C\) の頂点 \(x,y\) について、コスライスの射影 \(C_{x/}\to C\) ` | [4.6.5.1](4.6.5.1.md#t07-def-pinched-hom-1) |
| 35 / `t07-thm-pinched-hom-kan-1` | `\(C\) が quasicategory なら、頂点 \(x,y\) について \(\mathrm{Hom` | [4.6.5.5](4.6.5.5.md#t07-thm-pinched-hom-kan-1) |

### t-08-initial-terminal.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t08-def-initial-1` | `quasicategory \(C\) の頂点 \(x\) が始対象であるとは、コスライスの射影 \(C_{` | [4.7.3.12](4.7.3.12.md#t08-def-initial-1) |
| 35 / `t08-thm-initial-equiv-1` | `quasicategory \(C\) の頂点 \(x\) について、次は同値である。` | [4.7.3.1](4.7.3.1.md#t08-thm-initial-equiv-1) |
| 37 / `t08-thm-initial-equiv-2` | `\(x\) は始対象である（定義 8.1）。` | [4.7.3.1](4.7.3.1.md#t08-thm-initial-equiv-2) |
| 38 / `t08-thm-initial-equiv-3` | `すべての頂点 \(y\) について \(\mathrm{Hom}^L_C(x,y)\)（定義 7.1）は可縮` | [4.7.3.1](4.7.3.1.md#t08-thm-initial-equiv-3) |
| 46 / `t08-def-terminal-1` | `quasicategory \(C\) の頂点 \(y\) が終対象であるとは、スライスの射影 \(C_{/` | [4.7.3.12](4.7.3.12.md#t08-def-terminal-1) |
| 53 / `t08-thm-terminal-equiv-1` | `quasicategory \(C\) の頂点 \(y\) について、次は同値である。` | [4.7.3.1](4.7.3.1.md#t08-thm-terminal-equiv-1) |
| 55 / `t08-thm-terminal-equiv-2` | `\(y\) は終対象である（定義 8.3）。` | [4.7.3.1](4.7.3.1.md#t08-thm-terminal-equiv-2) |
| 56 / `t08-thm-terminal-equiv-3` | `すべての頂点 \(x\) について \(\mathrm{Hom}^R_C(x,y)\)（定義 7.1）は可縮` | [4.7.3.1](4.7.3.1.md#t08-thm-terminal-equiv-3) |

### t-09-limits.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t09-def-limit-1` | `\(C\) を quasicategory、\(K\) を単体的集合、\(p\colon K\to C\) ` | [7.1.3](7.1.3.md#t09-def-limit-1) |
| 30 / `t09-def-limit-2` | `\(C_{/p}\) の頂点で終対象（定義 8.3）であるものを \(p\) の極限という。` | [7.1.3.4](7.1.3.4.md#t09-def-limit-2) |
| 31 / `t09-def-limit-3` | `\(C_{p/}\) の頂点で始対象（定義 8.1）であるものを \(p\) の余極限という。` | [7.1.3.5](7.1.3.5.md#t09-def-limit-3) |
| 39 / `t09-rem-limit-cone-1` | `\(C_{/p}\) の頂点は、\(K\) 上で \(p\) となる射 \(\Delta^0\star K\` | [7.1.3](7.1.3.md#t09-rem-limit-cone-1) |

### t-10-fibration-yoneda.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t10-def-relative-fun-1` | `単体的集合の射 \(r\colon K\to S\)、\(q\colon X\to S\) について、\(r` | [3.1.3.7](3.1.3.7.md#t10-def-relative-fun-1) |
| 29 / `t10-def-relative-fun-2` | `\[\mathrm{Fun}_{/S}(K,X)=\mathrm{Fun}(K,X)\times_{\mat` | [3.1.3.7](3.1.3.7.md#t10-def-relative-fun-2) |
| 30 / `t10-def-relative-fun-3` | `を相対関手空間という（\(q_*\) の \(r\) 上のファイバー。定義 2.3）。その \(n\) 単体` | [3.1.3.7](3.1.3.7.md#t10-def-relative-fun-3) |
| 37 / `t10-def-yoneda-evaluation-1` | `単体的集合の射 \(q\colon E\to B\) と頂点 \(b\) について、\(B_{b/}\) を` | [4.2.5](4.2.5.md#t10-def-yoneda-evaluation-1) |
| 38 / `t10-def-yoneda-evaluation-2` | `\[\mathrm{ev}\colon\mathrm{Fun}_{/B}(B_{b/},E)\to E_b\` | [4.2.5](4.2.5.md#t10-def-yoneda-evaluation-2) |
| 39 / `t10-def-yoneda-evaluation-3` | `を、\(n\) 単体 \(f\colon B_{b/}\times\Delta^n\to E\) を \(f` | [4.2.5](4.2.5.md#t10-def-yoneda-evaluation-3) |
| 46 / `t10-thm-fibration-yoneda-1` | `\(B\) を単体的集合、\(b\) をその頂点、\(q\colon E\to B\) を射とする。` | [4.2.5](4.2.5.md#t10-thm-fibration-yoneda-1) |
| 48 / `t10-thm-fibration-yoneda-2` | `\(q\) が左 fibration（定義 5.3）なら、\(\mathrm{ev}\colon\mathr` | [4.2.5](4.2.5.md#t10-thm-fibration-yoneda-2) |
| 49 / `t10-thm-fibration-yoneda-3` | `\(q\) が右 fibration なら、\(\mathrm{ev}\colon\mathrm{Fun}_` | [4.2.5](4.2.5.md#t10-thm-fibration-yoneda-3) |
| 57 / `t10-rem-size-relative-fun-1` | `\(\mathrm{Fun}_{/S}(K,X)\) は \(K\)、\(X\)、\(S\) の大きさを問わ` | [4.2.5](4.2.5.md#t10-rem-size-relative-fun-1) |

### t-11-straightening.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t11-def-functor-qcat-1` | `単体的集合 \(B\) と quasicategory \(D\) について、\(B\) から \(D\) ` | [1.5.0.1](1.5.0.1.md#t11-def-functor-qcat-1) |
| 35 / `t11-def-small-fibers-1` | `単体的集合の射 \(q\colon E\to B\) が小さいファイバーをもつとは、\(B\) のすべての頂` | [5.6](5.6.md#t11-def-small-fibers-1) |
| 42 / `t11-def-straightening-1` | `単体的集合 \(B\) 上の左 fibration（定義 5.3）\(q\colon E\to B\) で小` | [5.6.0.6](5.6.0.6.md#t11-def-straightening-1) |
| 43 / `t11-def-straightening-2` | `\[\mathrm{St}(q)\colon B\to\mathcal S\]` | [5.6.0.6](5.6.0.6.md#t11-def-straightening-2) |
| 44 / `t11-def-straightening-3` | `を対応させる操作を straightening という（\(\mathcal S\) は定義 3.7）。構成` | [5.6.0.6](5.6.0.6.md#t11-def-straightening-3) |
| 51 / `t11-rem-straightening-intuition-1` | `\(\mathrm{St}(q)\) は頂点 \(b\) をファイバー \(E_b\) に、辺 \(b\to` | [5.6](5.6.md#t11-rem-straightening-intuition-1) |

### t-12-mapping-functor.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t12-def-opposite-1` | `\(\theta\colon[m]\to[n]\) について \(\theta^{\mathrm{rev}}` | [1.4.2.2](1.4.2.2.md#t12-def-opposite-1) |
| 29 / `t12-def-opposite-2` | `\[X^{\mathrm{op}}([n])=X([n]),\qquad X^{\mathrm{op}}(\` | [1.4.2.2](1.4.2.2.md#t12-def-opposite-2) |
| 30 / `t12-def-opposite-3` | `で定める。単体的集合の射 \(f\colon X\to Y\) について、同じ成分の写像で \(f^{\ma` | [1.4.2.2](1.4.2.2.md#t12-def-opposite-3) |
| 37 / `t12-def-twisted-arrow-1` | `単体的集合 \(C\) について、単体的集合 \(\mathrm{Tw}(C)\) を` | [8.1.1.1](8.1.1.1.md#t12-def-twisted-arrow-1) |
| 38 / `t12-def-twisted-arrow-2` | `\[\mathrm{Tw}(C)([n])=\mathrm{Hom}_{\mathrm{sSet}}\big` | [8.1.1.1](8.1.1.1.md#t12-def-twisted-arrow-2) |
| 39 / `t12-def-twisted-arrow-3` | `で定め、\(\theta\colon[m]\to[n]\) は \((\theta_*)^{\mathrm{` | [8.1.1.1](8.1.1.1.md#t12-def-twisted-arrow-3) |
| 46 / `t12-def-twisted-arrow-projection-1` | `\(n\) 単体 \(\sigma\colon(\Delta^n)^{\mathrm{op}}\star\D` | [8.1.1.6](8.1.1.6.md#t12-def-twisted-arrow-projection-1) |
| 47 / `t12-def-twisted-arrow-projection-2` | `\[\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C\]` | [8.1.1.6](8.1.1.6.md#t12-def-twisted-arrow-projection-2) |
| 48 / `t12-def-twisted-arrow-projection-3` | `を定める（積は定義 2.1。\(\Delta^n\) からの射と \(n\) 単体は米田の補題で同一視する）` | [8.1.1.6](8.1.1.6.md#t12-def-twisted-arrow-projection-3) |
| 55 / `t12-thm-twisted-arrow-left-fibration-1` | `\(C\) が quasicategory なら、射影 \(\mathrm{Tw}(C)\to C^{\ma` | [8.1.1.11](8.1.1.11.md#t12-thm-twisted-arrow-left-fibration-1) |
| 62 / `t12-rem-size-twisted-arrow-1` | `\(C\) が小さければ \(\mathrm{Tw}(C)\) は小さく、射影 \(\mathrm{Tw}(` | [8.1.1](8.1.1.md#t12-rem-size-twisted-arrow-1) |
| 69 / `t12-def-map-functor-1` | `\(C\) を小さい quasicategory とする。定理 12.4 と上の注意により、射影 \(\ma` | [8.3.3.1](8.3.3.1.md#t12-def-map-functor-1) |
| 70 / `t12-def-map-functor-2` | `\[\mathrm{Map}_C=\mathrm{St}\bigl(\mathrm{Tw}(C)\to C^` | [8.3.3.1](8.3.3.1.md#t12-def-map-functor-2) |
| 71 / `t12-def-map-functor-3` | `を \(C\) の写像空間の関手と定める。` | [8.3.3.1](8.3.3.1.md#t12-def-map-functor-3) |

### t-13-homotopy-equivalence.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t13-def-homotopy-equivalence-1` | `Kan 複体の射 \(f\colon X\to Y\) がホモトピー同値であるとは、射 \(g\colon ` | [3.1.7.1](3.1.7.1.md#t13-def-homotopy-equivalence-1) |
| 35 / `t13-def-induced-hom-1` | `単体的集合の射 \(f\colon C\to D\) と頂点 \(x,y\) について、\(\mathrm{` | [4.6.5](4.6.5.md#t13-def-induced-hom-1) |
| 36 / `t13-def-induced-hom-2` | `\[f_*\colon\mathrm{Hom}^R_C(x,y)\to\mathrm{Hom}^R_D(f(` | [4.6.5](4.6.5.md#t13-def-induced-hom-2) |
| 37 / `t13-def-induced-hom-3` | `を定める（\(\mathrm{Hom}^R\) は定義 7.1）。` | [4.6.5](4.6.5.md#t13-def-induced-hom-3) |
| 44 / `t13-def-fully-faithful-1` | `quasicategory の間の関手 \(f\colon C\to D\) が充満忠実であるとは、すべての` | [4.8.3.1](4.8.3.1.md#t13-def-fully-faithful-1) |

### t-14-presheaves.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t14-thm-fun-quasicategory-1` | `\(K\) を単体的集合、\(D\) を quasicategory とすると、\(\mathrm{Fun}` | [1.5.3.7](1.5.3.7.md#t14-thm-fun-quasicategory-1) |
| 35 / `t14-def-presheaf-1` | `小さい quasicategory \(C\) について、\(\mathcal P(C)=\mathrm{F` | [1.5.3.8](1.5.3.8.md#t14-def-presheaf-1) |
| 42 / `t14-rem-size-presheaf-1` | `\(\mathcal S\) は小さくない（第 3 章の注意）ので、\(\mathcal P(C)\) も小` | [8.3.3](8.3.3.md#t14-rem-size-presheaf-1) |
| 49 / `t14-def-representable-1` | `小さい quasicategory \(C\) の頂点 \(y\) について、前層 \(h_y\) を合成` | [5.6.6.2](5.6.6.2.md#t14-def-representable-1) |
| 50 / `t14-def-representable-2` | `\[h_y\colon C^{\mathrm{op}}\cong C^{\mathrm{op}}\times` | [5.6.6.2](5.6.6.2.md#t14-def-representable-2) |
| 51 / `t14-def-representable-3` | `で定め、\(y\) が表現する前層という（\(\mathrm{Map}_C\) は定義 12.5）。` | [5.6.6.2](5.6.6.2.md#t14-def-representable-3) |
| 58 / `t14-def-yoneda-embedding-1` | `小さい quasicategory \(C\) について、\(\mathrm{Map}_C\) と成分の入れ` | [8.3.3.9](8.3.3.9.md#t14-def-yoneda-embedding-1) |
| 59 / `t14-def-yoneda-embedding-2` | `\[j\colon C\to\mathcal P(C)\]` | [8.3.3.9](8.3.3.9.md#t14-def-yoneda-embedding-2) |
| 60 / `t14-def-yoneda-embedding-3` | `と書き、Yoneda 埋め込みという。頂点 \(y\) について \(j(y)=h_y\)（定義 14.3）` | [8.3.3.9](8.3.3.9.md#t14-def-yoneda-embedding-3) |

### t-15-yoneda.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 28 / `t15-def-yoneda-evaluation-functor-1` | `（未記入）` | [保留](issues.md#t15-def-yoneda-evaluation-functor-1) |
| 35 / `t15-thm-yoneda-1` | `\(C\) を小さい quasicategory とする。` | [8.3.1](8.3.1.md#t15-thm-yoneda-1) |
| 37 / `t15-thm-yoneda-2` | `前層 \(F\)（定義 14.2）と頂点 \(y\) について、\(\mathrm{Hom}^R_{\mat` | [8.3.1.3](8.3.1.3.md#t15-thm-yoneda-2) |
| 38 / `t15-thm-yoneda-3` | `Yoneda 埋め込み \(j\colon C\to\mathcal P(C)\)（定義 14.4）は充満忠` | [8.3.3.13](8.3.3.13.md#t15-thm-yoneda-3) |
