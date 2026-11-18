# Kerodon の本文原稿（NB-W1〜NB-W3）

## 原稿の規則

- `<項目番号>.md` の先頭に題・item-tags.csv の Tag へのリンク・既存 review の照合先を置く。照合先は本文外に記す。状態の正本は review。
- `<節番号>.md` は導入・つなぎ。独立した項目への対応が明確な第5章以降の段落も番号別に置く。
- 本文は凍結中の解説 t-01〜t-15 の文言・旧番号・数式の \( \) と \[ \] を保存する。原典からは Tag を引く。環境見出しは `##`、Lean 宣言名はバッククォートで記す。
- HTML コメントに元ページと行、各ブロックの前に移設用アンカーを置く。元リンクの表示文言を保存し、リンク先は移設後のファイル・アンカーに更新する。
- p・li・表のデータ tr をブロックとして数える。環境見出しと表の列見出しはブロック数に含めない。式だけの p も数える。保留本文と配置上の所見は [issues.md](issues.md) に置く。
- NB-W3 の出典は下表。文言・数式・Lean 名を保ち、元ページ名と見出しを追記する。表は一つのブロックとして主題の節に置く。表示式やコードにも元行のアンカーを付けた。本文のリンク先は凍結元を指す。所在を失った旧リンクは表示文言を残す。

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

## NB-W3 の分類

対象は未処理の HTML 37 ページ。節内で分かれる場合は元行で区切った。(a) は Kerodon 原稿へ転記、(b) は HTT・HA の照合先、(c) は読書経路・設計・実装一覧や応用の経路、(d) は転記済みの t 系の説明と重なる箇所。前文と章末の読書案内・要点も表に含む。

| 元ページ | 元の節・行 | 分類 | 対応・判断 |
| --- | --- | --- | --- |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 前文（17–24） | (c) | 配置・依存関係・読書順 |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 1. 基本の語彙：∞ 圏の符号化（29–43） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml)、[t-04-join-slice.html](#t-04-join-slicehtml)、[t-05-fibrations.html](#t-05-fibrationshtml)、[t-07-mapping-spaces.html](#t-07-mapping-spaceshtml)、[t-09-limits.html](#t-09-limitshtml)、[t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 1. 基本の語彙：∞ 圏の符号化 — 極限の定義（46–52） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml)、[t-04-join-slice.html](#t-04-join-slicehtml)、[t-05-fibrations.html](#t-05-fibrationshtml)、[t-07-mapping-spaces.html](#t-07-mapping-spaceshtml)、[t-09-limits.html](#t-09-limitshtml)、[t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 1. 基本の語彙：∞ 圏の符号化 — 写像空間（55–60） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml)、[t-04-join-slice.html](#t-04-join-slicehtml)、[t-05-fibrations.html](#t-05-fibrationshtml)、[t-07-mapping-spaces.html](#t-07-mapping-spaceshtml)、[t-09-limits.html](#t-09-limitshtml)、[t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 1. 基本の語彙：∞ 圏の符号化 — 同値（63–66） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml)、[t-04-join-slice.html](#t-04-join-slicehtml)、[t-05-fibrations.html](#t-05-fibrationshtml)、[t-07-mapping-spaces.html](#t-07-mapping-spaceshtml)、[t-09-limits.html](#t-09-limitshtml)、[t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 2. ディレクトリと層（71–89） | (c) | 本体の構成・状態・読書順 |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 2. ディレクトリと層 — 主要な定義の所在（92–105） | (c) | 本体の構成・状態・読書順 |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 3. 依存関係（109–138） | (c) | 本体の構成・状態・読書順 |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 4. 信頼性の状態（142–144） | (c) | 本体の構成・状態・読書順 |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 5. リファクタの候補（148–148） | (c) | 本体の構成・状態・読書順 |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | 6. この後の読み順（152–158） | (c) | 本体の構成・状態・読書順 |
| [00-map.html](../../../exposition/ja/infinity/00-map.html) | この章で押さえること（163–167） | (c) | 本体の構成・状態・読書順 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 前文（17–27） | (c) | 章の案内 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 1. quasicategory と fibration — 数学（33–41） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-05-fibrations.html](#t-05-fibrationshtml) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 1. quasicategory と fibration — 数学（42–46） | (a) | [4.1](4.1.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 1. quasicategory と fibration — 数学（49–55） | (c) | 実装の所在 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 2. ホモトピー圏 — 数学（62–67） | (a) | [1.4.5.7](1.4.5.7.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 2. ホモトピー圏 — Lean（70–80） | (c) | 実装の所在 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 2. ホモトピー圏 — Lean（81–81） | (a) | [1.4.5.7](1.4.5.7.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 2. ホモトピー圏 — Lean（84–85） | (c) | 実装の所在 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 2. ホモトピー圏 — Lean（87–88） | (a) | [1.4.5](1.4.5.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 3. 可逆な辺と Joyal の定理 — 数学（96–103） | (a) | [4.4.2.6](4.4.2.6.md)、[4.4.3](4.4.3.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 3. 可逆な辺と Joyal の定理 — Lean（107–116） | (c) | 実装の一覧 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 3. 可逆な辺と Joyal の定理 — 証明の方針（(1) ⇒ (2)）（119–132） | (a) | [4.4.2.6](4.4.2.6.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 4. join と slice — join の構成（138–154） | (d) | [t-04-join-slice.html](#t-04-join-slicehtml) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 4. join と slice — slice と普遍性（158–165） | (d) | [t-04-join-slice.html](#t-04-join-slicehtml) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 4. join と slice — slice と普遍性（166–166） | (a) | [4.3.5.13](4.3.5.13.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 4. join と slice — slice は quasicategory（Joyal の補題）（170–170） | (a) | [4.3.6.4](4.3.6.4.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 4. join と slice — slice は quasicategory（Joyal の補題）（171–171） | (d) | [t-04-join-slice.html](#t-04-join-slicehtml) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 4. join と slice — slice は quasicategory（Joyal の補題）（173–180） | (a) | [4.3.6](4.3.6.md)、[4.3.6.4](4.3.6.4.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 5. 終対象 — 定義（186–202） | (a) | [4.7.3.11](4.7.3.11.md)、[4.7.3](4.7.3.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 6. ∞ 圏の同値 — 定義（209–225） | (a) | [4.5.1.10](4.5.1.10.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 6. ∞ 圏の同値 — 基本的な性質（229–238） | (a) | [4.5.1](4.5.1.md) |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 6. ∞ 圏の同値 — 基本的な性質（241–242） | (c) | モデル構造を使わない方針 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 7. Core のファイル構成（この章の範囲）（247–256） | (c) | ファイル構成・候補・章の整理 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | 8. リファクタの候補（260–260） | (c) | ファイル構成・候補・章の整理 |
| [01-quasicategories.html](../../../exposition/ja/infinity/01-quasicategories.html) | この章で押さえること（264–268） | (c) | ファイル構成・候補・章の整理 |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 前文（17–23） | (c) | 章の案内 |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 1. 写像空間 — 定義（30–39） | (d) | [t-07-mapping-spaces.html](#t-07-mapping-spaceshtml) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 1. 写像空間 — 基本的な性質（42–53） | (a) | [4.6.5](4.6.5.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 1. 写像空間 — 左の写像空間と両者の比較（56–59） | (a) | [4.6.5.10](4.6.5.10.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 2. Kan 複体の言葉（63–80） | (d) | [t-05-fibrations.html](#t-05-fibrationshtml)、[t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 3. 終対象と写像空間（86–92） | (d) | [t-08-initial-terminal.html](#t-08-initial-terminalhtml) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 3. 終対象と写像空間（93–93） | (a) | [4.7.3.16](4.7.3.16.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 4. 充満忠実性と同値の判定 — 定義（99–104） | (d) | [t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 4. 充満忠実性と同値の判定 — 主定理（108–125） | (a) | [4.8.4.1](4.8.4.1.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 4. 充満忠実性と同値の判定 — 関連する結果（129–136） | (a) | [4.8](4.8.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 5. 極限 — 定義の復習と一意性（142–142） | (d) | [t-09-limits.html](#t-09-limitshtml) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 5. 極限 — 定義の復習と一意性（144–145） | (a) | [7.1.1](7.1.1.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 5. 極限 — 同値による保存（150–152） | (a) | [7.1.4.12](7.1.4.12.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 5. 極限 — 引き戻し（155–157） | (a) | [7.6.2](7.6.2.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 5. 極限 — 関手 ∞ 圏の極限は各点で計算できる（161–168） | (a) | [7.1.8.3](7.1.8.3.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 5. 極限 — 補助模型：fat join、lax slice、錐の族（171–182） | (a) | [4.6.2](4.6.2.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 5. 極限 — 通常の圏との整合性（186–186） | (a) | [7.6.1](7.6.1.md) |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 6. ファイル構成（この章の範囲）（190–199） | (c) | ファイル構成・候補・章の整理 |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | 7. リファクタの候補（203–203） | (c) | ファイル構成・候補・章の整理 |
| [02-mapping-limits.html](../../../exposition/ja/infinity/02-mapping-limits.html) | この章で押さえること（207–211） | (c) | ファイル構成・候補・章の整理 |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 前文（17–24） | (c) | 目標・案内 |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 1. cocartesian 辺と cocartesian fibration — 定義（30–37） | (a) | [5.1.1.1](5.1.1.1.md)、[5.1.4.1](5.1.4.1.md) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 1. cocartesian 辺と cocartesian fibration — transport（40–48） | (a) | [5.2.2](5.2.2.md) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 2. ∞ 圏を作る ∞ 圏：coherent nerve（53–56） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 2. ∞ 圏を作る ∞ 圏：coherent nerve（59–72） | (a) | [5.5.3](5.5.3.md) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 3. 主定理（空間値）（77–82） | (a) | [5.6](5.6.md) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 3. 主定理（空間値）（85–86） | (b) | HTT §2.2.1、Theorem 2.2.1.2 |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 4. 証明の経路（91–91） | (a) | [5.3.1](5.3.1.md) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 4. 証明の経路 — 第一段：底が通常の圏の nerve の場合（94–106） | (a) | [5.3.1](5.3.1.md) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 4. 証明の経路 — 第二段：一般の底への帰着（109–123） | (a) | [6.3.6.5](6.3.6.5.md)、[5.6](5.6.md) |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 4. 証明の経路 — 第二段：一般の底への帰着（126–134） | (c) | 本体の合成・Cat∞ 値の進捗と所在 |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 5. Cat∞ 値版（途中で止まっている）（139–146） | (c) | 本体の合成・Cat∞ 値の進捗と所在 |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 6. F1 の構成（この章の範囲）（150–163） | (c) | 本体の合成・Cat∞ 値の進捗と所在 |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | 7. リファクタの候補（167–167） | (c) | 本体の合成・Cat∞ 値の進捗と所在 |
| [03-straightening.html](../../../exposition/ja/infinity/03-straightening.html) | この章で押さえること（171–175） | (c) | 本体の合成・Cat∞ 値の進捗と所在 |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 前文（17–24） | (c) | 章の案内 |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 1. 前層 ∞ 圏（28–31） | (d) | [t-14-presheaves.html](#t-14-presheaveshtml) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 1. 前層 ∞ 圏（32–32） | (a) | [8.3.3](8.3.3.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 2. Hom 関手と Yoneda 埋め込み — 構成（38–49） | (d) | [t-12-mapping-functor.html](#t-12-mapping-functorhtml)、[t-14-presheaves.html](#t-14-presheaveshtml) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 2. Hom 関手と Yoneda 埋め込み — 主な結果（52–63） | (a) | [8.3.3.13](8.3.3.13.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 3. 随伴 — 定義（70–79） | (a) | [6.2.1.2](6.2.1.2.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 4. 局所化と反射的部分圏 — 局所化（85–88） | (a) | [6.3.1.9](6.3.1.9.md)、[6.3.1.13](6.3.1.13.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 4. 局所化と反射的部分圏 — 反射的部分圏（91–100） | (a) | [6.3.3](6.3.3.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 5. cofinality（104–117） | (a) | [7.2.1](7.2.1.md)、[7.2.1.1](7.2.1.1.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 6. Kan 拡張 — 定義：各点の条件（123–131） | (a) | [7.3.1.5](7.3.1.5.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 6. Kan 拡張 — 主な結果（134–142） | (a) | [7.3](7.3.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 6. Kan 拡張 — 証明の方針（存在）（145–145） | (a) | [7.3](7.3.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 7. 通常の圏論との整合（B5）（149–155） | (a) | [7.3](7.3.md) |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 8. ファイル構成（159–169） | (c) | ファイル構成・候補・章の整理 |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | 9. リファクタの候補（173–173） | (c) | ファイル構成・候補・章の整理 |
| [04-yoneda-adjunction-kan.html](../../../exposition/ja/infinity/04-yoneda-adjunction-kan.html) | この章で押さえること（177–181） | (c) | ファイル構成・候補・章の整理 |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 前文（17–26） | (c) | 橋の一覧と章の案内 |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 1. γ1：coherent nerve は quasicategory（31–37） | (d) | [t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 2. γ1.5：Dold–Kan 豊穣化と dg nerve（41–57） | (b) | HA §1.2.3・§1.3.1 |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 3. γ3：𝒮 の極限・余極限（62–62） | (a) | [7.4.1](7.4.1.md) |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 3. γ3：𝒮 の極限・余極限 — (a) 一般の coherent 図式：straightening 経由（無条件）（65–71） | (a) | [7.4.1](7.4.1.md) |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 3. γ3：𝒮 の極限・余極限 — (b) strict な図式：Bousfield–Kan 経由（74–82） | (a) | [7.5](7.5.md) |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 4. γ4：Quillen 随伴 ⇒ ∞ 随伴（86–93） | (b) | HTT §A.3.1–§A.3.2、HA §1.3.4 |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 5. ファイル構成（97–106） | (c) | ファイル構成・候補・章の整理 |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | 6. リファクタの候補（110–110） | (c) | ファイル構成・候補・章の整理 |
| [05-gamma-bridges.html](../../../exposition/ja/infinity/05-gamma-bridges.html) | この章で押さえること（114–117） | (c) | ファイル構成・候補・章の整理 |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 前文（17–29） | (c) | 前提と本体での位置 |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 1. Cat∞ の写像空間と極限（33–37） | (a) | [5.5.3](5.5.3.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 1. Cat∞ の写像空間と極限 — 引き戻しと lax pullback（40–47） | (a) | [4.6.4](4.6.4.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 2. filtered ∞ 圏と交換定理（51–60） | (a) | [9.1.1.4](9.1.1.4.md)、[9.1.5](9.1.5.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 3. Indκ(C) — 定義（65–67） | (a) | [9.3.1](9.3.1.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 3. Indκ(C) — 主な結果（70–77） | (a) | [9.3.1](9.3.1.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 4. κ-compact 対象（81–88） | (a) | [9.2.5](9.2.5.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 5. 冪等完備化（93–108） | (a) | [8.5](8.5.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 6. accessible と presentable（112–116） | (a) | [9.5.1](9.5.1.md) |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 7. 依存関係のまとめ（120–125） | (c) | 依存関係・実装・候補 |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 8. ファイル構成（129–136） | (c) | 依存関係・実装・候補 |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | 9. リファクタの候補（140–140） | (c) | 依存関係・実装・候補 |
| [06-catinfty-ind-presentable.html](../../../exposition/ja/infinity/06-catinfty-ind-presentable.html) | この章で押さえること（144–148） | (c) | 依存関係・実装・候補 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 前文（17–19） | (c) | 章の案内 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 1. 定義 — 零対象と fiber/cofiber（25–31） | (b) | HA §1.1.1–§1.1.4、Definition 1.1.1.9 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 1. 定義 — 安定性（HA Def. 1.1.1.9）（34–40） | (b) | HA §1.1.1–§1.1.4、Definition 1.1.1.9 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 1. 定義 — 判定と基本性質（43–49） | (b) | HA §1.1.1–§1.1.4、Definition 1.1.1.9 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 2. ホモトピー圏の三角構造（53–63） | (b) | HA §1.1.1–§1.1.4、Definition 1.1.1.9 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 2. ホモトピー圏の三角構造 — 長完全列（66–66） | (b) | HA §1.1.1–§1.1.4、Definition 1.1.1.9 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 3. 完全関手（70–77） | (b) | HA §1.1.1–§1.1.4、Definition 1.1.1.9 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 4. 作業中：Ω による安定性の判定（D-7）（82–86） | (c) | 進捗・使われ方・ファイル構成 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 5. 使われ方（91–94） | (c) | 進捗・使われ方・ファイル構成 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 6. ファイル構成（99–108） | (c) | 進捗・使われ方・ファイル構成 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | 7. リファクタの候補（112–112） | (c) | 進捗・使われ方・ファイル構成 |
| [07-stable.html](../../../exposition/ja/infinity/07-stable.html) | この章で押さえること（116–120） | (c) | 進捗・使われ方・ファイル構成 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 前文（17–27） | (c) | 章の案内と β 群の分担 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 1. dg nerve — 定義（HA Construction 1.3.1.6）（32–45） | (b) | HA §1.3.1、Construction 1.3.1.6 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 1. dg nerve — 主な性質（49–57） | (b) | HA §1.3.1、Construction 1.3.1.6 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 2. 導来 ∞ 圏 D(S) と Perf(S)（61–73） | (b) | HA §1.3.2・§7.1.2 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 3. Verdier 商（β3）（77–86） | (b) | HA §1.1.4 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 4. 非可換 dg 代数の導来 ∞ 圏と Morita 不変性（β5）（90–98） | (b) | HA §1.3.1・§7.1.2 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 5. 作業中：dg gluing と lax pullback（β4）（102–106） | (c) | dg gluing の進捗・ファイル構成 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 6. ファイル構成（111–120） | (c) | dg gluing の進捗・ファイル構成 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | 7. リファクタの候補（124–124） | (c) | dg gluing の進捗・ファイル構成 |
| [08-dgnerve-derived.html](../../../exposition/ja/infinity/08-dgnerve-derived.html) | この章で押さえること（128–132） | (c) | dg gluing の進捗・ファイル構成 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 前文（17–17） | (c) | 補章の案内 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 1. \(B\) とは何か（21–21） | (a) | [1.3.2](1.3.2.md) |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 1. \(B\) とは何か — 空間の場合（25–27） | (a) | [1.3.2](1.3.2.md) |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 1. \(B\) とは何か — \(B\) は torsor を分類する（31–34） | (b) | HTT §6.3.5・§7.1.6 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 1. \(B\) とは何か — 層（∞ トポス）の場合（37–51） | (b) | HTT §6.3.5・§7.1.6 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 2. 大域切断とは：\(\Gamma(B\mathbb Z)\) の例（55–68） | (c) | Frobenius を含む分類空間の大域切断の計算 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 3. 一般の群：自由ループ空間の公式 — 定数な離散群（74–85） | (c) | Frobenius を含む分類空間の大域切断の計算 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 3. 一般の群：自由ループ空間の公式 — Frobenius が非自明に作用する場合（88–97） | (c) | Frobenius を含む分類空間の大域切断の計算 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 3. 一般の群：自由ループ空間の公式 — 高次の群（100–100） | (c) | Frobenius を含む分類空間の大域切断の計算 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 4. 一般のエタール ∞ トポス：シェイプ（104–124） | (b) | HTT §7.1.6 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 5. 補章 8 §4.8 の三つの事実の出どころ（128–135） | (c) | 応用の典拠 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 6. 「空間」と「大域切断が連結」の意味 — 6.1 ここで言う空間（141–147） | (a) | [1.2.1](1.2.1.md) |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 6. 「空間」と「大域切断が連結」の意味 — 6.2 大域切断はなぜ空間か（150–156） | (b) | HTT §6.1・§7.1.6 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 6. 「空間」と「大域切断が連結」の意味 — 6.3 連結 ⇔ \(\pi_0\) がちょうど一点（159–165） | (a) | [1.2.1](1.2.1.md) |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 6. 「空間」と「大域切断が連結」の意味 — 6.4 連結は可縮より弱い・対象の連結性との違い（168–175） | (a) | [1.2.1](1.2.1.md) |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 7. \(\Gamma(B\mathbb Z)\) の連結性の ∞ 圏論的な証明（179–184） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 7. \(\Gamma(B\mathbb Z)\) の連結性の ∞ 圏論的な証明 — 7.1 副有限 = pro-π-有限なシェイプ（187–191） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 7. \(\Gamma(B\mathbb Z)\) の連結性の ∞ 圏論的な証明 — 7.2 π-有限な空間から \(S^1\) への写像は定数（195–196） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 7. \(\Gamma(B\mathbb Z)\) の連結性の ∞ 圏論的な証明 — 7.3 一行で（200–204） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション（208–208） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.0 出発点（211–211） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.1 底の構造：円周の上のファイブレーション（214–218） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.2 ファイバー上で \(\mathbb G_m\) が潰れる（221–227） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.3 付値で分解（230–230） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.4 単数の部分は消える（233–239） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.5 円周の上の \(B^2\mathbb Z\)：ここで \(\mathbb Q/\mathbb Z\) が出る（242–257） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.6 補足：2 次元のねじれたトーラス（260–260） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.7 \(\mathrm{Br}(K^{\mathrm{nr}})=0\) はどこまでホモトピー的に整理できるか（263–269） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.8 単数の部分と極限の扱い（272–279） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | 8. 局所体の Brauer 群：円周の上のファイブレーション — 8.9 Tate コホモロジーとノルムのホモトピー的な解釈（282–323） | (c) | 副有限化の数論への応用と Brauer 群 |
| [classifying-shape.html](../../../exposition/ja/infinity/classifying-shape.html) | この補章で押さえること（329–337） | (c) | 副有限化の数論への応用と Brauer 群 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 前文（17–19） | (c) | 補章の案内 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 1. 1 圏：Grothendieck opfibration（23–27） | (a) | [5.6.1](5.6.1.md) |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 2. ∞ 圏の定義（HTT Def. 2.4.2.1、Kerodon Def. 5.1.4.1）（31–37） | (a) | [5.1.4.1](5.1.4.1.md)、[5.1.1.1](5.1.1.1.md) |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 2. ∞ 圏の定義（HTT Def. 2.4.2.1、Kerodon Def. 5.1.4.1） — 外側のホーン \(\Lambda^n_0\) を使う理由（41–42） | (a) | [5.1.1](5.1.1.md) |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 2. ∞ 圏の定義（HTT Def. 2.4.2.1、Kerodon Def. 5.1.4.1） — 写像空間による言い換え（46–54） | (a) | [5.1.2](5.1.2.md) |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 3. marked 単体的集合での純粋なリフティング性質（HTT §3.1）（58–68） | (b) | HTT §3.1.1・§3.1.3 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 4. 他のファイブレーションとの比較（72–79） | (a) | [5.1.4](5.1.4.md) |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 5. 何のために必要か（83–83） | (c) | 選択の回避と六関手への応用 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 5. 何のために必要か — 関手を直接書くのは難しい（86–86） | (c) | 選択の回避と六関手への応用 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 5. 何のために必要か — 選択なしで fibration として生まれる構成（89–96） | (c) | 選択の回避と六関手への応用 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 5. 何のために必要か — 随伴（99–99） | (a) | [6.2.1](6.2.1.md) |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 5. 何のために必要か — ∞ 圏の極限・余極限（HTT §3.3）（102–108） | (b) | HTT §3.3 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | 5. 何のために必要か — 六関手形式での位置づけ（112–131） | (c) | 六関手への応用・補章の整理 |
| [cocartesian-definition.html](../../../exposition/ja/infinity/cocartesian-definition.html) | この補章で押さえること（137–141） | (c) | 六関手への応用・補章の整理 |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 前文（17–19） | (c) | 補章の案内 |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 1. 定義 — 出発点：普通のナーブ（25–25） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 1. 定義 — \(\mathfrak C[\Delta^n]\)（29–33） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 1. 定義 — ナーブ（36–39） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 1. 定義 — 低次元（42–48） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 1. 定義 — 基本定理と \(\mathcal S\)・\(\mathrm{Cat}_\infty\)（51–53） | (b) | HTT §2.2.5、Theorem 2.2.5.1 |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 1. 定義 — 基本定理と \(\mathcal S\)・\(\mathrm{Cat}_\infty\)（54–54） | (a) | [5.5.3](5.5.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 2. 普遍性（59–65） | (a) | [2.4.4](2.4.4.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 3. ホモトピー整合的図式 — 動機（71–71） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 3. ホモトピー整合的図式 — 定義（74–77） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 3. ホモトピー整合的図式 — 列 \([n]\) の場合（80–88） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 3. ホモトピー整合的図式 — 障害（91–91） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 3. ホモトピー整合的図式 — 厳密化定理（94–98） | (b) | HTT §4.2.4、Proposition 4.2.4.4 |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 4. 具体例 — 例 1：可換正方形と loop（104–115） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 4. 具体例 — 例 2：ホモトピー整合的な \(\mathbb Z/2\) 作用（119–130） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | 4. 具体例 — 例 3：持ち上がらないホモトピー可換図式（Toda 括弧）（133–158） | (a) | [2.4.3](2.4.3.md) |
| [coherent-nerve-diagrams.html](../../../exposition/ja/infinity/coherent-nerve-diagrams.html) | この補章で押さえること（164–167） | (c) | 補章の整理 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 前文（20–32） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 1. 符号化の前提（37–51） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 2. 今の配置（55–79） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 3. 数学の依存の順序（83–85） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 3. 数学の依存の順序 — 3.1 単体的集合の組合せ論が最初（88–89） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 3. 数学の依存の順序 — 3.2 quasicategory と空間の理論の順序（92–97） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 3. 数学の依存の順序 — 3.3 coherent nerve は空間の後（100–101） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 3. 数学の依存の順序 — 3.4 安定 ∞ 圏は presentable 性より前（104–105） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 3. 数学の依存の順序 — 3.5 安定 presentable は両方の後（108–108） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 4. ∞ 圏論の基盤に入れないもの（112–125） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 5. 主な宣言と所在（130–158） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 6. Verdier 商までの道筋（162–185） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | 7. 整備の工程（188–188） | (c) | 基盤の境界・依存順・整備工程 |
| [f-00-map.html](../../../exposition/ja/infinity/f-00-map.html) | この章で押さえること（192–195） | (c) | 基盤の境界・依存順・整備工程 |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 前文（20–33） | (c) | 章の案内 |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 1. 単体的集合の組合せ論（Simplicial） — 1.1 標準単体・境界・horn（39–46） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-05-fibrations.html](#t-05-fibrationshtml) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 1. 単体的集合の組合せ論（Simplicial） — 1.2 Kan 複体と quasicategory（49–64） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-05-fibrations.html](#t-05-fibrationshtml) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 1. 単体的集合の組合せ論（Simplicial） — 1.3 anodyne 射と inner anodyne 射（68–77） | (a) | [3.1.2](3.1.2.md)、[4.1.3](4.1.3.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 1. 単体的集合の組合せ論（Simplicial） — 1.4 分解と置き換え（81–89） | (a) | [3.1.8](3.1.8.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 1. 単体的集合の組合せ論（Simplicial） — 1.5 prism とホモトピー（92–94） | (a) | [3.1.5](3.1.5.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 1. 単体的集合の組合せ論（Simplicial） — 1.6 宇宙の持ち上げ（97–114） | (c) | 宇宙の実装と依存の境界 |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 2. 境目：Core に残る Kan の道具（119–130） | (c) | 宇宙の実装と依存の境界 |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 3. ホモトピー群（Kan） — 3.1 定義（136–142） | (a) | [3.2.2.4](3.2.2.4.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 3. ホモトピー群（Kan） — 3.2 写像、不変性、π_* 同型（146–148） | (a) | [3.2.2.4](3.2.2.4.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 3. ホモトピー群（Kan） — 3.3 Kan fibration の長完全列（152–158） | (a) | [3.2.6](3.2.6.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 3. ホモトピー群（Kan） — 3.4 Whitehead の定理（162–167） | (a) | [3.2.7.1](3.2.7.1.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 3. ホモトピー群（Kan） — 3.5 弱同値の三つの見方（170–177） | (a) | [3.2.7.2](3.2.7.2.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 4. 塔と lim¹（Kan）（181–190） | (a) | [7.6.5](7.6.5.md)、[7.6.5.11](7.6.5.11.md)、[保留](issues.md#nb-w3-の保留と転記上の所見) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 5. 基点付きの空間（195–205） | (a) | [5.5.2](5.5.2.md) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 6. 基本亜群と necklace（210–212） | (a) | [保留](issues.md#nb-w3-の保留と転記上の所見) |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | 7. 今の所在（まとめ）（217–227） | (c) | ファイルの所在と章の整理 |
| [f-01-simplicial-kan.html](../../../exposition/ja/infinity/f-01-simplicial-kan.html) | この章で押さえること（231–234） | (c) | ファイルの所在と章の整理 |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 前文（20–27） | (c) | モデル圏に依存しない構成を採る方針 |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 1. なぜモデル圏を避けるのか（33–42） | (c) | モデル圏に依存しない構成を採る方針 |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 2. 道具 1：small object argument と Kan 置換（48–57） | (a) | [3.1.8](3.1.8.md) |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 3. 道具 2：ホモトピーと anodyne 局所化 — 3.1 端点の包含は anodyne（63–65） | (a) | [3.1.2](3.1.2.md) |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 3. 道具 2：ホモトピーと anodyne 局所化 — 3.2 anodyne 局所化（68–73） | (a) | [3.1.7](3.1.7.md) |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 4. 弱同値の三つの見方が一致すること（78–99） | (a) | [3.2.7.2](3.2.7.2.md) |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 5. bisimplicial 集合の対角（105–112） | (b) | HTT §4.2.3・§A.2.9 |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 6. 本当にモデル圏が要るもの（117–129） | (c) | モデル圏に依存する範囲と整理の方針 |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | 7. いまの状態：付随的な依存とその切り方（133–133） | (c) | モデル圏に依存する範囲と整理の方針 |
| [f-02-model-free.html](../../../exposition/ja/infinity/f-02-model-free.html) | この章で押さえること（137–140） | (c) | モデル圏に依存する範囲と整理の方針 |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 前文（20–36） | (c) | 章の案内・Core の読み方 |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 1. Core の要点（40–48） | (c) | 章の案内・Core の読み方 |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 2. 局所化の定義（53–73） | (a) | [6.3.1.9](6.3.1.9.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 3. 存在：任意の辺の集合で局所化できる（81–88） | (a) | [6.3.2](6.3.2.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 3. 存在：任意の辺の集合で局所化できる — 3.1 段 1：可逆な辺の「歩く版」を作る（91–96） | (a) | [6.3.2.1](6.3.2.1.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 3. 存在：任意の辺の集合で局所化できる — 3.2 段 2：W の辺ごとに J を貼り付ける（99–109） | (a) | [6.3.2](6.3.2.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 3. 存在：任意の辺の集合で局所化できる — 3.3 段 3：quasicategory に置き換える（112–124） | (a) | [6.3.2](6.3.2.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 4. 普遍性からすぐ出ること（130–137） | (a) | [6.3.1](6.3.1.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 5. 判定法：与えられた関手が局所化であることを示す（141–150） | (a) | [6.3.1](6.3.1.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 6. Dwyer–Kan 局所化と Bousfield 局所化（154–162） | (a) | [6.3.3](6.3.3.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 7. hammock 局所化：写像空間を計算する（167–181） | (c) | Dwyer–Kan の hammock 模型と実装経路 |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 8. 局所化に関わる概念の整理（185–196） | (a) | [6.3](6.3.md) |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | 9. 今の所在（200–210） | (c) | 所在と章の整理 |
| [f-03-localization.html](../../../exposition/ja/infinity/f-03-localization.html) | この章で押さえること（214–217） | (c) | 所在と章の整理 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 前文（20–26） | (c) | 章の案内 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 1. 安定 ∞ 圏の基本 — 1.1 定義（32–49） | (b) | HA §1.1.1–§1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 1. 安定 ∞ 圏の基本 — 1.2 基本的な結果（52–59） | (b) | HA §1.1.1–§1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 1. 安定 ∞ 圏の基本 — 1.3 完全関手の ∞ 圏（62–66） | (b) | HA §1.1.1–§1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 2. 部分圏を零にすることと、cofiber 辺を可逆にすること（72–87） | (b) | HA §1.1.1–§1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 3. Verdier 列 — 3.1 定義（9 人論文による特徴づけ）（93–111） | (b) | HA §1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 3. Verdier 列 — 3.2 もう一つの定義：完全関手として普遍的な商（115–136） | (b) | HA §1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 3. Verdier 列 — 3.3 二つの形の関係（140–141） | (b) | HA §1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 4. 厚い部分圏（144–151） | (b) | HA §1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 5. 随伴による判定と半直交分解（157–168） | (b) | HA §1.1.4 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 6. 安定 ∞ 圏の ∞ 圏と局所化不変量（173–176） | (c) | 局所化不変量への適用・本体の例・所在 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 7. いまある Verdier 列の例（181–190） | (c) | 局所化不変量への適用・本体の例・所在 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | 8. 今の所在（194–207） | (c) | 局所化不変量への適用・本体の例・所在 |
| [f-04-stable-verdier.html](../../../exposition/ja/infinity/f-04-stable-verdier.html) | この章で押さえること（211–214） | (c) | 局所化不変量への適用・本体の例・所在 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 前文（20–32） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 1. 何が問題か（37–41） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 2. すでにあるもの：分数による写像空間の計算 — 2.1 ホモトピー圏の水準（48–56） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 2. すでにあるもの：分数による写像空間の計算 — 2.2 ∞ 圏の水準：写像空間を span で表す（60–73） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 3. 足りない定理（M1〜M11）（77–90） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 4. 二つの道 — 4.1 道 (A)：直接構成する（96–103） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 4. 二つの道 — 4.2 道 (B)：Ind を経由する（107–124） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 4. 二つの道 — 4.3 どちらを主路にするか（128–137） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 5. 商の関手性（M8）（141–155） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 6. 進める順序（160–160） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | 7. 今の所在（163–170） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-05-verdier-quotient.html](../../../exposition/ja/infinity/f-05-verdier-quotient.html) | この章で押さえること（174–177） | (c) | Verdier 商の実装・不足定理・選択肢 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 前文（20–35） | (c) | 章の案内 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 1. 何を分類するか（40–48） | (d) | [t-05-fibrations.html](#t-05-fibrationshtml)、[t-11-straightening.html](#t-11-straighteninghtml) |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 1. 何を分類するか（49–49） | (a) | [5.2.2.20](5.2.2.20.md) |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 1. 何を分類するか（50–53） | (d) | [t-05-fibrations.html](#t-05-fibrationshtml)、[t-11-straightening.html](#t-11-straighteninghtml) |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 2. 空間値版の主経路（完成）（57–76） | (a) | [5.6](5.6.md) |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 3. Kerodon の方法との比較（80–96） | (a) | [5.6](5.6.md) |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 4. Cat∞ 値版の現状と、一般の底に必要なもの（100–113） | (c) | Cat∞ 値の不足・工事経路と選択 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 5. 証明方法の比較（モデル圏なし・模型そのまま）（117–128） | (c) | Cat∞ 値の不足・工事経路と選択 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 6. 普遍 cocartesian fibration \(\mathcal Z\) — 6.1 定義と役割（134–137） | (a) | [5.5.5](5.5.5.md) |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 6. 普遍 cocartesian fibration \(\mathcal Z\) — 6.2 難しさ（140–140） | (c) | 定義の実装上の難しさ |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 6. 普遍 cocartesian fibration \(\mathcal Z\) — 6.3 Kerodon の構成：\(f\) を 2 射に置く（142–142） | (a) | [5.5.5.8](5.5.5.8.md) |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 6. 普遍 cocartesian fibration \(\mathcal Z\) — 6.4 構成案：点を表現可能な右 fibration で表す（144–169） | (c) | 構成案・計画の典拠・六関手での利用 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 7. 計画の典拠（174–176） | (c) | 構成案・計画の典拠・六関手での利用 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 8. Cat∞ 値の関手がどこで要るか（181–186） | (c) | 構成案・計画の典拠・六関手での利用 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 8. Cat∞ 値の関手がどこで要るか — 8.1 基礎理論の中（188–198） | (c) | 構成案・計画の典拠・六関手での利用 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 8. Cat∞ 値の関手がどこで要るか — 8.2 六関手形式の中（200–200） | (c) | 構成案・計画の典拠・六関手での利用 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | 9. presentable の状況と \(\mathrm{Pr}^L\) のモノイダル構造（204–224） | (b) | HTT §5.5、HA §4.8.1 |
| [f-06-straightening.html](../../../exposition/ja/infinity/f-06-straightening.html) | この章で押さえること（230–234） | (c) | 章の整理 |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 前文（20–23） | (c) | 章の案内 |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 1. 始対象と写像空間（27–28） | (d) | [t-08-initial-terminal.html](#t-08-initial-terminalhtml) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 1. 始対象と写像空間 — 写像空間の定義と比較（30–39） | (a) | [4.6.5](4.6.5.md) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 1. 始対象と写像空間 — Lurie の定義との同値と一意性（43–45） | (a) | [4.7.3](4.7.3.md) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 2. スライスと join の補題（50–59） | (d) | [t-04-join-slice.html](#t-04-join-slicehtml) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 2. スライスと join の補題 — スライスが quasicategory であること（61–76） | (a) | [4.3.6.4](4.3.6.4.md)、[4.3.6](4.3.6.md) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 3. 単体の見方：結合律と五角形（80–122） | (a) | [2.4.3](2.4.3.md) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 3. 単体の見方：結合律と五角形 — 3 次元を経由した見方（124–124） | (a) | [2.4.3](2.4.3.md) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 3. 単体の見方：結合律と五角形 — 写像空間の立方体と horn（126–150） | (a) | [2.4.3](2.4.3.md) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 4. 極限・随伴・随伴関手定理（156–166） | (a) | [7.1.3](7.1.3.md) |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | 5. 基礎の枠組み（170–178） | (c) | 基盤の見取り図と章の整理 |
| [f-a-basics.html](../../../exposition/ja/infinity/f-a-basics.html) | この章で押さえること（182–185） | (c) | 基盤の見取り図と章の整理 |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 前文（20–23） | (c) | 文献の使い分けと章立ての対照 |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 1. Kerodon と HTT の章立て — Kerodon（28–42） | (c) | 文献の使い分けと章立ての対照 |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 1. Kerodon と HTT の章立て — HTT（44–58） | (c) | 文献の使い分けと章立ての対照 |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 2. Kerodon 第 7 章の内容（63–82） | (a) | [7.1](7.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 3. cofinality（86–92） | (a) | [7.2](7.2.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 4. Kan 拡張の位置づけ — 4.1 二つの役割（99–100） | (a) | [7.3](7.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 4. Kan 拡張の位置づけ — 4.2 この先の定義で使う場面（103–111） | (a) | [7.3](7.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 4. Kan 拡張の位置づけ — 4.3 「すべては Kan 拡張」（113–121） | (a) | [7.3](7.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 4. Kan 拡張の位置づけ — 4.4 一点への Kan 拡張（123–123） | (a) | [7.3](7.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 5. ホモトピー極限（Kerodon 7.5）（128–131） | (a) | [7.5](7.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 6. Yoneda の補題 — 6.1 二つの形（137–141） | (d) | [t-10-fibration-yoneda.html](#t-10-fibration-yonedahtml)、[t-15-yoneda.html](#t-15-yonedahtml) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 6. Yoneda の補題 — 6.2 fibration 版の意味（144–152） | (d) | [t-10-fibration-yoneda.html](#t-10-fibration-yonedahtml)、[t-15-yoneda.html](#t-15-yonedahtml) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 6. Yoneda の補題 — 6.3 証明の部品（156–170） | (a) | [8.3.3](8.3.3.md)、[4.2.5](4.2.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 6. Yoneda の補題 — 6.4 関手版（173–182） | (a) | [8.3.3](8.3.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 7. 部品 A・B の詳しい証明 — 7.1 部品 A：\(\mathrm{id}_b\) は \(B_{b/}\) の始対象（188–200） | (a) | [4.7.3](4.7.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 7. 部品 A・B の詳しい証明 — 7.2 部品 B：始対象の包含は left anodyne（retract による証明）（204–209） | (a) | [4.2.5](4.2.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 7. 部品 A・B の詳しい証明 — 7.3 他の証明（212–218） | (a) | [4.2.5](4.2.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 7. 部品 A・B の詳しい証明 — 7.4 持ち上げ性質による証明（221–236） | (a) | [4.2.5](4.2.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 8. 前層と、写像空間の相対関手空間としての読み替え — 8.1 前層の二つの定義（242–249） | (a) | [5.6.6](5.6.6.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 8. 前層と、写像空間の相対関手空間としての読み替え — 8.2 主張（252–253） | (a) | [5.6.6](5.6.6.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 8. 前層と、写像空間の相対関手空間としての読み替え — 8.3 両辺の中身と橋渡し（257–269） | (a) | [5.6.6](5.6.6.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 8. 前層と、写像空間の相対関手空間としての読み替え — 8.4 読み替えの役割（272–279） | (a) | [5.6.6](5.6.6.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.1 straightening のおさらい（285–285） | (d) | [t-11-straightening.html](#t-11-straighteninghtml) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.2 なぜ素朴には関手にならないか（288–288） | (a) | [5.3.1](5.3.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.3 St の第一段：底が普通の圏の脈体 \(N(C)\)（291–297） | (a) | [5.3.1](5.3.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.4 相対関手空間 \(\mathrm{Fun}_{/S}(K,X)\)（301–303） | (a) | [5.3.1](5.3.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.5 St の第二段：一般の quasicategory の底（307–313） | (a) | [6.3.6.5](6.3.6.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.6 局所化（先に用意するもの）（316–316） | (a) | [6.3.6.5](6.3.6.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.7 \(\mathrm{fv}\) が局所化であることの証明（319–327） | (a) | [6.3.6.5](6.3.6.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.8 \(h_y\) の定義と、スライスとの比較（331–348） | (a) | [5.6.6](5.6.6.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 9. straightening の構成と \(h_y\) の関手性 — 9.9 全体の流れ：fibration 版 Yoneda → St → Map → 関手版 Yoneda（352–357） | (a) | [8.3.3](8.3.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 10. fibration 版 Yoneda の証明の確認 — 10.1 設定（365–369） | (a) | [4.2.5.4](4.2.5.4.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 10. fibration 版 Yoneda の証明の確認 — 10.2 相対関手空間の普遍性による書き直し（373–383） | (a) | [4.2.5.4](4.2.5.4.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 10. fibration 版 Yoneda の証明の確認 — 10.3 pushout-product で \(i\) に帰着（386–386） | (a) | [4.2.5.4](4.2.5.4.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 10. fibration 版 Yoneda の証明の確認 — 10.4 \(i\) が left anodyne：縮約を式で書く（389–400） | (a) | [4.2.5](4.2.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 10. fibration 版 Yoneda の証明の確認 — 10.5 一般の始対象と left anodyne（403–409） | (a) | [4.2.5](4.2.5.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 11. 極限の同値な定義と、その使いどころ — 11.1 定義の一覧（414–426） | (a) | [7.1.3](7.1.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 11. 極限の同値な定義と、その使いどころ — 11.2 (1)(2)(3) の正確な形（430–433） | (a) | [7.1.3](7.1.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 11. 極限の同値な定義と、その使いどころ — 11.3 補題（437–442） | (a) | [7.1.3](7.1.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 11. 極限の同値な定義と、その使いどころ — 11.4 (1) ⇔ (2)（445–445） | (a) | [7.1.3](7.1.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 11. 極限の同値な定義と、その使いどころ — 11.5 (2) ⇔ (3)（449–453） | (a) | [7.1.3](7.1.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 11. 極限の同値な定義と、その使いどころ — 11.6 (3) の使いどころ（456–471） | (a) | [7.1.3](7.1.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 11. 極限の同値な定義と、その使いどころ — 11.7 Kerodon の順番（随伴 → 極限 → Yoneda）の依存関係（474–474） | (a) | [7.1.3](7.1.3.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 12. 随伴の同値な定義と、その使いどころ — 12.1 定義の一覧（479–488） | (a) | [6.2.1](6.2.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 12. 随伴の同値な定義と、その使いどころ — 12.2 同値性の筋道（491–501） | (a) | [6.2.1](6.2.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 12. 随伴の同値な定義と、その使いどころ — 12.3 自然性はどこにあるか（505–510） | (a) | [6.2.1](6.2.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 12. 随伴の同値な定義と、その使いどころ — 12.4 それぞれの使い道（513–521） | (a) | [6.2.1](6.2.1.md) |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | 13. 基礎として残るもの（join・スライス・fibration・随伴・Yoneda・極限の先）（525–534） | (c) | 基礎理論の依存関係と章の整理 |
| [f-b-literature-yoneda.html](../../../exposition/ja/infinity/f-b-literature-yoneda.html) | この章で押さえること（538–549） | (c) | 基礎理論の依存関係と章の整理 |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 前文（20–23） | (c) | 章の案内・論証の順序 |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 1. 流れ（28–35） | (c) | 章の案内・論証の順序 |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 2. 単体的圏と \(\mathcal Kan\)（40–44） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 3. \(\mathfrak C[\Delta^n]\) と一般の \(\mathfrak C\) — 3.1 定義（49–56） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 3. \(\mathfrak C[\Delta^n]\) と一般の \(\mathfrak C\) — 3.2 一般の \(K\)（59–66） | (a) | [2.4.4](2.4.4.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 4. \(N^{hc}\) と quasicategory 性 — 4.1 低次元の単体（72–75） | (a) | [2.4.3](2.4.3.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 4. \(N^{hc}\) と quasicategory 性 — 4.2 定理：局所 Kan なら quasicategory（HTT 1.1.5.10、Kerodon 2.4.5.1）（80–84） | (d) | [t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 4. \(N^{hc}\) と quasicategory 性 — 4.3 局所 Kan でないと失敗する例（87–87） | (a) | [2.4.5](2.4.5.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 5. \(\mathcal S\) と \(\mathrm{Cat}_\infty\)（91–101） | (a) | [5.5.3](5.5.3.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 6. \(\mathcal S\) の他の定義との比較（106–113） | (a) | [3.1.6](3.1.6.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 7. 写像空間の比較定理 — 7.1 主張と \(\mathrm{Hom}^L\) の具体形（118–121） | (a) | [4.6.7.5](4.6.7.5.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 7. 写像空間の比較定理 — 7.2 比較写像と素朴な方針の難点（124–124） | (a) | [4.6.7.5](4.6.7.5.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 8. Kerodon 4.6.7 の証明（モデル圏なし）（128–138） | (a) | [4.6.7.5](4.6.7.5.md)、[4.6.7.23](4.6.7.23.md)、[4.6.7.8](4.6.7.8.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 9. 形式化での証明（142–166） | (a) | [4.6.7](4.6.7.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 10. 局所 Kan でない場合に止まる場所（170–180） | (a) | [4.6.7.8](4.6.7.8.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.1 方針（186–192） | (d) | [t-11-straightening.html](#t-11-straighteninghtml)、[t-12-mapping-functor.html](#t-12-mapping-functorhtml) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.2 単体的集合の反対（195–206） | (d) | [t-11-straightening.html](#t-11-straighteninghtml)、[t-12-mapping-functor.html](#t-12-mapping-functorhtml) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.3 \(\mathrm{Tw}(C)\) の定義（209–215） | (d) | [t-11-straightening.html](#t-11-straighteninghtml)、[t-12-mapping-functor.html](#t-12-mapping-functorhtml) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.4 \(n=0,1,2\) の計算（219–230） | (a) | [8.1.1.2](8.1.1.2.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.5 左 fibration であること：持ち上げの計算（233–240） | (a) | [8.1.1.11](8.1.1.11.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.6 ファイバーの計算（244–257） | (a) | [8.1.1](8.1.1.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.7 straighten する（260–266） | (d) | [t-11-straightening.html](#t-11-straighteninghtml)、[t-12-mapping-functor.html](#t-12-mapping-functorhtml) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.8 残りの比較（270–277） | (a) | [8.1.2](8.1.2.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | 11. \(\mathrm{Map}\) を関手にする：twisted arrow の straightening — 11.9 他の作り方との比較（280–294） | (a) | [8.1.2](8.1.2.md) |
| [f-c-spaces.html](../../../exposition/ja/infinity/f-c-spaces.html) | この章で押さえること（298–303） | (c) | 章の整理 |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 前文（20–23） | (c) | 章の案内 |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 1. 随伴関手定理の主張と骨格（27–35） | (a) | [9.5.2](9.5.2.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 2. 必要な部品（40–59） | (a) | [9.5.2](9.5.2.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 3. 左随伴の側だけアクセシブル性が要る理由（63–63） | (a) | [9.5.2](9.5.2.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 3. 左随伴の側だけアクセシブル性が要る理由 — 3.1 1 の向きで条件が要らない理由（65–65） | (a) | [9.5.2](9.5.2.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 3. 左随伴の側だけアクセシブル性が要る理由 — 3.2 2 の向きでアクセシブル性が効く場所（67–83） | (a) | [9.5.2](9.5.2.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 4. 表現可能性定理（87–87） | (a) | [9.5.1](9.5.1.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 4. 表現可能性定理 — 4.1 用語（89–96） | (a) | [9.5.1](9.5.1.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 4. 表現可能性定理 — 4.2 二つの向きの役割（100–103） | (a) | [9.5.1](9.5.1.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 4. 表現可能性定理 — 4.3 証明（106–122） | (a) | [9.5.1.8](9.5.1.8.md) |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 5. 形式化の状況（F2/Presentable、約 700 ファイル） — 5.1 随伴関手定理（128–133） | (c) | 実装・進捗・章の整理 |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | 5. 形式化の状況（F2/Presentable、約 700 ファイル） — 5.2 \(\mathrm{Pr}^L\)（136–151） | (c) | 実装・進捗・章の整理 |
| [f-d-adjoint-presentable.html](../../../exposition/ja/infinity/f-d-adjoint-presentable.html) | この章で押さえること（156–159） | (c) | 実装・進捗・章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 前文（17–19） | (c) | 補章の案内 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 1. 擬関手 — 定義（25–41） | (a) | [5.6.1](5.6.1.md) |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 1. 擬関手 — 1 圏と ∞ 圏：どこで等式になるか（44–51） | (a) | [5.6.1](5.6.1.md) |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 1. 擬関手 — 整合性の処理の三通り（54–59） | (a) | [5.6.1](5.6.1.md) |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 2. 厳密にすると何が困るか（64–69） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 3. ファイバー圏（SGA1 Exposé VI） — 3.1 定義（75–75） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 3. ファイバー圏（SGA1 Exposé VI） — 3.2 擬関手との対応（78–82） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 3. ファイバー圏（SGA1 Exposé VI） — 3.3 例（85–90） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 3. ファイバー圏（SGA1 Exposé VI） — 3.4 2-米田（93–96） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 4. 降下（SGA1 Exposé VI・VIII） — 4.1 降下データ（102–103） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 4. 降下（SGA1 Exposé VI・VIII） — 4.2 篩からの cartesian 関手（106–110） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 4. 降下（SGA1 Exposé VI・VIII） — 4.3 極限としての言い換えと切り詰めの階層（113–120） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 4. 降下（SGA1 Exposé VI・VIII） — 4.4 Beck–Chevalley とモナド性（123–123） | (c) | SGA1 の降下と通常のファイバー圏を使う経路 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 5. ∞ への接続（127–141） | (b) | HTT §3.2・§6.1.3 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 6. 擬関手と lax 関手の使い分け（145–151） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 6. 擬関手と lax 関手の使い分け — 擬関手の使い道（154–154） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 6. 擬関手と lax 関手の使い分け — lax 関手の使い道（158–163） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 7. 具体例：群の表現 — 7.1 擬関手としての記述（テンソル積モデル）（169–175） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 7. 具体例：群の表現 — 7.2 Grothendieck 構成（178–190） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 7. 具体例：群の表現 — 7.3 選択なしの記述（193–193） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 7. 具体例：群の表現 — 7.4 誘導表現と Frobenius 相互律（196–200） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | 7. 具体例：群の表現 — 7.5 ∞ 版：∞ 群と \(\mathrm{Fun}(BG,D(k))\)（203–244） | (c) | lax 関手と表現論の応用、補章の整理 |
| [fibered-descent.html](../../../exposition/ja/infinity/fibered-descent.html) | この補章で押さえること（250–255） | (c) | lax 関手と表現論の応用、補章の整理 |
| [index.html](../../../exposition/ja/infinity/index.html) | 前文（15–15） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 目標：∞ 圏の解説動画（18–29） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 I 部 旧シリーズ（ディレクトリ単位） — 章（34–56） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 I 部 旧シリーズ（ディレクトリ単位） — 読書ルート（61–64） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 I 部 旧シリーズ（ディレクトリ単位） — 設計ノート（69–69） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 I 部 旧シリーズ（ディレクトリ単位） — リファクタ記録（73–73） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 I 部 旧シリーズ（ディレクトリ単位） — 各章の書き方（77–81） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 II 部 整備後の ∞ 圏基盤（2026-10-28〜）（86–89） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 II 部 整備後の ∞ 圏基盤（2026-10-28〜） — この部の書き方（93–97） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 II 部 整備後の ∞ 圏基盤（2026-10-28〜） — 章（101–114） | (c) | 目次と三部の読書案内 |
| [index.html](../../../exposition/ja/infinity/index.html) | 第 III 部（仮） — 章（118–135） | (c) | 目次と三部の読書案内 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 前文（17–17） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 1. 作りたいもの（21–35） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 1. 作りたいもの — なぜ ∞ 関手でなければならないか（38–43） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 2. 登場する ∞ 圏（47–55） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 3. 何が起きたか：dg 側だけで組む設計の破綻 — 当初の設計（62–70） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 3. 何が起きたか：dg 側だけで組む設計の破綻 — D-S が Lean で示した三つの反例（73–78） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 3. 何が起きたか：dg 側だけで組む設計の破綻 — 根本原因（82–84） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 4. 新しい設計（2026-10-27 11:55）（89–102） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 5. 形式化の状況 — ∞ 側（109–119） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 5. 形式化の状況 — dg 側の対応物（122–129） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 6. dg と安定 ∞ 圏の関係の書き方 — (1) ∞ 関手 ν（完成）（135–142） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 6. dg と安定 ∞ 圏の関係の書き方 — (2) 構成ごとの比較（145–154） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 7. 新しい設計で必要な作業（159–163） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 8. 前提：このリポジトリでの ∞ 関手の作り方（167–173） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 9. \(K_\infty\colon\) StableInfinity → Sp（178–196） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 9. \(K_\infty\colon\) StableInfinity → Sp — 作り方（方法 (a)）（201–204） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 9. \(K_\infty\colon\) StableInfinity → Sp — 難しいところ（208–209） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 10. \(\Sigma_\infty\colon\) StableInfinity → StableInfinity — 作り方（215–222） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 10. \(\Sigma_\infty\colon\) StableInfinity → StableInfinity — 難しいところ（226–229） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 11. 共通の難しさ：Knc∞ が局所化不変量であること（234–243） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | 12. まとめ（見立て）（248–261） | (c) | 非連結 K の設計と反例・実装の記録 |
| [k-nonconnective-design.html](../../../exposition/ja/infinity/k-nonconnective-design.html) | このページで押さえること（267–272） | (c) | 非連結 K の設計と反例・実装の記録 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 前文（17–19） | (c) | 補章の案内 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 1. 対称モノイダル ∞ 圏の定義（24–40） | (b) | HA §2.1.1–§2.1.2・§2.4.3 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 1. 対称モノイダル ∞ 圏の定義 — ∞ operad と表現可能性（43–46） | (b) | HA §2.1.1–§2.1.2・§2.4.3 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 2. \(\mathrm{Pr}^L\) のテンソル積（51–59） | (b) | HA §4.8.1 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 2. \(\mathrm{Pr}^L\) のテンソル積 — 構成（63–73） | (b) | HA §4.8.1 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 2. \(\mathrm{Pr}^L\) のテンソル積 — 例（77–83） | (b) | HA §4.8.1 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 2. \(\mathrm{Pr}^L\) のテンソル積 — 基本的な性質（86–94） | (b) | HA §4.8.1 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 3. 代数と加群（99–109） | (b) | HA §3.1・§3.3 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 4. 六関手形式での使われ方（115–117） | (c) | 六関手への利用 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | 5. 1 圏との比較（122–142） | (b) | HA §2.1・§4.8.1 |
| [monoidal-prl.html](../../../exposition/ja/infinity/monoidal-prl.html) | この補章で押さえること（148–151） | (c) | 補章の整理 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 前文（17–19） | (c) | 六関手形式からの依存順 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 1. 基礎理論の地図（六関手形式を目標とする場合）（24–39） | (c) | 六関手形式からの依存順 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 2. 随伴関手定理（44–52） | (a) | [9.5.2.1](9.5.2.1.md)、[9.5.1.8](9.5.1.8.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 2. 随伴関手定理（54–63） | (c) | 六関手の例と要件 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 3. \(\mathcal P(A)\) とは何か（68–84） | (a) | [8.3.3](8.3.3.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 4. \(\mathcal P(A)\) の普遍性（89–105） | (a) | [8.4.3](8.4.3.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 4. \(\mathcal P(A)\) の普遍性 — 証明の流れ（110–128） | (a) | [8.4.3](8.4.3.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 5. 表現可能性定理の証明（133–133） | (a) | [9.5.1.8](9.5.1.8.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 5. 表現可能性定理の証明 — 準備（137–138） | (a) | [9.5.1.8](9.5.1.8.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 5. 表現可能性定理の証明 — 段階 I：\(\mathcal C=\mathcal P(A)\)（142–146） | (a) | [9.5.1.8](9.5.1.8.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 5. 表現可能性定理の証明 — 段階 II：一般の \(\mathcal C\)（150–154） | (a) | [9.5.1.8](9.5.1.8.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 5. 表現可能性定理の証明 — ∞ 圏で何が変わるか（157–164） | (a) | [9.5.1.8](9.5.1.8.md) |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 6. Gabriel–Ulmer と Lurie–Simpson（169–169） | (b) | HTT §5.3–§5.5 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 6. Gabriel–Ulmer と Lurie–Simpson — 主張（172–186） | (b) | HTT §5.3–§5.5 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 6. Gabriel–Ulmer と Lurie–Simpson — 証明の核：nerve の充満忠実性（190–205） | (b) | HTT §5.3–§5.5 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 6. Gabriel–Ulmer と Lurie–Simpson — ∞ 圏で何が変わるか（208–217） | (b) | HTT §5.3–§5.5 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | 6. Gabriel–Ulmer と Lurie–Simpson — 全体の流れ（220–238） | (c) | 読書経路と補章の整理 |
| [presentable-route.html](../../../exposition/ja/infinity/presentable-route.html) | この補章で押さえること（244–248） | (c) | 読書経路と補章の整理 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 前文（17–19） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 1. 表現論での使われ方 — 1.1 古典的な定理が関手性と基底変換の系になる（25–43） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 1. 表現論での使われ方 — 1.2 三角圏では扱いにくく、∞ 圏で本質的に楽になる問題（47–49） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 1. 表現論での使われ方 — 1.3 幾何学的・数論的表現論（54–55） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成（60–60） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.0 設定（63–63） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.1 道具立て：Tate 構成（66–80） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.2 数論的入力：類構造の公理（残る）（83–86） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.3 基本類（90–90） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.4 Tate の定理の ∞ 版（93–97） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.5 相互写像（101–104） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.6 \(K^{\mathrm{ab}}\) へ（107–107） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 2. 局所類体論の再構成 — 2.7 切り分け（110–119） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 3. Clausen の K 理論的アプローチ（123–123） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 3. Clausen の K 理論的アプローチ — 3.1 何をしているか（126–135） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 3. Clausen の K 理論的アプローチ — 3.2 相互律：Eilenberg swindle（138–138） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 3. Clausen の K 理論的アプローチ — 3.3 §2 との比較（141–148） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 3. Clausen の K 理論的アプローチ — 3.4 何が残っているか（論文自身の記述）（152–156） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか（161–161） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.1 Brauer 群は Mod の捻れた形（164–168） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.2 不変量写像の分解（171–180） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.3 向きとしての基本類（183–183） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.4 導来代数幾何で Brauer 群の計算は簡単になるか（186–211） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.5 例：有限体の Brauer 群が自明なことの導来的な証明（214–253） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.6 別証明：ホモトピー群もコホモロジーも取らずに降下データを直接分類する（256–273） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.7 もっと抽象的に：円周上の捻れた形は \(\pi_0\mathrm{Aut}\) しか見ない（276–297） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | 4. 基本類の存在は整理できるか — 4.8 Postnikov 分解の議論を抽象論で書く（300–347） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [rep-cft.html](../../../exposition/ja/infinity/rep-cft.html) | この補章で押さえること（353–361） | (c) | 表現論・局所類体論と Brauer 群を整理する応用経路 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 前文（17–17） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 1. 目標から逆算する：三つのレベル（21–38） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 2. \(\mathrm{Pr}^L\) はどこで必要か（42–49） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 3. \(\mathrm{Corr}(\mathcal C,E)\) の定義 — 3.1 入力と 1 圏的な姿（55–56） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 3. \(\mathrm{Corr}(\mathcal C,E)\) の定義 — 3.2 単体的集合としての定義（59–67） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 3. \(\mathrm{Corr}(\mathcal C,E)\) の定義 — 3.3 準圏であることの証明の筋（71–73） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 3. \(\mathrm{Corr}(\mathcal C,E)\) の定義 — 3.4 対称モノイダル構造は抽象論から出る（78–93） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 4. 定義に必要なものの一覧（97–107） | (c) | 六関手の入力と Corr の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 5. まず \(\mathrm{Cat}_\infty\) とその対称モノイダル構造（111–119） | (a) | [5.5.3](5.5.3.md) |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 5. まず \(\mathrm{Cat}_\infty\) とその対称モノイダル構造 — 5.1 段 1 の詳細：\(\mathfrak C[\Delta^n]\) は単体的圏、\(N^{hc}\) は単体的集合（122–154） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml)、[t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 6. \(\mathrm{QCat}^\Delta\) の記号と core の有無（158–158） | (a) | [5.5.3](5.5.3.md) |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 6. \(\mathrm{QCat}^\Delta\) の記号と core の有無 — 6.1 上付きの \(\Delta\)（161–167） | (a) | [5.5.3](5.5.3.md) |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 6. \(\mathrm{QCat}^\Delta\) の記号と core の有無 — 6.2 \(\mathrm{Cat}_\infty\) の射と写像空間（171–174） | (a) | [5.5.3](5.5.3.md) |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 6. \(\mathrm{QCat}^\Delta\) の記号と core の有無 — 6.3 core を取るかどうか（178–187） | (a) | [5.5.3](5.5.3.md) |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 7. \(\mathrm{Cat}_\infty\) の対称モノイダル構造（191–191） | (b) | HA §2.4.1・§2.4.3 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 7. \(\mathrm{Cat}_\infty\) の対称モノイダル構造 — 7.1 有限積（194–194） | (b) | HA §2.4.1・§2.4.3 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 7. \(\mathrm{Cat}_\infty\) の対称モノイダル構造 — 7.2 一般的な構成 \(\mathcal C^\times\)（197–208） | (b) | HA §2.4.1・§2.4.3 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 7. \(\mathrm{Cat}_\infty\) の対称モノイダル構造 — 7.3 cartesian 構造への lax 関手：六関手の定義への接続（211–222） | (b) | HA §2.4.1・§2.4.3 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 7. \(\mathrm{Cat}_\infty\) の対称モノイダル構造 — 7.4 lax 関手への普遍性：何のために要るか、詳しい形（225–253） | (b) | HA §2.4.1・§2.4.3 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 8. (c) \(\mathrm{Corr}(\mathcal C,E)\) の定義と準圏性 — 8.0 入力（259–259） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 8. (c) \(\mathrm{Corr}(\mathcal C,E)\) の定義と準圏性 — 8.1 添字の半順序集合（262–267） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 8. (c) \(\mathrm{Corr}(\mathcal C,E)\) の定義と準圏性 — 8.2 条件と言い換え（270–275） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 8. (c) \(\mathrm{Corr}(\mathcal C,E)\) の定義と準圏性 — 8.3 単体的集合であること（278–287） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 8. (c) \(\mathrm{Corr}(\mathcal C,E)\) の定義と準圏性 — 8.4 定理：\(\mathrm{Corr}(\mathcal C,E)\) は準圏（290–315） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 9. (d) \(\mathrm{Corr}(\mathcal C,E)\) の対称モノイダル構造（319–319） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 9. (d) \(\mathrm{Corr}(\mathcal C,E)\) の対称モノイダル構造 — 9.1 注意：§7 の cartesian 構造は使えない（322–322） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 9. (d) \(\mathrm{Corr}(\mathcal C,E)\) の対称モノイダル構造 — 9.2 抽象的な構成（三段）（326–330） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 9. (d) \(\mathrm{Corr}(\mathcal C,E)\) の対称モノイダル構造 — 9.3 技術的な一段：厳密な関手から ∞ 関手へ（333–339） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 9. (d) \(\mathrm{Corr}(\mathcal C,E)\) の対称モノイダル構造 — 9.4 結果の具体的な姿（342–358） | (c) | Corr の構成と準圏性・モノイダル構造の設計 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 10. (e) ∞ operad と lax 関手の正確な定義（362–362） | (b) | HA §2.1.1–§2.1.2、Definition 2.1.1.10・2.1.2.7 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 10. (e) ∞ operad と lax 関手の正確な定義 — 10.1 \(\mathrm{Fin}_*\) の二種類の射（365–370） | (b) | HA §2.1.1–§2.1.2、Definition 2.1.1.10・2.1.2.7 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 10. (e) ∞ operad と lax 関手の正確な定義 — 10.2 ∞ operad（HA Def. 2.1.1.10）（373–379） | (b) | HA §2.1.1–§2.1.2、Definition 2.1.1.10・2.1.2.7 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 10. (e) ∞ operad と lax 関手の正確な定義 — 10.3 対称モノイダル ∞ 圏との関係（382–382） | (b) | HA §2.1.1–§2.1.2、Definition 2.1.1.10・2.1.2.7 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 10. (e) ∞ operad と lax 関手の正確な定義 — 10.4 lax 関手（HA Def. 2.1.2.7）（385–385） | (b) | HA §2.1.1–§2.1.2、Definition 2.1.1.10・2.1.2.7 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 10. (e) ∞ operad と lax 関手の正確な定義 — 10.5 lax の構造写像の取り出し方（389–409） | (b) | HA §2.1.1–§2.1.2、Definition 2.1.1.10・2.1.2.7 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 11. (f) 随伴 — 11.0 六関手形式で何が要るか（415–421） | (c) | 六関手で用いる随伴 |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 11. (f) 随伴 — 11.1 定義の三つの形（424–437） | (a) | [6.2.1](6.2.1.md) |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 11. (f) 随伴 — 11.2 定義に必要なのは (i) だけ（440–440） | (c) | 六関手での要件とページのまとめ |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 11. (f) 随伴 — 11.3 定義の後で使う性質（参考）（444–447） | (c) | 六関手での要件とページのまとめ |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | 12. 全体のまとめ：六関手形式の定義（453–477） | (c) | 六関手での要件とページのまとめ |
| [route-6ff-definition.html](../../../exposition/ja/infinity/route-6ff-definition.html) | この章で押さえること（483–488） | (c) | 六関手での要件とページのまとめ |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 前文（17–17） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 1. 一般論の地図 — 1.1 ∞ トポスの一般論（議論の土台）（23–31） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 1. 一般論の地図 — 1.2 シェイプと副有限ホモトピー型（34–42） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 1. 一般論の地図 — 1.3 降下と捻れた形（45–51） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 1. 一般論の地図 — 1.4 群作用、ノルム、Tate 構成（54–60） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 1. 一般論の地図 — 1.5 安定 ∞ 圏とスペクトル系列・1.6 モノイダル構造・1.7 双対性と六関手（63–75） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 2. 主要な三文献 — 2.1 Hoyois「Higher Galois theory」（arXiv:1506.07155）（81–90） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 2. 主要な三文献 — 2.2 Nikolaus–Scholze「On topological cyclic homology」（Acta Math. 221, arXiv:1707.01799）（93–99） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 2. 主要な三文献 — 2.3 Antieau–Gepner「Brauer groups and étale cohomology in derived algebraic geometry」（Geom. Topol. 18, arXiv:1210.0290）（102–111） | (c) | 数論への文献ルート・読む順序 |
| [route-arith.html](../../../exposition/ja/infinity/route-arith.html) | 3. 読む順序（116–126） | (c) | 数論への文献ルート・読む順序 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 前文（17–17） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 0. 左 fibration と cocartesian fibration の意義（21–21） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 0. 左 fibration と cocartesian fibration の意義 — 0.1 関手を書く代わりのもの（24–24） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 0. 左 fibration と cocartesian fibration の意義 — 0.2 1 圏や位相幾何での類似（27–35） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 0. 左 fibration と cocartesian fibration の意義 — 0.3 基本的な対象が最初から fibration として現れる（38–46） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 0. 左 fibration と cocartesian fibration の意義 — 0.4 極限・余極限、cofinality（49–49） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 0. 左 fibration と cocartesian fibration の意義 — 0.5 理論の組み立ての中での位置（52–52） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 0. 左 fibration と cocartesian fibration の意義 — 0.6 左と cocartesian の違い（55–62） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 1. 目標と道筋（66–81） | (c) | 分類定理を目標にした読書経路・依存関係 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 2. 段 0：単体的集合とホーン — 2.1（0.1）単体的集合（86–95） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-05-fibrations.html](#t-05-fibrationshtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 2. 段 0：単体的集合とホーン — 2.2（0.2）ホーンの持ち上げ（98–128） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-05-fibrations.html](#t-05-fibrationshtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 2. 段 0：単体的集合とホーン — 2.3（0.2 補足）普遍性をホーン型の拡張条件として述べる（131–154） | (a) | [4.7.3](4.7.3.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 2. 段 0：単体的集合とホーン — 2.4（0.3）Kan 複体と準圏（156–186） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-05-fibrations.html](#t-05-fibrationshtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 2. 段 0：単体的集合とホーン — 2.5（0.4）持ち上げ性質と fibration の言葉（188–229） | (d) | [t-01-definitions.html](#t-01-definitionshtml)、[t-05-fibrations.html](#t-05-fibrationshtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 2. 段 0：単体的集合とホーン — 2.6（0.5）アノダイン写像（231–276） | (a) | [3.1.2](3.1.2.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏（279–289） | (c) | 段1の読む順序 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.1（1.1）関手の ∞ 圏 \(\mathrm{Fun}(K,\mathcal C)\) の中身（292–308） | (d) | [t-02-kan-category.html](#t-02-kan-categoryhtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.2（1.2）同値な辺と Joyal の定理（311–372） | (a) | [4.4.2.6](4.4.2.6.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.3（1.3）core \(\mathcal C^{\simeq}\)（375–402） | (a) | [4.4.3](4.4.3.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.4（1.4）写像空間 \(\mathrm{Map}_{\mathcal C}(x,y)\)（406–413） | (d) | [t-07-mapping-spaces.html](#t-07-mapping-spaceshtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.4（1.4）写像空間 \(\mathrm{Map}_{\mathcal C}(x,y)\)（414–436） | (a) | [4.6](4.6.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.4（1.4）写像空間 \(\mathrm{Map}_{\mathcal C}(x,y)\)（437–447） | (d) | [t-07-mapping-spaces.html](#t-07-mapping-spaceshtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.5（1.5）自然同値は各点で判定できる（450–470） | (a) | [4.4.4](4.4.4.md)、[4.4.4.4](4.4.4.4.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.6（1.6）∞ 圏の同値（473–476） | (d) | [t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.6（1.6）∞ 圏の同値（477–496） | (a) | [4.8.4.1](4.8.4.1.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 3. 段 1：写像空間・同値・関手の ∞ 圏 — 3.6（1.6）∞ 圏の同値（498–498） | (d) | [t-13-homotopy-equivalence.html](#t-13-homotopy-equivalencehtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 4. 段 2：左 fibration（501–510） | (c) | 段2の読む順序 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 4. 段 2：左 fibration — 4.1（2.1）定義と例、\(\mathrm{LFib}(B)\)（513–559） | (d) | [t-05-fibrations.html](#t-05-fibrationshtml)、[t-11-straightening.html](#t-11-straighteninghtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 4. 段 2：左 fibration — 4.2（2.2）fiber は Kan 複体、全ての辺は cocartesian（562–584） | (a) | [5.2](5.2.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 4. 段 2：左 fibration — 4.3（2.3）輸送 \(u_!\colon E_b\to E_{b'}\)（587–606） | (a) | [5.2](5.2.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 4. 段 2：左 fibration — 4.4（2.4）安定性（609–614） | (a) | [5.2](5.2.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 4. 段 2：左 fibration — 4.5（2.5）fiber ごとの同値の判定（617–638） | (a) | [5.1.6](5.1.6.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 4. 段 2：左 fibration — 4.6（2.6）\(\Delta^1\) 上の左 fibration（写像柱）（641–659） | (a) | [5.2.4](5.2.4.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 5. 段 3：\(\mathcal S=N^{hc}(\mathrm{Kan})\) と写像空間の比較定理（662–672） | (c) | 段3の読む順序 |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 5. 段 3：\(\mathcal S=N^{hc}(\mathrm{Kan})\) と写像空間の比較定理 — 5.1（3.1）\(N^{hc}\) の復習と、準圏であること（675–685） | (d) | [t-03-coherent-nerve.html](#t-03-coherent-nervehtml) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 5. 段 3：\(\mathcal S=N^{hc}(\mathrm{Kan})\) と写像空間の比較定理 — 5.2（3.2）低い次元の単体と \(h\mathcal S\)（688–699） | (a) | [2.4.3](2.4.3.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 5. 段 3：\(\mathcal S=N^{hc}(\mathrm{Kan})\) と写像空間の比較定理 — 5.3（3.3）写像空間の比較定理（702–711） | (a) | [4.6.7.5](4.6.7.5.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 5. 段 3：\(\mathcal S=N^{hc}(\mathrm{Kan})\) と写像空間の比較定理 — 5.4（3.4）\(\mathcal S\) の写像空間と合成（714–725） | (a) | [4.6.7](4.6.7.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 5. 段 3：\(\mathcal S=N^{hc}(\mathrm{Kan})\) と写像空間の比較定理 — 5.5（3.5）\(\mathrm{Cat}_\infty\) の場合（728–740） | (a) | [5.5.3](5.5.3.md) |
| [route-classification.html](../../../exposition/ja/infinity/route-classification.html) | 5. 段 3：\(\mathcal S=N^{hc}(\mathrm{Kan})\) と写像空間の比較定理 — 5.6（3.6）大きさ（宇宙）の扱い（743–758） | (a) | [5.5.3](5.5.3.md) |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 前文（24–24） | (c) | 米田補題までの読書経路 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 1. 目標（29–43） | (c) | 米田補題までの読書経路 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 2. 証明の本体：四つの同値の合成（47–66） | (a) | [8.3.3](8.3.3.md) |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 2. 証明の本体：四つの同値の合成 — h₃ の中身（70–83） | (a) | [8.3.3](8.3.3.md) |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 3. 依存の全体像（87–103） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 1 quasicategory の基本 第 1 章（111–112） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 2 写像空間と自明 Kan fibration 第 2 章 §1〜2（117–118） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 3 左 fibration と相対関手空間 第 1 章 §1、第 3 章 §4、第 4 章 §5（123–131） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 4 𝒮、関手 ∞ 圏、前層 第 3 章 §2、第 4 章 §1、第 5 章 §1（136–136） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 5 straightening の構成 第 3 章 §4一回目は黒箱（141–147） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 6 unstraightening 第 3 章、補章（152–157） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 7 twisted arrow と Hom 関手 第 4 章 §2（163–165） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 8 Yoneda の補題 §2（171–171） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 4. 段ごとの読み方 — 段 9（発展） Yoneda 埋め込みは充満忠実 第 4 章 §2（176–176） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 5. 進め方（182–184） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 7. straightening を使わない Yoneda（189–196） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 7. straightening を使わない Yoneda — 関手版で straightening が要る理由（199–209） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | 6. この道で見つかったリファクタの候補（214–214） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [route-yoneda.html](../../../exposition/ja/infinity/route-yoneda.html) | この道で押さえること（218–220） | (c) | 依存関係・読書順・別経路の比較・候補 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | 前文（13–13） | (c) | 六関手の基盤の概観 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | straightening/unstraightening と、極限・余極限・随伴（15–15） | (c) | 六関手の基盤の概観 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | straightening/unstraightening と、極限・余極限・随伴 — 三段階の対応（17–24） | (c) | 六関手の基盤の概観 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | straightening/unstraightening と、極限・余極限・随伴 — 極限と余極限（27–32） | (c) | 六関手の基盤の概観 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | straightening/unstraightening と、極限・余極限・随伴 — 降下（35–36） | (c) | 六関手の基盤の概観 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | straightening/unstraightening と、極限・余極限・随伴 — 随伴（38–43） | (c) | 六関手の基盤の概観 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | ∞-オペラドと対称モノイダル構造（45–50） | (b) | HA §2.1–§2.4 |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | 局所化（53–53） | (a) | [6.3.1](6.3.1.md) |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | 局所化 — 定義と1-圏との比較（55–59） | (a) | [6.3.1](6.3.1.md) |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | 局所化 — 二種類の局所化（62–67） | (a) | [6.3.1](6.3.1.md) |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | 局所化 — 判定法（70–72） | (a) | [6.3.1](6.3.1.md) |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | 局所化 — 余極限との関係（76–78） | (a) | [6.3.1](6.3.1.md) |
| [sixff-foundations.html](../../../exposition/ja/infinity/sixff-foundations.html) | 局所化 — 形式化の設計（82–86） | (c) | 形式化の設計 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 前文（17–19） | (c) | 補章の案内 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 1. スペクトルの ∞ 圏 — 定義：安定化（25–28） | (b) | HA §1.4.2–§1.4.3 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 1. スペクトルの ∞ 圏 — 普遍性（32–34） | (b) | HA §1.4.2–§1.4.3 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 1. スペクトルの ∞ 圏 — 内在的に展開できるもの（38–45） | (b) | HA §1.4.2–§1.4.3 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 2. 連結 K 理論 I：\(S_\bullet\) 構成（51–54） | (c) | S 構成・スパンを K 理論に用いる経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 2. 連結 K 理論 I：\(S_\bullet\) 構成 — Step 1：\(S_n\mathcal C\) は安定 ∞ 圏（57–62） | (c) | S 構成・スパンを K 理論に用いる経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 2. 連結 K 理論 I：\(S_\bullet\) 構成 — Step 2：単体的構造（65–65） | (c) | S 構成・スパンを K 理論に用いる経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 2. 連結 K 理論 I：\(S_\bullet\) 構成 — Step 3：core（68–68） | (c) | S 構成・スパンを K 理論に用いる経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 2. 連結 K 理論 I：\(S_\bullet\) 構成 — Step 4：実現 ＝ \(\Delta^{\mathrm{op}}\) 上の余極限（71–80） | (c) | S 構成・スパンを K 理論に用いる経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 2. 連結 K 理論 I：\(S_\bullet\) 構成 — スペクトル化（83–83） | (c) | S 構成・スパンを K 理論に用いる経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 3. ナーブ型の構成：\(\mathfrak C[\Delta^n]\)・\(\mathrm{Ar}[n]\)・スパン（87–97） | (c) | S 構成・スパンを K 理論に用いる経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 4. 連結 K 理論 II：群完備化（102–104） | (b) | HA §5.2.6・§1.4.3 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 4. 連結 K 理論 II：群完備化 — Step 1：\(E_\infty\) 空間（107–107） | (b) | HA §5.2.6・§1.4.3 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 4. 連結 K 理論 II：群完備化 — Step 2：群完備化 ＝ bar 構成の実現のループ（110–113） | (b) | HA §5.2.6・§1.4.3 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 4. 連結 K 理論 II：群完備化 — Step 3：\(\mathrm{CMon}^{\mathrm{gp}}(\mathcal S)\simeq\mathrm{Sp}_{\ge0}\)（116–116） | (b) | HA §5.2.6・§1.4.3 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 4. 連結 K 理論 II：群完備化 — \(S_\bullet\) との比較（119–119） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 5. 加法性定理（123–123） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 5. 加法性定理 — 主張（同値な三つの形）（127–129） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 5. 加法性定理 — (A) ⇔ (B)（133–133） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 5. 加法性定理 — 使い道：\(\Omega\) スペクトルになること（137–140） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 5. 加法性定理 — 証明そのもの（144–144） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 6. 非連結 K 理論 — なぜ必要か（150–150） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 6. 非連結 K 理論 — 構成：Calkin 圏（154–156） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 6. 非連結 K 理論 — 連結版との関係（161–164） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 6. 非連結 K 理論 — 独立に定義できるか・復元できるか（169–172） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 6. 非連結 K 理論 — 原典確認：BGT の該当箇所（2026-10-27 追記）（176–194） | (c) | K 理論の比較、加法性、非連結化と局所化不変量 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商（201–204） | (b) | HA §1.1.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記）（208–208） | (b) | HA §1.1.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — 前提（211–215） | (b) | HA §1.1.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — Verdier 列（219–224） | (b) | HA §1.1.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — Karoubi 列（227–228） | (b) | HA §1.1.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — 違いが重要になる理由（232–235） | (b) | HA §1.1.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 形式化の状況（2026-10-28 調査、基準コミット cbb891432）（239–239） | (c) | 形式化の状況と今後の構成 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 形式化の状況（2026-10-28 調査、基準コミット cbb891432） — 定義：二つある（242–250） | (c) | 形式化の状況と今後の構成 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 形式化の状況（2026-10-28 調査、基準コミット cbb891432） — 例として示されている Verdier 列（255–258） | (c) | 形式化の状況と今後の構成 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 7. ∞ 圏的な Verdier 商 — 形式化の状況（2026-10-28 調査、基準コミット cbb891432） — Verdier 商を一般に作るのに必要な部品（262–284） | (c) | 形式化の状況と今後の構成 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 8. DG 圏の K 理論との比較 — dg nerve（HA §1.3.1）（291–298） | (b) | HA §1.3.1–§1.3.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 8. DG 圏の K 理論との比較 — 二つの定義（302–308） | (b) | HA §1.3.1–§1.3.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 8. DG 圏の K 理論との比較 — 可換な三角形（311–318） | (b) | HA §1.3.1–§1.3.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 8. DG 圏の K 理論との比較 — 普遍性による証明（323–336） | (b) | HA §1.3.1–§1.3.4 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | この補章で押さえること（342–346） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 形式化との対応（351–351） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 形式化との対応 — 全体の印象（354–354） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 形式化との対応 — 節ごとの対応（357–371） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較（376–376） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較 — 対象と版（379–385） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較 — 9 人論文（389–396） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較 — Barwick（401–406） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較 — Efimov（411–414） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較 — Lurie 281（419–423） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較 — 比較（427–436） | (c) | 整理・実装状況・後継文献の経路 |
| [spectra-k-theory.html](../../../exposition/ja/infinity/spectra-k-theory.html) | 付録 2 後継文献の比較 — このプロジェクトにとっての結論（440–444） | (c) | 整理・実装状況・後継文献の経路 |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 前文（17–24） | (c) | 三段の対応による読み方 |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 1. 三段の並び（30–39） | (c) | 三段の対応による読み方 |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 1. 三段の並び — 集合の場合（42–45） | (c) | 三段の対応による読み方 |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 2. 「点付き」の三つの版（50–60） | (a) | [5.5.2](5.5.2.md) |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 2. 「点付き」の三つの版 — 引き戻しの定義（64–65） | (a) | [5.5.2](5.5.2.md) |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 3. Un は関手で、Hom を保つ（71–75） | (a) | [5.6.2](5.6.2.md) |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 3. Un は関手で、Hom を保つ — 射への作用は \(B\times[1]\) 上の引き戻しと輸送（79–79） | (a) | [5.6.2](5.6.2.md) |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 3. Un は関手で、Hom を保つ — Hom の比較はエンドになる（82–92） | (a) | [5.6.2](5.6.2.md) |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 4. straightening（97–118） | (a) | [5.6](5.6.md) |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 5. Yoneda を使わない道（123–131） | (c) | 別証明の選択肢と補章の整理 |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 5. Yoneda を使わない道 — 方法 A：単体ごとに作って貼り合わせる（135–140） | (c) | 別証明の選択肢と補章の整理 |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | 5. Yoneda を使わない道 — 方法 B：普遍 fibration を直接正当化する（univalence）（144–165） | (c) | 別証明の選択肢と補章の整理 |
| [unstraightening-analogy.html](../../../exposition/ja/infinity/unstraightening-analogy.html) | この補章で押さえること（171–174） | (c) | 別証明の選択肢と補章の整理 |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 前文（17–31） | (c) | 補章の案内 |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 1. 普遍左 fibration \(\mathcal S_*\to\mathcal S\)（35–40） | (a) | [5.5.2.2](5.5.2.2.md)、[5.5.2.1](5.5.2.1.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 1. 普遍左 fibration \(\mathcal S_*\to\mathcal S\) — fiber は空間そのもの（43–52） | (a) | [5.5.2.2](5.5.2.2.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 2. 定義：引き戻し（56–77） | (a) | [5.6.2.9](5.6.2.9.md)、[5.6.2.5](5.6.2.5.md)、[5.6.2](5.6.2.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 3. 宇宙と小ささ（82–87） | (a) | [5.6.2](5.6.2.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 4. 変換への作用（91–107） | (a) | [5.6.2](5.6.2.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 5. 写像空間の比較（Yoneda の h₁）（112–116） | (a) | [5.6.6](5.6.6.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 5. 写像空間の比較（Yoneda の h₁） — 比較写像 \(M\) の作り方（120–120） | (a) | [5.6.6](5.6.6.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 5. 写像空間の比較（Yoneda の h₁） — 同値性の証明：普遍的な族から逆を作る（123–140） | (a) | [5.6.6](5.6.6.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 5. 写像空間の比較（Yoneda の h₁） — 可逆性の保存と反映（143–143） | (a) | [5.6.6](5.6.6.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 6. strict な図式との比較（147–153） | (a) | [5.3.3.1](5.3.3.1.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 7. straightening との関係（157–164） | (a) | [5.6](5.6.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 7. straightening との関係 — どこで使われるか（169–171） | (a) | [5.6](5.6.md) |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | 8. ファイル構成（176–186） | (c) | 実装の所在と補章の整理 |
| [unstraightening.html](../../../exposition/ja/infinity/unstraightening.html) | この補章で押さえること（190–194） | (c) | 実装の所在と補章の整理 |


## NB-W3 の段落の行き先

(a) の各ブロックと保留を元ページ順に記録した。

### 01-quasicategories.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 42 / `nbw3-01-quasicategories-l42` | `これらのホーン族が生成する「左側のクラス」（llp(rlp(·))）を、それぞれ inner／右／左 anodyne` | [4.1](4.1.md#nbw3-01-quasicategories-l42) |
| 43 / `nbw3-01-quasicategories-l43` | `inductive rightHornInclusions : MorphismProperty SSet.{u} ` | [4.1](4.1.md#nbw3-01-quasicategories-l43) |
| 62 / `nbw3-01-quasicategories-l62` | `quasicategory \(X\) のホモトピー圏 \(hX\) には、よく知られた構成が二つある。` | [1.4.5.7](1.4.5.7.md#nbw3-01-quasicategories-l62) |
| 64 / `nbw3-01-quasicategories-l64` | `(a) 道の商：頂点を対象とし、辺の道で生成した自由圏を 2 単体の関係（\(d_1\sigma\sim d_0\s` | [1.4.5.7](1.4.5.7.md#nbw3-01-quasicategories-l64) |
| 65 / `nbw3-01-quasicategories-l65` | `(b) 辺のホモトピー類：射を、辺の「ホモトピー類」とする（Boardman–Vogt、HTT §1.2.3）。合成` | [1.4.5.7](1.4.5.7.md#nbw3-01-quasicategories-l65) |
| 67 / `nbw3-01-quasicategories-l67` | `quasicategory では二つが一致する（HTT §1.2.3、Kerodon §1.4.5）。` | [1.4.5.7](1.4.5.7.md#nbw3-01-quasicategories-l67) |
| 81 / `nbw3-01-quasicategories-l81` | `証明の方針：(a) → (b) は自由圏の普遍性で辺を類に送る関手として作る。(b) → (a) は「左ホモトピック` | [1.4.5.7](1.4.5.7.md#nbw3-01-quasicategories-l81) |
| 87 / `nbw3-01-quasicategories-l87` | `homotopyCategory_homMk_surjective：\(hX\) の射は 1 本の辺で表せる。` | [1.4.5](1.4.5.md#nbw3-01-quasicategories-l87) |
| 88 / `nbw3-01-quasicategories-l88` | `compStruct_nonempty_of_homMk_fac：\(hX\) での合成の等式は実際の合成 2 単体` | [1.4.5](1.4.5.md#nbw3-01-quasicategories-l88) |
| 96 / `nbw3-01-quasicategories-l96` | `辺 \(e\colon x\to y\) が可逆とは、\(hX\) で同型になることをいう。Joyal の定理（HT` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l96) |
| 98 / `nbw3-01-quasicategories-l98` | `定理. quasicategory \(X\) の辺 \(e\) について次は同値。` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l98) |
| 100 / `nbw3-01-quasicategories-l100` | `\(e\) は可逆。` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l100) |
| 101 / `nbw3-01-quasicategories-l101` | `最後の辺が \(e\) であるような任意の \(\Lambda^{n}_{n}\to X\)（\(n\ge 2\)）` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l101) |
| 103 / `nbw3-01-quasicategories-l103` | `最初の辺と \(\Lambda^n_0\) についても同様。系：quasicategory \(X\) が Kan ` | [4.4.3](4.4.3.md#nbw3-01-quasicategories-l103) |
| 119 / `nbw3-01-quasicategories-l119` | `鍵は、外側ホーンを join で書き直すことである（finalHornJoinIso、Core/OuterHornJ` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l119) |
| 120 / `nbw3-01-quasicategories-l120` | `\[ \Lambda^{n+2}_{n+2}\;\cong\;(\partial\Delta^n\star\Delt` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l120) |
| 123 / `nbw3-01-quasicategories-l123` | `ここで \(\Lambda^1_1=\{1\}\) であり、右因子 \(\Delta^1\) が問題の最後の辺 \(` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l123) |
| 124 / `nbw3-01-quasicategories-l124` | `\[ \begin{array}{ccc} \{1\} & \longrightarrow & X_{\sigma/` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l124) |
| 131 / `nbw3-01-quasicategories-l131` | `ここで \(\sigma\) は最初の \(n+1\) 頂点が張る単体である。§4 の結果から \(q\) は左 f` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l131) |
| 132 / `nbw3-01-quasicategories-l132` | `(2) ⇒ (1) では、2 次元のホーンで片側の逆を作り、3 次元のホーンで同じ辺が反対側の逆にもなることを示す。` | [4.4.2.6](4.4.2.6.md#nbw3-01-quasicategories-l132) |
| 166 / `nbw3-01-quasicategories-l166` | `sliceOverEquiv が「\(A\to X_{/p}\) は \(A\star K\to X\) と同じ」と` | [4.3.5.13](4.3.5.13.md#nbw3-01-quasicategories-l166) |
| 170 / `nbw3-01-quasicategories-l170` | `命題（HTT Lemma 2.1.2.3、Kerodon Prop. 4.3.6.4）. \(A_0\hookrig` | [4.3.6.4](4.3.6.4.md#nbw3-01-quasicategories-l170) |
| 173 / `nbw3-01-quasicategories-l173` | `内容Lean場所 生成ホーンの場合の計算joinUnion_rightHorn_boundary_innerAnod` | [4.3.6](4.3.6.md#nbw3-01-quasicategories-l173) |
| 180 / `nbw3-01-quasicategories-l180` | `証明の方針：生成元 \(\Lambda^p_i\hookrightarrow\Delta^p\)（\(0<i\)）と` | [4.3.6.4](4.3.6.4.md#nbw3-01-quasicategories-l180) |
| 186 / `nbw3-01-quasicategories-l186` | `頂点 \(x\) が終対象とは、最後の頂点が \(x\) である任意の \(\partial\Delta^{n+1}` | [4.7.3.11](4.7.3.11.md#nbw3-01-quasicategories-l186) |
| 187 / `nbw3-01-quasicategories-l187` | `def IsTerminalVertex {X : SSet.{u}} (x : X _⦋0⦌) : Prop :=` | [4.7.3.11](4.7.3.11.md#nbw3-01-quasicategories-l187) |
| 192 / `nbw3-01-quasicategories-l192` | `内容Lean場所 \(x\) が終対象 ⇔ \(X_{/x}\to X\) が trivial Kan fibrat` | [4.7.3](4.7.3.md#nbw3-01-quasicategories-l192) |
| 198 / `nbw3-01-quasicategories-l198` | `第 0 章で見たように、極限 IsLimitCone は slice の終対象として定義されるので、この節の結果はそ` | [4.7.3](4.7.3.md#nbw3-01-quasicategories-l198) |
| 201 / `nbw3-01-quasicategories-l201` | `原典との違い` | [4.7.3](4.7.3.md#nbw3-01-quasicategories-l201) |
| 202 / `nbw3-01-quasicategories-l202` | `HTT Def. 1.2.12.1 は「任意の \(y\) について \(\mathrm{Map}(y,x)\) が` | [4.7.3.11](4.7.3.11.md#nbw3-01-quasicategories-l202) |
| 209 / `nbw3-01-quasicategories-l209` | `Kerodon Def. 4.5.1.10 に従い、\(F\colon X\to Y\) が同値であるとは、\(G\` | [4.5.1.10](4.5.1.10.md#nbw3-01-quasicategories-l209) |
| 210 / `nbw3-01-quasicategories-l210` | `abbrev FunctorIso {X Y : SSet.{u}} (f g : X ⟶ Y) := (SSet.` | [4.5.1.10](4.5.1.10.md#nbw3-01-quasicategories-l210) |
| 224 / `nbw3-01-quasicategories-l224` | `注意：FunctorIso は頂点ごとの同型の族ではない` | [4.5.1.10](4.5.1.10.md#nbw3-01-quasicategories-l224) |
| 225 / `nbw3-01-quasicategories-l225` | `FunctorIso f g は関手 ∞ 圏 \(\mathrm{Fun}(X,Y)\) のホモトピー圏での同型であ` | [4.5.1.10](4.5.1.10.md#nbw3-01-quasicategories-l225) |
| 229 / `nbw3-01-quasicategories-l229` | `内容Lean場所 反射律・対称律・推移律QCatEquivalence.refl／symm／transCore/Eq` | [4.5.1](4.5.1.md#nbw3-01-quasicategories-l229) |
| 238 / `nbw3-01-quasicategories-l238` | `最後の項目の方針：\(i\colon A\to B\) が inner anodyne なら、制限 \(\mathr` | [4.5.1](4.5.1.md#nbw3-01-quasicategories-l238) |

### 02-mapping-limits.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 42 / `nbw3-02-mapping-limits-l42` | `内容Lean場所 頂点 = \(x\) から \(y\) への辺PinchedHom.vertexEquivPinc` | [4.6.5](4.6.5.md#nbw3-02-mapping-limits-l42) |
| 53 / `nbw3-02-mapping-limits-l53` | `Kan 性の証明の方針：\(\mathrm{Hom}^R(x,y)\) の右ホーン \(\Lambda^{n+1}_` | [4.6.5](4.6.5.md#nbw3-02-mapping-limits-l53) |
| 56 / `nbw3-02-mapping-limits-l56` | `左 pinched 写像空間 \(\mathrm{Hom}^L(x,y)\) は、反対圏の右写像空間の反対として定義` | [4.6.5.10](4.6.5.10.md#nbw3-02-mapping-limits-l56) |
| 57 / `nbw3-02-mapping-limits-l57` | `def pinchedHomLeft {X : SSet.{u}} (x y : X _⦋0⦌) : SSet.{u` | [4.6.5.10](4.6.5.10.md#nbw3-02-mapping-limits-l57) |
| 59 / `nbw3-02-mapping-limits-l59` | `Kan 性と \(\pi_0\) の計算は、反対圏を通して右の場合から導かれる（Core/MappingSpaceL` | [4.6.5.10](4.6.5.10.md#nbw3-02-mapping-limits-l59) |
| 93 / `nbw3-02-mapping-limits-l93` | `あわせて、終対象性は \(hX\) での同型で不変であることが示されている（isTerminalVertex_iff` | [4.7.3.16](4.7.3.16.md#nbw3-02-mapping-limits-l93) |
| 108 / `nbw3-02-mapping-limits-l108` | `定理（HTT §1.2.10。コードの docstring は Kerodon Thm. 4.8.4.1・Prop.` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l108) |
| 110 / `nbw3-02-mapping-limits-l110` | `Lean では isQCatEquivalence_iff_fullyFaithful_essentiallySur` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l110) |
| 112 / `nbw3-02-mapping-limits-l112` | `isofibration への置き換え（Core/EquivalencePath*）。\(Y\) の可逆な辺がなす ` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l112) |
| 113 / `nbw3-02-mapping-limits-l113` | `性質の移送。\(\tilde f\) も充満忠実で、本質的全射性は頂点上の全射に強まる（可逆な辺を経由して像を動かせ` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l113) |
| 114 / `nbw3-02-mapping-limits-l114` | `trivial Kan fibration であることの証明（Core/FullyFaithfulBoundary）` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l114) |
| 116 / `nbw3-02-mapping-limits-l116` | `このとき trivial Kan fibration は同値なので、\(\tilde f\)、したがって \(f\)` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l116) |
| 119 / `nbw3-02-mapping-limits-l119` | `Lean の構造：写像空間の写像を trivial fibration に上げる` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l119) |
| 120 / `nbw3-02-mapping-limits-l120` | `3 段目の「充満忠実な inner fibration は終対象性を反映する」の内部では、次の組み合わせが繰り返し使` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l120) |
| 122 / `nbw3-02-mapping-limits-l122` | `pinchedHomMap_rightFibration：写像空間の写像は右 fibration、とくに Kan f` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l122) |
| 123 / `nbw3-02-mapping-limits-l123` | `trivialKanFibration_of_fibration_of_simplicialHomotopyEqui` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l123) |
| 125 / `nbw3-02-mapping-limits-l125` | `二つを合わせると IsFullyFaithful.pinchedHomMap_trivialKanFibration` | [4.8.4.1](4.8.4.1.md#nbw3-02-mapping-limits-l125) |
| 129 / `nbw3-02-mapping-limits-l129` | `内容Lean場所 充満忠実 ⇒ \(hX\to hY\) も充満忠実IsFullyFaithful.toHoFull` | [4.8](4.8.md#nbw3-02-mapping-limits-l129) |
| 144 / `nbw3-02-mapping-limits-l144` | `isLimitCone_iff_trivialKanFibration：\(c\) が極限錐 ⇔ \((X_{/p}` | [7.1.1](7.1.1.md#nbw3-02-mapping-limits-l144) |
| 145 / `nbw3-02-mapping-limits-l145` | `limitConeIso、limitVertexIso：二つの極限錐は \(h(X_{/p})\) で同型で、頂点は` | [7.1.1](7.1.1.md#nbw3-02-mapping-limits-l145) |
| 150 / `nbw3-02-mapping-limits-l150` | `命題. \(f\colon X\to Y\) が同値なら、\(c\) が極限錐であることと \(f\circ c\)` | [7.1.4.12](7.1.4.12.md#nbw3-02-mapping-limits-l150) |
| 152 / `nbw3-02-mapping-limits-l152` | `Lean では IsQCatEquivalence.isLimitCone_iff（Core/Equivalence` | [7.1.4.12](7.1.4.12.md#nbw3-02-mapping-limits-l152) |
| 155 / `nbw3-02-mapping-limits-l155` | `引き戻しの四角形は \(\Delta^1\times\Delta^1\to X\) として扱う。鍵は同型 \(\De` | [7.6.2](7.6.2.md#nbw3-02-mapping-limits-l155) |
| 156 / `nbw3-02-mapping-limits-l156` | `def IsPullbackSquare {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) ` | [7.6.2](7.6.2.md#nbw3-02-mapping-limits-l156) |
| 157 / `nbw3-02-mapping-limits-l157` | `規約：右辺と上辺が cospan で、座標 \((0,0)\) が錐の頂点（Core/Pullback）。` | [7.6.2](7.6.2.md#nbw3-02-mapping-limits-l157) |
| 161 / `nbw3-02-mapping-limits-l161` | `命題（HTT Prop. 5.1.2.2、Kerodon §7.1.8）. 図式 \(p\colon J\to\ma` | [7.1.8.3](7.1.8.3.md#nbw3-02-mapping-limits-l161) |
| 163 / `nbw3-02-mapping-limits-l163` | `各点 \(k\in K\) で評価した錐が極限錐なら、元の錐も極限錐（isLimitCone_of_pointwis` | [7.1.8.3](7.1.8.3.md#nbw3-02-mapping-limits-l163) |
| 164 / `nbw3-02-mapping-limits-l164` | `各点で極限が存在するなら、各点で極限になる錐が存在する（exists_pointwiseLimitCone）。したが` | [7.1.8.3](7.1.8.3.md#nbw3-02-mapping-limits-l164) |
| 165 / `nbw3-02-mapping-limits-l165` | `その状況では、極限錐であることと各点で極限錐であることは同値（isLimitCone_iff_pointwise_o` | [7.1.8.3](7.1.8.3.md#nbw3-02-mapping-limits-l165) |
| 168 / `nbw3-02-mapping-limits-l168` | `2 の難しさは、各点で選んだ極限錐に自然性がないことにある。そこで「相対的な終点境界充填」を使い、選んだ錐を \(K` | [7.1.8.3](7.1.8.3.md#nbw3-02-mapping-limits-l168) |
| 171 / `nbw3-02-mapping-limits-l171` | `関手 ∞ 圏の極限を扱うには、slice \(X_{/p}\) のままでは \(\mathrm{Fun}(K,-)\` | [4.6.2](4.6.2.md#nbw3-02-mapping-limits-l171) |
| 172 / `nbw3-02-mapping-limits-l172` | `模型中身slice との比較 fat join \(A\diamond B\)\(A\times\Delta^1\t` | [4.6.2](4.6.2.md#nbw3-02-mapping-limits-l172) |
| 178 / `nbw3-02-mapping-limits-l178` | `錐の族の模型では、錐が関手 ∞ 圏の対象になる。そのため \(\mathrm{Fun}(K,-)\) との交換が内部` | [4.6.2](4.6.2.md#nbw3-02-mapping-limits-l178) |
| 181 / `nbw3-02-mapping-limits-l181` | `原典との違い` | [4.6.2](4.6.2.md#nbw3-02-mapping-limits-l181) |
| 182 / `nbw3-02-mapping-limits-l182` | `HTT は slice \(X_{/p}\) と fat slice \(X^{/p}\) の比較を Joyal の` | [4.6.2](4.6.2.md#nbw3-02-mapping-limits-l182) |
| 186 / `nbw3-02-mapping-limits-l186` | `Core/LimitExamples では、順序圏 \(0\to1\) の二項積が nerve の極限と一致する、と` | [7.6.1](7.6.1.md#nbw3-02-mapping-limits-l186) |

### 03-straightening.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 30 / `nbw3-03-straightening-l30` | `\(p\colon X\to B\) の辺 \(e\) が \(p\)-cocartesian とは、最初の辺が \` | [5.1.1.1](5.1.1.1.md#nbw3-03-straightening-l30) |
| 31 / `nbw3-03-straightening-l31` | `def IsCocartesianEdge {X B : SSet.{u}} (p : X ⟶ B) (e : X ` | [5.1.1.1](5.1.1.1.md#nbw3-03-straightening-l31) |
| 36 / `nbw3-03-straightening-l36` | `\(p\) が cocartesian fibration とは、inner fibration であって、底の任意` | [5.1.4.1](5.1.4.1.md#nbw3-03-straightening-l36) |
| 37 / `nbw3-03-straightening-l37` | `第 1 章の Joyal の定理は、「\(B=\Delta^0\) のとき、cocartesian 辺は可逆な辺に一` | [5.1.4.1](5.1.4.1.md#nbw3-03-straightening-l37) |
| 40 / `nbw3-03-straightening-l40` | `cocartesian fibration では、底の辺 \(e\colon b\to b'\) に沿って fibe` | [5.2.2](5.2.2.md#nbw3-03-straightening-l40) |
| 41 / `nbw3-03-straightening-l41` | `内容Lean場所 一点の持ち上げ（対象の移送）chooseCocartesianEdgeLift、cocartesi` | [5.2.2](5.2.2.md#nbw3-03-straightening-l41) |
| 48 / `nbw3-03-straightening-l48` | `「選択空間が可縮」という形で一意性を述べるのが、以後の構成の基本の型である。選び方の任意性を、可縮な Kan 複体の` | [5.2.2](5.2.2.md#nbw3-03-straightening-l48) |
| 59 / `nbw3-03-straightening-l59` | `∞ 圏Lean単体的圏の対象Hom（Kan 複体）場所 \(\mathcal S\)SpaceInfinity小さい` | [5.5.3](5.5.3.md#nbw3-03-straightening-l59) |
| 66 / `nbw3-03-straightening-l66` | `def SpaceInfinity : SSet.{u + 1} := SimplicialNerve KanObj` | [5.5.3](5.5.3.md#nbw3-03-straightening-l66) |
| 71 / `nbw3-03-straightening-l71` | `宇宙の扱い` | [5.5.3](5.5.3.md#nbw3-03-straightening-l71) |
| 72 / `nbw3-03-straightening-l72` | `対象が宇宙 \(u\) の単体的集合なので、それらを集めた ∞ 圏は宇宙 \(u+1\) に入る。関手 ∞ 圏 \(` | [5.5.3](5.5.3.md#nbw3-03-straightening-l72) |
| 77 / `nbw3-03-straightening-l77` | `def leftStraighteningInfinityMap (B : SSet.{u}) : LeftFibr` | [5.6](5.6.md#nbw3-03-straightening-l77) |
| 82 / `nbw3-03-straightening-l82` | `場所：F1/LeftStraighteningAllBases（構成）、F1/LeftStraighteningIn` | [5.6](5.6.md#nbw3-03-straightening-l82) |
| 91 / `nbw3-03-straightening-l91` | `二段に分かれる。まず通常の圏の nerve \(N(C)\) を底とする場合を示し、次に一般の \(B\) をそれに` | [5.3.1](5.3.1.md#nbw3-03-straightening-l91) |
| 94 / `nbw3-03-straightening-l94` | `strict transport。\(N(C)\) 上の左 fibration \(X\) と対象 \(c\) に対` | [5.3.1](5.3.1.md#nbw3-03-straightening-l94) |
| 95 / `nbw3-03-straightening-l95` | `def strictTransportDomains (C : Type u) [Category.{u} C] :` | [5.3.1](5.3.1.md#nbw3-03-straightening-l95) |
| 101 / `nbw3-03-straightening-l101` | `この構成は fibration \(X\) についても単体的に関手的なので、二変数の単体的関手「左 fibratio` | [5.3.1](5.3.1.md#nbw3-03-straightening-l101) |
| 103 / `nbw3-03-straightening-l103` | `充満忠実性（leftStraighteningCoherentMap_isFullyFaithful）：Hom への` | [5.3.1](5.3.1.md#nbw3-03-straightening-l103) |
| 104 / `nbw3-03-straightening-l104` | `本質的全射性（leftStraighteningCoherentMap_isEssentiallySurjectiv` | [5.3.1](5.3.1.md#nbw3-03-straightening-l104) |
| 106 / `nbw3-03-straightening-l106` | `結論：leftStraighteningCoherentMap_isQCatEquivalence（F1/LeftS` | [5.3.1](5.3.1.md#nbw3-03-straightening-l106) |
| 109 / `nbw3-03-straightening-l109` | `任意の単体的集合 \(B\) に対し、単体の圏 \(\Delta_{/B}\)（Lean では TransportS` | [6.3.6.5](6.3.6.5.md#nbw3-03-straightening-l109) |
| 110 / `nbw3-03-straightening-l110` | `\[ \mathrm{fv}\colon N(\Delta_{/B})\longrightarrow B \]` | [6.3.6.5](6.3.6.5.md#nbw3-03-straightening-l110) |
| 113 / `nbw3-03-straightening-l113` | `を考える。鍵になるのは次の事実である。` | [6.3.6.5](6.3.6.5.md#nbw3-03-straightening-l113) |
| 115 / `nbw3-03-straightening-l115` | `命題. \(\mathrm{fv}\) は、「始点を保つ辺」の集合 \(W\) に関する局所化である。すなわち \(` | [6.3.6.5](6.3.6.5.md#nbw3-03-straightening-l115) |
| 116 / `nbw3-03-straightening-l116` | `Lean：transportSimplexFirstVertexMap_isLocalization（F1/Tran` | [6.3.6.5](6.3.6.5.md#nbw3-03-straightening-l116) |
| 118 / `nbw3-03-straightening-l118` | `\(N(\Delta_{/B})\) は通常の圏の nerve なので、第一段が使える。\(B\) 上の左 fibr` | [5.6](5.6.md#nbw3-03-straightening-l118) |
| 119 / `nbw3-03-straightening-l119` | `本質的全射性は上で見たとおり一般の底で示されているので、残るのは充満忠実性である。同値性は次の判定に帰着する（F1/` | [5.6](5.6.md#nbw3-03-straightening-l119) |
| 120 / `nbw3-03-straightening-l120` | `lemma leftStraighteningInfinityMap_isQCatEquivalence_iff_f` | [5.6](5.6.md#nbw3-03-straightening-l120) |
| 123 / `nbw3-03-straightening-l123` | `つまり、「左 fibration を \(\mathrm{fv}\) で引き戻す操作が充満忠実」であればよい。これは` | [5.6](5.6.md#nbw3-03-straightening-l123) |

### 04-yoneda-adjunction-kan.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 32 / `nbw3-04-yoneda-adjunction-kan-l32` | `前層 ∞ 圏は小さい極限・余極限を無条件に持ち、それらは評価で保存・検出される（presheafInfinity_h` | [8.3.3](8.3.3.md#nbw3-04-yoneda-adjunction-kan-l32) |
| 52 / `nbw3-04-yoneda-adjunction-kan-l52` | `内容Lean場所 Yoneda の補題（写像空間版）：\(\mathrm{Map}_{\mathcal P(C)}(` | [8.3.3.13](8.3.3.13.md#nbw3-04-yoneda-adjunction-kan-l52) |
| 59 / `nbw3-04-yoneda-adjunction-kan-l59` | `充満忠実性の方針：Yoneda の補題から \(\mathrm{Map}(h_x,h_y)\simeq h_y(x)` | [8.3.3.13](8.3.3.13.md#nbw3-04-yoneda-adjunction-kan-l59) |
| 62 / `nbw3-04-yoneda-adjunction-kan-l62` | `原典との違い` | [8.3.3.13](8.3.3.13.md#nbw3-04-yoneda-adjunction-kan-l62) |
| 63 / `nbw3-04-yoneda-adjunction-kan-l63` | `HTT §5.1.3 は Yoneda 埋め込みを単体的圏の側で作り、モデル構造を通して ∞ 圏の関手にする。ここで` | [8.3.3.13](8.3.3.13.md#nbw3-04-yoneda-adjunction-kan-l63) |
| 70 / `nbw3-04-yoneda-adjunction-kan-l70` | `随伴は Kerodon Def. 6.2.1.1 と Remark 6.2.1.4 に従い、ホモトピー 2-圏での随` | [6.2.1.2](6.2.1.2.md#nbw3-04-yoneda-adjunction-kan-l70) |
| 71 / `nbw3-04-yoneda-adjunction-kan-l71` | `abbrev QCatAdjunction {X Y : SSet.{u}} [Quasicategory X] [` | [6.2.1.2](6.2.1.2.md#nbw3-04-yoneda-adjunction-kan-l71) |
| 73 / `nbw3-04-yoneda-adjunction-kan-l73` | `内容Lean場所 随伴 ⇒ 写像空間のホモトピー同値 \(\mathrm{Map}_Y(Fx,y)\simeq\ma` | [6.2.1.2](6.2.1.2.md#nbw3-04-yoneda-adjunction-kan-l73) |
| 79 / `nbw3-04-yoneda-adjunction-kan-l79` | `ホモトピー 2-圏での定義は扱いやすい一方で、「関手 ∞ 圏の中の随伴」や「随伴の空間」のような高次の情報は含まない` | [6.2.1.2](6.2.1.2.md#nbw3-04-yoneda-adjunction-kan-l79) |
| 85 / `nbw3-04-yoneda-adjunction-kan-l85` | `def IsLocalization {X D : SSet.{u}} (F : X ⟶ D) (W : Set (` | [6.3.1.9](6.3.1.9.md#nbw3-04-yoneda-adjunction-kan-l85) |
| 88 / `nbw3-04-yoneda-adjunction-kan-l88` | `\(F\) が \(W\) を反転し、任意の quasicategory \(E\) について、前合成 \(\mat` | [6.3.1.13](6.3.1.13.md#nbw3-04-yoneda-adjunction-kan-l88) |
| 91 / `nbw3-04-yoneda-adjunction-kan-l91` | `structure ReflectiveSubcategory (X : SSet.{u}) [Quasicateg` | [6.3.3](6.3.3.md#nbw3-04-yoneda-adjunction-kan-l91) |
| 94 / `nbw3-04-yoneda-adjunction-kan-l94` | `頂点の条件 \(P\) が張る充満部分 ∞ 圏への、包含の左随伴を指定したもの。ここから次が導かれる（F1B/Ref` | [6.3.3](6.3.3.md#nbw3-04-yoneda-adjunction-kan-l94) |
| 96 / `nbw3-04-yoneda-adjunction-kan-l96` | `余単位は可逆で、\(L\circ L\simeq L\)（counitIso、idempotentIso）` | [6.3.3](6.3.3.md#nbw3-04-yoneda-adjunction-kan-l96) |
| 97 / `nbw3-04-yoneda-adjunction-kan-l97` | `局所対象（単位が可逆な対象）は本質的像と一致する（isLocal_iff_essentialImage）` | [6.3.3](6.3.3.md#nbw3-04-yoneda-adjunction-kan-l97) |
| 98 / `nbw3-04-yoneda-adjunction-kan-l98` | `反射は、自身が反転する辺についての局所化（ReflectiveSubcategory.isLocalization）` | [6.3.3](6.3.3.md#nbw3-04-yoneda-adjunction-kan-l98) |
| 100 / `nbw3-04-yoneda-adjunction-kan-l100` | `一般の局所化の存在（Bousfield 局所化）は含まれていない。これは presentable の理論（第 6 章` | [6.3.3](6.3.3.md#nbw3-04-yoneda-adjunction-kan-l100) |
| 104 / `nbw3-04-yoneda-adjunction-kan-l104` | `def IsLeftCofinal {A B : SSet.{u}} (i : A ⟶ B) : Prop := ∀` | [7.2.1](7.2.1.md#nbw3-04-yoneda-adjunction-kan-l104) |
| 107 / `nbw3-04-yoneda-adjunction-kan-l107` | `任意の左 fibration \(E\to B\) について、切断の空間の制限 \(\mathrm{Fun}_{/B` | [7.2.1.1](7.2.1.1.md#nbw3-04-yoneda-adjunction-kan-l107) |
| 108 / `nbw3-04-yoneda-adjunction-kan-l108` | `内容Lean場所 left anodyne ⇒ left cofinal（right も同様）isRightCofi` | [7.2.1](7.2.1.md#nbw3-04-yoneda-adjunction-kan-l108) |
| 117 / `nbw3-04-yoneda-adjunction-kan-l117` | `cofinal な射に沿う slice の制限が trivial Kan fibration になる（sliceOv` | [7.2.1](7.2.1.md#nbw3-04-yoneda-adjunction-kan-l117) |
| 123 / `nbw3-04-yoneda-adjunction-kan-l123` | `\(\delta\colon K\to C\)、\(F_0\colon K\to D\) と、\(F\colon C` | [7.3.1.5](7.3.1.5.md#nbw3-04-yoneda-adjunction-kan-l123) |
| 124 / `nbw3-04-yoneda-adjunction-kan-l124` | `\[ K\times_C C_{/c}\longrightarrow K\xrightarrow{F_0}D \]` | [7.3.1.5](7.3.1.5.md#nbw3-04-yoneda-adjunction-kan-l124) |
| 127 / `nbw3-04-yoneda-adjunction-kan-l127` | `の上の誘導された余錐（頂点 \(F(c)\)）が余極限であることをいう（Kerodon Variant 7.3.1.` | [7.3.1.5](7.3.1.5.md#nbw3-04-yoneda-adjunction-kan-l127) |
| 128 / `nbw3-04-yoneda-adjunction-kan-l128` | `def IsLeftKanExtension {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ ` | [7.3.1.5](7.3.1.5.md#nbw3-04-yoneda-adjunction-kan-l128) |
| 131 / `nbw3-04-yoneda-adjunction-kan-l131` | `変換 \(\beta\) は単体的ホモトピー（\(K\times\Delta^1\to D\)）として厳密に持つ。\` | [7.3.1.5](7.3.1.5.md#nbw3-04-yoneda-adjunction-kan-l131) |
| 134 / `nbw3-04-yoneda-adjunction-kan-l134` | `内容Lean場所 存在 ⇔ 各点の局所図式が余極限を持つexists_kanLeftExtension_iff_lo` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l134) |
| 142 / `nbw3-04-yoneda-adjunction-kan-l142` | `右 Kan 拡張も双対的に揃っている（局所図式は \(K\times_C C_{c/}\)、条件は極限）。` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l142) |
| 145 / `nbw3-04-yoneda-adjunction-kan-l145` | `各点で余極限を選ぶだけでは、それらを一つの関手 \(F\) に束ねられない。そこで「相対 join」による表示を使う` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l145) |
| 149 / `nbw3-04-yoneda-adjunction-kan-l149` | `F1B では、∞ 圏の概念を通常の圏の nerve に制限すると Mathlib の概念に一致することを確かめている` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l149) |
| 151 / `nbw3-04-yoneda-adjunction-kan-l151` | `随伴：kanNonempty_adjunction_iff_nerveAdjunction` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l151) |
| 152 / `nbw3-04-yoneda-adjunction-kan-l152` | `左右の Kan 拡張（pointwise）：kanNerve_isLeftKanExtensionHom_iff_p` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l152) |
| 153 / `nbw3-04-yoneda-adjunction-kan-l153` | `局所的な Kan 錐の双方向の移送：kanNerveLeftCoconeTransport_cocone、kanNe` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l153) |
| 155 / `nbw3-04-yoneda-adjunction-kan-l155` | `定義が意図どおりであることを確かめる検算の役目を果たしている。第 2 章で見たとおり、一般の極限についての同種の比較` | [7.3](7.3.md#nbw3-04-yoneda-adjunction-kan-l155) |

### 05-gamma-bridges.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 62 / `nbw3-05-gamma-bridges-l62` | `空間の ∞ 圏 \(\mathcal S\) が完備かつ余完備であることは、二つの経路で示されている。` | [7.4.1](7.4.1.md#nbw3-05-gamma-bridges-l62) |
| 65 / `nbw3-05-gamma-bridges-l65` | `内容Lean場所 任意の小さい coherent 図式 \(B\to\mathcal S\) は極限を持つ。極限は ` | [7.4.1](7.4.1.md#nbw3-05-gamma-bridges-l65) |
| 71 / `nbw3-05-gamma-bridges-l71` | `これは「\(\lim F=\) 左 fibration \(\mathrm{Un}(F)\to B\) の切断の空間` | [7.4.1](7.4.1.md#nbw3-05-gamma-bridges-l71) |
| 74 / `nbw3-05-gamma-bridges-l74` | `通常の小さい圏 \(I\) 上の strict な図式 \(F\colon I\to\mathrm{Kan}\) は` | [7.5](7.5.md#nbw3-05-gamma-bridges-l74) |
| 75 / `nbw3-05-gamma-bridges-l75` | `内容Lean場所 任意の小圏上の Kan 値図式：Bousfield–Kan coend は ∞ 余極限（HTT 4` | [7.5](7.5.md#nbw3-05-gamma-bridges-l75) |
| 82 / `nbw3-05-gamma-bridges-l82` | `(b) が必要なのは、スペクトラム（Sp レーン）での Tot、ホモトピー不動点、fiber 列のように、古典的なホ` | [7.5](7.5.md#nbw3-05-gamma-bridges-l82) |

### 06-catinfty-ind-presentable.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 33 / `nbw3-06-catinfty-ind-presentable-l33` | `Cat∞ は coherent nerve として定義されていた（第 3 章）。その写像空間は関手 ∞ 圏の cor` | [5.5.3](5.5.3.md#nbw3-06-catinfty-ind-presentable-l33) |
| 34 / `nbw3-06-catinfty-ind-presentable-l34` | `def catInfinityMappingEquivalence (X Y : QCat.{u}) : QCatE` | [5.5.3](5.5.3.md#nbw3-06-catinfty-ind-presentable-l34) |
| 37 / `nbw3-06-catinfty-ind-presentable-l37` | `場所：F2/CatMappingSpace。coherent nerve の写像空間が元の単体的圏の Hom と同値` | [5.5.3](5.5.3.md#nbw3-06-catinfty-ind-presentable-l37) |
| 40 / `nbw3-06-catinfty-ind-presentable-l40` | `内容Lean場所 Cat∞ の引き戻し：cospan \(A\to C\leftarrow B\) を path で` | [4.6.4](4.6.4.md#nbw3-06-catinfty-ind-presentable-l40) |
| 47 / `nbw3-06-catinfty-ind-presentable-l47` | `lax pullback は Tamme の切除定理（K 理論の Land–Tamme 経路）の中心にある構成で、こ` | [4.6.4](4.6.4.md#nbw3-06-catinfty-ind-presentable-l47) |
| 51 / `nbw3-06-catinfty-ind-presentable-l51` | `class IsKappaFiltered (κ : Cardinal.{u}) (C : SSet.{u}) [Q` | [9.1.1.4](9.1.1.4.md#nbw3-06-catinfty-ind-presentable-l51) |
| 54 / `nbw3-06-catinfty-ind-presentable-l54` | `κ-small な図式がすべて余錐を持つこと（HTT Def. 5.3.1.7 の形）。cofinality による` | [9.1.1.4](9.1.1.4.md#nbw3-06-catinfty-ind-presentable-l54) |
| 57 / `nbw3-06-catinfty-ind-presentable-l57` | `目標（HTT Prop. 5.3.3.3）. \(\mathcal S\) において、filtered 余極限は有限` | [9.1.5](9.1.5.md#nbw3-06-catinfty-ind-presentable-l57) |
| 58 / `nbw3-06-catinfty-ind-presentable-l58` | `状態：未完成。Lean では仮定の形 CoherentFilteredLimitExchangeShape K（「形` | [9.1.5](9.1.5.md#nbw3-06-catinfty-ind-presentable-l58) |
| 60 / `nbw3-06-catinfty-ind-presentable-l60` | `この定理は、Ind の安定性（§3）、compact 対象の有限余極限での閉性（§4）、さらにその先の K 理論側の` | [9.1.5](9.1.5.md#nbw3-06-catinfty-ind-presentable-l60) |
| 65 / `nbw3-06-catinfty-ind-presentable-l65` | `def IndInfinity (κ : Cardinal.{u}) (C : SSet.{u}) [Quasica` | [9.3.1](9.3.1.md#nbw3-06-catinfty-ind-presentable-l65) |
| 67 / `nbw3-06-catinfty-ind-presentable-l67` | `前層 ∞ 圏 \(\mathcal P(C)\) の中で、表現可能前層を含み、同型と小さい κ-filtered 余` | [9.3.1](9.3.1.md#nbw3-06-catinfty-ind-presentable-l67) |
| 70 / `nbw3-06-catinfty-ind-presentable-l70` | `内容Lean場所 Ind 対象 ⇔ 表現可能前層の単一の小さい κ-filtered 図式の余極限isIndVert` | [9.3.1](9.3.1.md#nbw3-06-catinfty-ind-presentable-l70) |
| 77 / `nbw3-06-catinfty-ind-presentable-l77` | `Ind(C) の安定性（HA 1.1.3.6）は未完成（F1-7 b）。有限の半順序集合上の図式を単一の filte` | [9.3.1](9.3.1.md#nbw3-06-catinfty-ind-presentable-l77) |
| 81 / `nbw3-06-catinfty-ind-presentable-l81` | `def IsKappaCompact (κ : Cardinal.{u}) {C : SSet.{max u v}}` | [9.2.5](9.2.5.md#nbw3-06-catinfty-ind-presentable-l81) |
| 84 / `nbw3-06-catinfty-ind-presentable-l84` | `\(\mathrm{Map}(x,-)\) が小さい κ-filtered 余極限を保つこと。` | [9.2.5](9.2.5.md#nbw3-06-catinfty-ind-presentable-l84) |
| 86 / `nbw3-06-catinfty-ind-presentable-l86` | `表現可能前層は \(\mathcal P(C)\) の中でも Ind の中でも κ-compact（indYoned` | [9.2.5](9.2.5.md#nbw3-06-catinfty-ind-presentable-l86) |
| 87 / `nbw3-06-catinfty-ind-presentable-l87` | `retract で閉じる。有限余極限で閉じることは、交換定理を仮定にとった形で証明されている（a7 待ち）` | [9.2.5](9.2.5.md#nbw3-06-catinfty-ind-presentable-l87) |
| 88 / `nbw3-06-catinfty-ind-presentable-l88` | `compact 生成：\(C\) が冪等完備なら \(C\simeq\mathrm{Ind}_\kappa(C)^\` | [9.2.5](9.2.5.md#nbw3-06-catinfty-ind-presentable-l88) |
| 93 / `nbw3-06-catinfty-ind-presentable-l93` | `冪等射は、高次の整合性まで含めて「冪等図式」（Idem の nerve からの図式、CoherentIdempote` | [8.5](8.5.md#nbw3-06-catinfty-ind-presentable-l93) |
| 94 / `nbw3-06-catinfty-ind-presentable-l94` | `def IsIdempotentComplete (X : SSet.{u}) : Prop := ∀ d : Co` | [8.5](8.5.md#nbw3-06-catinfty-ind-presentable-l94) |
| 100 / `nbw3-06-catinfty-ind-presentable-l100` | `冪等完備化とは、冪等完備な \(D\) への充満忠実な \(f\) で、\(D\) の任意の対象が像の retrac` | [8.5](8.5.md#nbw3-06-catinfty-ind-presentable-l100) |
| 101 / `nbw3-06-catinfty-ind-presentable-l101` | `内容Lean場所 存在：前層 ∞ 圏の中の retract 閉包 \(\mathrm{Idem}(C)\)idemY` | [8.5](8.5.md#nbw3-06-catinfty-ind-presentable-l101) |
| 108 / `nbw3-06-catinfty-ind-presentable-l108` | `これで Catperf（冪等完備な小さい安定 ∞ 圏）を扱う準備が整っている。` | [8.5](8.5.md#nbw3-06-catinfty-ind-presentable-l108) |
| 112 / `nbw3-06-catinfty-ind-presentable-l112` | `def IsKappaAccessible (κ : Cardinal.{u}) (C : SSet.{u + 1}` | [9.5.1](9.5.1.md#nbw3-06-catinfty-ind-presentable-l112) |
| 115 / `nbw3-06-catinfty-ind-presentable-l115` | `完成：\(\mathrm{Ind}_\kappa(A)\) の accessibility、κ-compact 対象` | [9.5.1](9.5.1.md#nbw3-06-catinfty-ind-presentable-l115) |
| 116 / `nbw3-06-catinfty-ind-presentable-l116` | `作業中（P-1 b〜g）：presentable の定義と前層・Ind の presentable 性、極限・余極限` | [9.5.1](9.5.1.md#nbw3-06-catinfty-ind-presentable-l116) |

### classifying-shape.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 21 / `nbw3-classifying-shape-l21` | `\(B\) は群から「その群を自己同型として持つ一点」を作る操作（分類空間、デループ）。これまでの \(BG\)（群` | [1.3.2](1.3.2.md#nbw3-classifying-shape-l21) |
| 25 / `nbw3-classifying-shape-l25` | `離散群：\(BG\) は対象が一つで自己射の群が \(G\) の亜群。空間としては \(K(G,1)\)。連結で \` | [1.3.2](1.3.2.md#nbw3-classifying-shape-l25) |
| 26 / `nbw3-classifying-shape-l26` | `∞ 群：bar 構成 \(BG:=\operatorname{colim}_{[n]\in\Delta^{\math` | [1.3.2](1.3.2.md#nbw3-classifying-shape-l26) |
| 27 / `nbw3-classifying-shape-l27` | `繰り返し：\(A\) がアーベル群（\(E_\infty\) 群）なら \(BA\) も群で、\(B^nA=K(A,` | [1.3.2](1.3.2.md#nbw3-classifying-shape-l27) |
| 141 / `nbw3-classifying-shape-l141` | `この会話での「空間」は ∞ 亜群（∞ 圏 \(\mathcal S\) の対象、Kan 複体で表されるもの、補章 3` | [1.2.1](1.2.1.md#nbw3-classifying-shape-l141) |
| 142 / `nbw3-classifying-shape-l142` | `種類持っているもの空間としては 集合点0-切り詰め 亜群点、可逆な射1-切り詰め ∞ 亜群点、道、全ての高次のホモト` | [1.2.1](1.2.1.md#nbw3-classifying-shape-l142) |
| 159 / `nbw3-classifying-shape-l159` | `\(\Gamma(F)\) が連結 ⇔ \(\pi_0\Gamma(F)=\ast\)：空でなく、どの二つの大域切断` | [1.2.1](1.2.1.md#nbw3-classifying-shape-l159) |
| 160 / `nbw3-classifying-shape-l160` | `\(F\)\(\Gamma(F)\) の点点を結ぶ道連結 ⇔ \(BG\)\(G\) torsortorsor の同` | [1.2.1](1.2.1.md#nbw3-classifying-shape-l160) |
| 168 / `nbw3-classifying-shape-l168` | `性質意味例 空でない存在する基点付きなら自動 連結同値を除いて一意\(\mathrm{Br}(\mathbb F_q` | [1.2.1](1.2.1.md#nbw3-classifying-shape-l168) |
| 175 / `nbw3-classifying-shape-l175` | `\(\Gamma(B\mathbb Z)\simeq S^1\) は連結だが可縮でない（自明な torsor の自己` | [1.2.1](1.2.1.md#nbw3-classifying-shape-l175) |

### cocartesian-definition.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 23 / `nbw3-cocartesian-definition-l23` | `関手 \(p\colon E\to B\) の射 \(f\colon e\to e'\) が cocartesian` | [5.6.1](5.6.1.md#nbw3-cocartesian-definition-l23) |
| 31 / `nbw3-cocartesian-definition-l31` | `\(p\colon E\to B\) を準圏の間の写像とする。` | [5.1.4.1](5.1.4.1.md#nbw3-cocartesian-definition-l31) |
| 33 / `nbw3-cocartesian-definition-l33` | `内ファイブレーション：内ホーン \(\Lambda^n_i\subset\Delta^n\)（\(0\lt i\lt` | [5.1.4.1](5.1.4.1.md#nbw3-cocartesian-definition-l33) |
| 34 / `nbw3-cocartesian-definition-l34` | `cocartesian 辺：辺 \(f\colon x\to y\) が \(p\)-cocartesian とは、` | [5.1.1.1](5.1.1.1.md#nbw3-cocartesian-definition-l34) |
| 35 / `nbw3-cocartesian-definition-l35` | `cocartesian 持ち上げの存在：任意の \(x\in E\) と \(u\colon p(x)\to b\)` | [5.1.4.1](5.1.4.1.md#nbw3-cocartesian-definition-l35) |
| 37 / `nbw3-cocartesian-definition-l37` | `1〜3 を満たすとき \(p\) を cocartesian fibration という。1 はリフティング性質だが` | [5.1.4.1](5.1.4.1.md#nbw3-cocartesian-definition-l37) |
| 41 / `nbw3-cocartesian-definition-l41` | `\(n=2\)（存在）：\(\Lambda^2_0\) は辺 \(0\to1\)（\(=f\)）と \(0\to2\` | [5.1.1](5.1.1.md#nbw3-cocartesian-definition-l41) |
| 42 / `nbw3-cocartesian-definition-l42` | `\(n\ge3\)（一意性）：1 圏の一意性は、∞ 圏では「\(h\) を選ぶ空間が可縮」になる。可縮性は全ての次元` | [5.1.1](5.1.1.md#nbw3-cocartesian-definition-l42) |
| 46 / `nbw3-cocartesian-definition-l46` | `\(f\colon x\to y\) が cocartesian ⇔ 任意の \(z\) について次の正方形がホモト` | [5.1.2](5.1.2.md#nbw3-cocartesian-definition-l46) |
| 72 / `nbw3-cocartesian-definition-l72` | `種類リフティング性質意味 内ファイブレーション内ホーン \(\Lambda^n_i\)（\(0\lt i\lt n\` | [5.1.4](5.1.4.md#nbw3-cocartesian-definition-l72) |
| 79 / `nbw3-cocartesian-definition-l79` | `左ファイブレーションでは全ての辺が cocartesian なので、どの辺が特別かを区別する必要がなく、印なしのリフ` | [5.1.4](5.1.4.md#nbw3-cocartesian-definition-l79) |
| 99 / `nbw3-cocartesian-definition-l99` | `\(\Delta^1\) 上の両側 fibration（bicartesian fibration）が随伴そのもの（` | [6.2.1](6.2.1.md#nbw3-cocartesian-definition-l99) |

### coherent-nerve-diagrams.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 42 / `nbw3-coherent-nerve-diagrams-l42` | `次元データ 0対象 \(x\) 1射 \(f_{01}\in\mathrm{Map}(x_0,x_1)_0\) 2\` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l42) |
| 54 / `nbw3-coherent-nerve-diagrams-l54` | `\(\mathrm{Cat}_\infty=N^{hc}(\mathrm{QCat}^\Delta)\)：\(\ma` | [5.5.3](5.5.3.md#nbw3-coherent-nerve-diagrams-l54) |
| 59 / `nbw3-coherent-nerve-diagrams-l59` | `レベル普遍性 \(\mathfrak C[\Delta^n]\)Boardman–Vogt の W 構成 \(W[n` | [2.4.4](2.4.4.md#nbw3-coherent-nerve-diagrams-l59) |
| 65 / `nbw3-coherent-nerve-diagrams-l65` | `したがって \(\mathcal S\) は sSet（Kan–Quillen）を弱同値で、\(\mathrm{Ca` | [2.4.4](2.4.4.md#nbw3-coherent-nerve-diagrams-l65) |
| 71 / `nbw3-coherent-nerve-diagrams-l71` | `\(J\) 型の図式として、厳密な図式 \(J\to\mathcal C\) は硬すぎ、ホモトピー可換図式 \(J\` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l71) |
| 74 / `nbw3-coherent-nerve-diagrams-l74` | `\[ \mathfrak C[N(J)]\longrightarrow\mathcal C\ \ \text{（単体` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l74) |
| 77 / `nbw3-coherent-nerve-diagrams-l77` | `\(J\) の合成可能な列 \(j_0\to\cdots\to j_n\) ごとに \(\mathfrak C[\D` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l77) |
| 80 / `nbw3-coherent-nerve-diagrams-l80` | `\(n=3\) で新しく必要になるのは \(\mathrm{Map}(x_0,x_3)\) の中の正方形である。` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l80) |
| 81 / `nbw3-coherent-nerve-diagrams-l81` | `\[ \begin{array}{ccc} f_{03} & \xrightarrow{\ H_{013}\ } &` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l81) |
| 88 / `nbw3-coherent-nerve-diagrams-l88` | `頂点は部分集合 \(\{0,3\},\{0,1,3\},\{0,2,3\},\{0,1,2,3\}\)、辺は低次のホ` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l88) |
| 91 / `nbw3-coherent-nerve-diagrams-l91` | `境界が与えられても内部を埋められるとは限らない。\(n\) 段目の障害は \(\pi_{n-2}\mathrm{Ma` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l91) |
| 104 / `nbw3-coherent-nerve-diagrams-l104` | `\[ \begin{array}{ccc} \ast & \longrightarrow & \ast\\ \dow` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l104) |
| 111 / `nbw3-coherent-nerve-diagrams-l111` | `\(J=[1]\times[1]\)。\(J\) の中では二つの経路の合成は同じ射 \(a\to d\) なので、整` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l111) |
| 113 / `nbw3-coherent-nerve-diagrams-l113` | `ホモトピー可換図式としては、どの \(\gamma\) でも同じ一つの図式。` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l113) |
| 114 / `nbw3-coherent-nerve-diagrams-l114` | `整合的図式としては、\(\gamma\) と \(\gamma'\) が同値になるのは、端点を止めてホモトピックなと` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l114) |
| 115 / `nbw3-coherent-nerve-diagrams-l115` | `違いは実際に現れる：この正方形はホモトピー引き戻し \(\ast\times^h_X\ast=\Omega X\) ` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l115) |
| 119 / `nbw3-coherent-nerve-diagrams-l119` | `\(J=B(\mathbb Z/2)\)（1 対象、射 \(e,\tau\)、\(\tau^2=e\)）、値は空間 ` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l119) |
| 121 / `nbw3-coherent-nerve-diagrams-l121` | `1 単体 \((\tau)\)：写像 \(t\colon X\to X\)。` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l121) |
| 122 / `nbw3-coherent-nerve-diagrams-l122` | `2 単体 \((\tau,\tau)\)：合成は \(e\) なので、ホモトピー \(H\colon\mathrm{` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l122) |
| 123 / `nbw3-coherent-nerve-diagrams-l123` | `3 単体 \((\tau,\tau,\tau)\)：§3 の正方形で、\(f_{01}=f_{12}=f_{23}=` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l123) |
| 128 / `nbw3-coherent-nerve-diagrams-l128` | `さらに高次の単体 \((\tau,\dots,\tau)\) ごとに、より高次の整合性が続く。` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l128) |
| 130 / `nbw3-coherent-nerve-diagrams-l130` | `\(t\) と \(H\) だけ（「ホモトピーで \(t^2\simeq\mathrm{id}\)」）では、一般に整` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l130) |
| 133 / `nbw3-coherent-nerve-diagrams-l133` | `安定域（\(n\) が十分大きい）で次の列を考える。` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l133) |
| 134 / `nbw3-coherent-nerve-diagrams-l134` | `\[ S^{n+2}\xrightarrow{\ 2\ }S^{n+2}\xrightarrow{\ \eta\ }` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l134) |
| 137 / `nbw3-coherent-nerve-diagrams-l137` | `\(\eta\circ2\simeq0\) かつ \(2\circ\eta\simeq0\) なので、\(f_{02` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l137) |
| 139 / `nbw3-coherent-nerve-diagrams-l139` | `零ホモトピー \(H_{012}\colon0\Rightarrow\eta\circ2\) と \(H_{123}` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l139) |
| 140 / `nbw3-coherent-nerve-diagrams-l140` | `§3 の正方形の境界は、\(\mathrm{Map}(S^{n+2},S^{n+1})\) の零写像における loo` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l140) |
| 141 / `nbw3-coherent-nerve-diagrams-l141` | `Toda の計算により \(\langle2,\eta,2\rangle=\{\eta^2\}\)（不定性なし）なの` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l141) |
| 143 / `nbw3-coherent-nerve-diagrams-l143` | `このホモトピー可換図式は整合的図式にも厳密な図式にも持ち上がらない。§3 の「\(n=3\) の障害は \(\pi_` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l143) |
| 146 / `nbw3-coherent-nerve-diagrams-l146` | `原典との違い` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l146) |
| 148 / `nbw3-coherent-nerve-diagrams-l148` | `HTT は \(\mathfrak C[\Delta^n]\) を Def. 1.1.5.1 で、上と同じ部分集合の` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l148) |
| 149 / `nbw3-coherent-nerve-diagrams-l149` | `W 構成との一致（Cordier）、厳密化定理（Vogt）は古典的な結果で、HTT では Prop. 4.2.4.4` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l149) |
| 154 / `nbw3-coherent-nerve-diagrams-l154` | `このリポジトリとの対応（既出の宣言のみ）` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l154) |
| 156 / `nbw3-coherent-nerve-diagrams-l156` | `coherent nerve 自体は Mathlib の SimplicialNerve をそのまま使う。Kan 豊` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l156) |
| 157 / `nbw3-coherent-nerve-diagrams-l157` | `\(\mathcal S\)・\(\mathrm{Cat}_\infty\) は SpaceInfinity・Cat` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l157) |
| 158 / `nbw3-coherent-nerve-diagrams-l158` | `strict な図式を整合的図式とみなすのは kanDiagramCoherentNerve（F1/KanDiagr` | [2.4.3](2.4.3.md#nbw3-coherent-nerve-diagrams-l158) |

### f-01-simplicial-kan.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 68 / `nbw3-f-01-simplicial-kan-l68` | `Kan fibration に対して左持ち上げ性質を持つ射を anodyne といい、inner fibration` | [3.1.2](3.1.2.md#nbw3-f-01-simplicial-kan-l68) |
| 69 / `nbw3-f-01-simplicial-kan-l69` | `\[ \text{anodyne} = {}^{\text{⧄}}(\text{Kan fibration}),\q` | [3.1.2](3.1.2.md#nbw3-f-01-simplicial-kan-l69) |
| 74 / `nbw3-f-01-simplicial-kan-l74` | `anodyneExtensions := (fibrations _).llp、innerAnodyneExtens` | [3.1.2](3.1.2.md#nbw3-f-01-simplicial-kan-l74) |
| 75 / `nbw3-f-01-simplicial-kan-l75` | `small object argument により、anodyne 射は「horn の包含の pushout の超限` | [4.1.3](4.1.3.md#nbw3-f-01-simplicial-kan-l75) |
| 76 / `nbw3-f-01-simplicial-kan-l76` | `pushout-product：anodyne と単射の pushout-product は anodyne、inn` | [4.1.3](4.1.3.md#nbw3-f-01-simplicial-kan-l76) |
| 81 / `nbw3-f-01-simplicial-kan-l81` | `small object argument から、どんな射も「anodyne の後に fibration」に分解でき` | [3.1.8](3.1.8.md#nbw3-f-01-simplicial-kan-l81) |
| 82 / `nbw3-f-01-simplicial-kan-l82` | `置き換え主張宣言（いまの所在） inner anodyne と inner fibration への分解任意の \(` | [3.1.8](3.1.8.md#nbw3-f-01-simplicial-kan-l82) |
| 89 / `nbw3-f-01-simplicial-kan-l89` | `二つの Kan 置換の違いは次のとおり。small object argument による置換は作り方が抽象的で、E` | [3.1.8](3.1.8.md#nbw3-f-01-simplicial-kan-l89) |
| 92 / `nbw3-f-01-simplicial-kan-l92` | `写像 \(f, g : X \to Y\) の間のホモトピーは、\(\Delta^1 \times X \to Y\` | [3.1.5](3.1.5.md#nbw3-f-01-simplicial-kan-l92) |
| 136 / `nbw3-f-01-simplicial-kan-l136` | `Kan 複体 \(X\) と頂点 \(x\) について、\(\pi_n(X, x)\) は、境界を \(x\) に送` | [3.2.2.4](3.2.2.4.md#nbw3-f-01-simplicial-kan-l136) |
| 137 / `nbw3-f-01-simplicial-kan-l137` | `宣言意味場所 KanHomotopyGroup X n x\(\pi_{n+1}(X, x)\)（添字が一つずれてい` | [3.2.2.4](3.2.2.4.md#nbw3-f-01-simplicial-kan-l137) |
| 146 / `nbw3-f-01-simplicial-kan-l146` | `Kan 複体の写像は、ホモトピー群の準同型を誘導する。基点付きホモトピーで移り合う写像は、同じ準同型を誘導する（Ka` | [3.2.2.4](3.2.2.4.md#nbw3-f-01-simplicial-kan-l146) |
| 147 / `nbw3-f-01-simplicial-kan-l147` | `KanPiIsomorphism f：すべての基点とすべての \(n\) で \(\pi_n(f)\) が全単射であ` | [3.2.2.4](3.2.2.4.md#nbw3-f-01-simplicial-kan-l147) |
| 148 / `nbw3-f-01-simplicial-kan-l148` | `基点のないホモトピーで移り合う二つの写像は、同時に π_* 同型になるか、同時にならないか、のどちらか（kanPiI` | [3.2.2.4](3.2.2.4.md#nbw3-f-01-simplicial-kan-l148) |
| 152 / `nbw3-f-01-simplicial-kan-l152` | `Kan fibration \(p : E \to B\)（\(E, B\) は Kan 複体）と、\(E\) の頂` | [3.2.6](3.2.6.md#nbw3-f-01-simplicial-kan-l152) |
| 153 / `nbw3-f-01-simplicial-kan-l153` | `\[ \cdots \to \pi_{n+1}(B) \xrightarrow{\ \partial\ } \pi_` | [3.2.6](3.2.6.md#nbw3-f-01-simplicial-kan-l153) |
| 157 / `nbw3-f-01-simplicial-kan-l157` | `fiberLongExact p e（KST/Spectra/FibrationSequence.lean:28）：` | [3.2.6](3.2.6.md#nbw3-f-01-simplicial-kan-l157) |
| 158 / `nbw3-f-01-simplicial-kan-l158` | `連結準同型は群準同型である：connectingHom p e n : π_{n+2}(B) →* π_{n+1}(` | [3.2.6](3.2.6.md#nbw3-f-01-simplicial-kan-l158) |
| 162 / `nbw3-f-01-simplicial-kan-l162` | `Kan 複体の間の写像が π_* 同型なら、ホモトピー同値である。` | [3.2.7.1](3.2.7.1.md#nbw3-f-01-simplicial-kan-l162) |
| 164 / `nbw3-f-01-simplicial-kan-l164` | `基点付き版：exists_pointedHomotopyInverse（KST/Spectra/PointedKan` | [3.2.7.1](3.2.7.1.md#nbw3-f-01-simplicial-kan-l164) |
| 165 / `nbw3-f-01-simplicial-kan-l165` | `基点なし版：homotopyEquivalence_of_kanPiIsomorphism_of_piZero_su` | [3.2.7.1](3.2.7.1.md#nbw3-f-01-simplicial-kan-l165) |
| 167 / `nbw3-f-01-simplicial-kan-l167` | `§2 の結果と合わせると、Kan 複体の間の写像について、次の四つが同値になる。「π_* 同型」「ホモトピー同値」「` | [3.2.7.1](3.2.7.1.md#nbw3-f-01-simplicial-kan-l167) |
| 170 / `nbw3-f-01-simplicial-kan-l170` | `単体的集合（Kan とは限らない）の間の写像 \(f : A \to B\) が「弱同値」であることには、このリポジ` | [3.2.7.2](3.2.7.2.md#nbw3-f-01-simplicial-kan-l170) |
| 171 / `nbw3-f-01-simplicial-kan-l171` | `言い方定義宣言 Kan 複体への写像で見るすべての Kan 複体 \(Z\) について、\(\pi_0\mathrm` | [3.2.7.2](3.2.7.2.md#nbw3-f-01-simplicial-kan-l171) |
| 177 / `nbw3-f-01-simplicial-kan-l177` | `関係を示す結果として、Kan 複体の間の anodyne 射は π_* 同型である（kanPiIsomorphism` | [3.2.7.2](3.2.7.2.md#nbw3-f-01-simplicial-kan-l177) |
| 181 / `nbw3-f-01-simplicial-kan-l181` | `Kan fibration の塔 \(\cdots \to X_2 \to X_1 \to X_0\) の極限を考え` | [7.6.5](7.6.5.md#nbw3-f-01-simplicial-kan-l181) |
| 183 / `nbw3-f-01-simplicial-kan-l183` | `極限は Kan 複体：各 \(X_{n+1} \to X_n\) が Kan fibration で、\(X_0\)` | [7.6.5.11](7.6.5.11.md#nbw3-f-01-simplicial-kan-l183) |
| 184 / `nbw3-f-01-simplicial-kan-l184` | `非可換な lim¹：群の塔 \(G_n\) と準同型 \(q_n : G_{n+1} \to G_n\) について、` | [保留](issues.md#nbw3-f-01-simplicial-kan-l184) |
| 185 / `nbw3-f-01-simplicial-kan-l185` | `Milnor の完全列（KST/Spectra/TowerMilnorExactness.lean・TowerGro` | [保留](issues.md#nbw3-f-01-simplicial-kan-l185) |
| 190 / `nbw3-f-01-simplicial-kan-l190` | `Mittag–Leffler：塔が Mittag–Leffler 条件を満たせば、\(\lim^1\) は自明になり` | [保留](issues.md#nbw3-f-01-simplicial-kan-l190) |
| 195 / `nbw3-f-01-simplicial-kan-l195` | `基点付き単体的集合は PointedSimplicialSet := PointedObject SSet（Serr` | [5.5.2](5.5.2.md#nbw3-f-01-simplicial-kan-l195) |
| 196 / `nbw3-f-01-simplicial-kan-l196` | `構成・結果主張宣言（いまの所在） smash 積と基点付き内部 Homsmash 積で対称モノイダル閉圏になり、\(` | [5.5.2](5.5.2.md#nbw3-f-01-simplicial-kan-l196) |
| 205 / `nbw3-f-01-simplicial-kan-l205` | `最後の同型は、道空間 fibration \(\Omega Y \to PY \to Y\) の長完全列（§3.3）` | [5.5.2](5.5.2.md#nbw3-f-01-simplicial-kan-l205) |
| 210 / `nbw3-f-01-simplicial-kan-l210` | `基本亜群：単体的集合 \(A\) の基本亜群を、ホモトピー圏の自由亜群として定義する（simplicialFunda` | [保留](issues.md#nbw3-f-01-simplicial-kan-l210) |
| 212 / `nbw3-f-01-simplicial-kan-l212` | `necklace（Dugger–Spivak）：単体を頂点で貼り合わせた「数珠」の形の単体的集合。coherent ` | [保留](issues.md#nbw3-f-01-simplicial-kan-l212) |

### f-02-model-free.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 48 / `nbw3-f-02-model-free-l48` | `持ち上げ性質で定まる射の族 \(I\) について、small object argument は、任意の射を「\(I` | [3.1.8](3.1.8.md#nbw3-f-02-model-free-l48) |
| 50 / `nbw3-f-02-model-free-l50` | `\[ X \xrightarrow{\ \text{anodyne}\ } RX \xrightarrow{\ \t` | [3.1.8](3.1.8.md#nbw3-f-02-model-free-l50) |
| 53 / `nbw3-f-02-model-free-l53` | `つまり、関手的な Kan 置換 \(X \to RX\) である（AnodyneKanReplacement.fac` | [3.1.8](3.1.8.md#nbw3-f-02-model-free-l53) |
| 56 / `nbw3-f-02-model-free-l56` | `関連する一般的な補題もある：generatedLeft_map（HomotopicalAlgebra/Generat` | [3.1.8](3.1.8.md#nbw3-f-02-model-free-l56) |
| 63 / `nbw3-f-02-model-free-l63` | `単体的集合 \(X\) について、端点の包含 \(X \to \Delta^1 \times X\)（\(0\) 側` | [3.1.2](3.1.2.md#nbw3-f-02-model-free-l63) |
| 68 / `nbw3-f-02-model-free-l68` | `単体的集合の圏を、anodyne 射を可逆にして局所化した 1 圏を考える（Gabriel–Zisman の局所化）` | [3.1.7](3.1.7.md#nbw3-f-02-model-free-l68) |
| 69 / `nbw3-f-02-model-free-l69` | `\[ \texttt{anodyneQ} : \mathbf{sSet} \to \mathbf{sSet}[\te` | [3.1.7](3.1.7.md#nbw3-f-02-model-free-l69) |
| 72 / `nbw3-f-02-model-free-l72` | `（anodyneQ := SSet.anodyneExtensions.Q、HomotopicalAlgebra/S` | [3.1.7](3.1.7.md#nbw3-f-02-model-free-l72) |
| 78 / `nbw3-f-02-model-free-l78` | `第 1 章 §3.5 で、単体的集合の写像 \(f : X \to Y\) が「弱同値」であることの三つの言い方を挙` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l78) |
| 80 / `nbw3-f-02-model-free-l80` | `見方定義宣言 (a) anodyne 局所化\(\texttt{anodyneQ}(f)\) が同型IsIso (a` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l80) |
| 87 / `nbw3-f-02-model-free-l87` | `(a) ⇔ (b)：anodyneQ_isIso_iff_tests（KanTestDetection.lean:1` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l87) |
| 89 / `nbw3-f-02-model-free-l89` | `(a) ⇒ (b)：Kan 複体 \(K\) へのホモトピー類 \([-, K]\) は、anodyne 射を全単射` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l89) |
| 90 / `nbw3-f-02-model-free-l90` | `(b) ⇒ (a)：Kan 置換 \(X \to RX\) は anodyne なので、anodyneQ の中で \` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l90) |
| 93 / `nbw3-f-02-model-free-l93` | `(b) ⇔ (c)：Kan 複体の間の写像については、(b) はホモトピー同値と同じで、ホモトピー同値は White` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l93) |
| 97 / `nbw3-f-02-model-free-l97` | `ポイント` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l97) |
| 98 / `nbw3-f-02-model-free-l98` | `「弱同値」を、モデル構造の公理から出すのではなく、Kan 複体へのホモトピー類（(b)）で定義してしまう。そうすれば` | [3.2.7.2](3.2.7.2.md#nbw3-f-02-model-free-l98) |

### f-03-localization.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 53 / `nbw3-f-03-localization-l53` | `単体的集合 \(X\)、辺の集合 \(W \subseteq X_1\)、写像 \(F : X \to D\) につ` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l53) |
| 55 / `nbw3-f-03-localization-l55` | `\(F\) は \(W\) の辺をすべて可逆な辺に送る。` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l55) |
| 56 / `nbw3-f-03-localization-l56` | `すべての quasicategory \(E\)（同じ宇宙）について、前合成 \[ F^* : \mathrm{Fu` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l56) |
| 63 / `nbw3-f-03-localization-l63` | `def IsLocalization {X D : SSet.{u}} (F : X ⟶ D) (W : Set (` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l63) |
| 66 / `nbw3-f-03-localization-l66` | `InfinityCategories/Kerodon/AdjointFunctors/Localization/Lo` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l66) |
| 69 / `nbw3-f-03-localization-l69` | `定義の細かい点` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l69) |
| 71 / `nbw3-f-03-localization-l71` | `\(D\) が quasicategory であることは要求しない。実際、§3 の証明の途中に出てくる「逆辺を貼り付` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l71) |
| 72 / `nbw3-f-03-localization-l72` | `普遍性を確かめる相手 \(E\) は同じ宇宙 u に限る。宇宙を変える補題（IsLocalization.ulift` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l72) |
| 73 / `nbw3-f-03-localization-l73` | `これは Dwyer–Kan 局所化（一般の局所化）の定義である。Bousfield 局所化（反射的局所化）は、その特` | [6.3.1.9](6.3.1.9.md#nbw3-f-03-localization-l73) |
| 81 / `nbw3-f-03-localization-l81` | `定理` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l81) |
| 82 / `nbw3-f-03-localization-l82` | `任意の単体的集合 \(X\) と辺の集合 \(W\) について、quasicategory \(Q\) と、\(W\` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l82) |
| 83 / `nbw3-f-03-localization-l83` | `theorem exists_quasicategory_localization (X : SSet.{u}) (` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l83) |
| 85 / `nbw3-f-03-localization-l85` | `InfinityCategories/Kerodon/AdjointFunctors/Localization/Lo` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l85) |
| 88 / `nbw3-f-03-localization-l88` | `証明は三段で、どれも第 1・2 章の道具でできている。` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l88) |
| 91 / `nbw3-f-03-localization-l91` | `\(\Delta^1\)（一本の辺）を Kan 置換したものを \(J\) とする（walkingEquivalen` | [6.3.2.1](6.3.2.1.md#nbw3-f-03-localization-l91) |
| 93 / `nbw3-f-03-localization-l93` | `\(J\) は Kan 複体なので、すべての辺が可逆である。` | [6.3.2.1](6.3.2.1.md#nbw3-f-03-localization-l93) |
| 94 / `nbw3-f-03-localization-l94` | `包含 \(\Delta^1 \to J\) は anodyne である。` | [6.3.2.1](6.3.2.1.md#nbw3-f-03-localization-l94) |
| 96 / `nbw3-f-03-localization-l96` | `つまり \(J\) は「可逆な辺が一本ある、可縮な空間」で、\(J\) から \(Y\) への関手は「\(Y\) の` | [6.3.2.1](6.3.2.1.md#nbw3-f-03-localization-l96) |
| 99 / `nbw3-f-03-localization-l99` | `\(W\) の各辺 \(w\) について、\(\Delta^1 \xrightarrow{w} X\) と \(\D` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l99) |
| 100 / `nbw3-f-03-localization-l100` | `\[ P \;=\; X \sqcup_{\coprod_{w \in W} \Delta^1} \coprod_{` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l100) |
| 103 / `nbw3-f-03-localization-l103` | `（inverseAttachment X W、InfinityCategories/Kerodon/AdjointF` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l103) |
| 104 / `nbw3-f-03-localization-l104` | `主張：どの quasicategory \(Y\) についても、制限写像 \(\mathrm{Fun}(P, Y) ` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l104) |
| 105 / `nbw3-f-03-localization-l105` | `理由は次のとおり。\(P\) への関手は「\(X\) への関手」と「各 \(J\) への延長」の組である。 \(W\` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l105) |
| 109 / `nbw3-f-03-localization-l109` | `自明 Kan fibration は同値なので（§1）、\(X \to P\) は局所化である（inverseAtt` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l109) |
| 112 / `nbw3-f-03-localization-l112` | `\(P \to \ast\) を「inner anodyne の後に inner fibration」に分解する（第` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l112) |
| 113 / `nbw3-f-03-localization-l113` | `\[ P \xrightarrow{\ j\ (\text{inner anodyne})\ } Q \to \as` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l113) |
| 116 / `nbw3-f-03-localization-l116` | `inner anodyne \(j\) について、どの quasicategory \(Y\) でも前合成 \(j^` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l116) |
| 120 / `nbw3-f-03-localization-l120` | `この証明の性格` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l120) |
| 122 / `nbw3-f-03-localization-l122` | `使っているのは、Kan 置換、pushout、自明 Kan fibration、inner anodyne 置換だけ` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l122) |
| 123 / `nbw3-f-03-localization-l123` | `得られるのは存在と普遍性で、\(Q\) の写像空間は分からない（\(J\) を貼り付けて置き換えた後の形は具体的に計` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l123) |
| 124 / `nbw3-f-03-localization-l124` | `この定理は InfinityCategories/Kerodon/AdjointFunctors/Localizat` | [6.3.2](6.3.2.md#nbw3-f-03-localization-l124) |
| 130 / `nbw3-f-03-localization-l130` | `結果宣言 前合成は充満忠実：\(\mathrm{Fun}(D, E) \to \mathrm{Fun}(X, E)\` | [6.3.1](6.3.1.md#nbw3-f-03-localization-l130) |
| 141 / `nbw3-f-03-localization-l141` | `存在定理は抽象的な \(Q\) を作るだけなので、実際には「手元の具体的な関手 \(F : X \to D\) が局` | [6.3.1](6.3.1.md#nbw3-f-03-localization-l141) |
| 143 / `nbw3-f-03-localization-l143` | `判定法条件の形宣言 延長による判定前合成が充満忠実で、\(W\) を可逆に送る関手がすべて延びるisLocaliza` | [6.3.1](6.3.1.md#nbw3-f-03-localization-l143) |
| 150 / `nbw3-f-03-localization-l150` | `最後の「反射による判定」が、Bousfield 局所化を Dwyer–Kan 局所化の特別な場合にしている（§6）。` | [6.3.1](6.3.1.md#nbw3-f-03-localization-l150) |
| 154 / `nbw3-f-03-localization-l154` | `Bousfield 局所化（反射的局所化）とは、充満部分圏 \(C_{\mathrm{loc}} \subseteq` | [6.3.3](6.3.3.md#nbw3-f-03-localization-l154) |
| 155 / `nbw3-f-03-localization-l155` | `\[ L : C \to C_{\mathrm{loc}} \ \text{は}\ W_L = \{ f \mid ` | [6.3.3](6.3.3.md#nbw3-f-03-localization-l155) |
| 159 / `nbw3-f-03-localization-l159` | `抽象的な局所化を \(C\) の中の部分圏として実現でき、写像空間が \(C\) の写像空間で計算できる。これが B` | [6.3.3](6.3.3.md#nbw3-f-03-localization-l159) |
| 162 / `nbw3-f-03-localization-l162` | `逆に、一般の局所化は右随伴を持つとは限らない。例えば、小さい安定 ∞ 圏の Verdier 商は、ふつう右随伴を持た` | [6.3.3](6.3.3.md#nbw3-f-03-localization-l162) |
| 185 / `nbw3-f-03-localization-l185` | `概念Dwyer–Kan 局所化との関係所在 Gabriel–Zisman 局所化（1 圏）∞ 局所化のホモトピー圏M` | [6.3](6.3.md#nbw3-f-03-localization-l185) |

### f-06-straightening.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 49 / `nbw3-f-06-straightening-l49` | `Kan fibration は、transport がすべてホモトピー同値である左 fibration（Kerodo` | [5.2.2.20](5.2.2.20.md#nbw3-f-06-straightening-l49) |
| 57 / `nbw3-f-06-straightening-l57` | `主定理は、任意の小さい quasicategory \(B\) について \(\mathrm{LFib}(B)\si` | [5.6](5.6.md#nbw3-f-06-straightening-l57) |
| 58 / `nbw3-f-06-straightening-l58` | `部品内容Lean・場所（旧シリーズの記述）状態 両辺の ∞ 圏\(\mathcal S\)、\(\mathrm{Ca` | [5.6](5.6.md#nbw3-f-06-straightening-l58) |
| 69 / `nbw3-f-06-straightening-l69` | `Map の関手性の三つの作り方` | [5.6](5.6.md#nbw3-f-06-straightening-l69) |
| 71 / `nbw3-f-06-straightening-l71` | `単体的圏 \(\mathfrak C[C]\) の厳密な合成を使い、Kan 化して \(N(\mathcal Kan` | [5.6](5.6.md#nbw3-f-06-straightening-l71) |
| 72 / `nbw3-f-06-straightening-l72` | `twisted arrow を straightening する。いまの形式化はこれ。` | [5.6](5.6.md#nbw3-f-06-straightening-l72) |
| 73 / `nbw3-f-06-straightening-l73` | `関手にせず fibration のまま扱う（Cisinski の本）。\(\mathcal S\) は普遍左 fib` | [5.6](5.6.md#nbw3-f-06-straightening-l73) |
| 76 / `nbw3-f-06-straightening-l76` | `底が quasicategory でない一般の単体的集合の場合は、主張としては入っていない。quasicategor` | [5.6](5.6.md#nbw3-f-06-straightening-l76) |
| 80 / `nbw3-f-06-straightening-l80` | `Kerodon（5.6 節）は Cat∞ 値を本命として扱い、空間値はその特殊な場合として得る。` | [5.6](5.6.md#nbw3-f-06-straightening-l80) |
| 82 / `nbw3-f-06-straightening-l82` | `普遍 cocartesian fibration \(V\colon\mathcal{QC}_{\mathrm{Ob` | [5.6](5.6.md#nbw3-f-06-straightening-l82) |
| 83 / `nbw3-f-06-straightening-l83` | `unstraightening \(\int_{\mathcal C}F=\mathcal C\times_{\ma` | [5.6](5.6.md#nbw3-f-06-straightening-l83) |
| 84 / `nbw3-f-06-straightening-l84` | `主定理 5.6.0.2：表現と同値の組全体の Kan 複体 \(\mathrm{TW}(\mathcal E/\ma` | [5.6](5.6.md#nbw3-f-06-straightening-l84) |
| 85 / `nbw3-f-06-straightening-l85` | `証明（5.6.9）は底の骨格に沿った帰納法。\(\mathrm{TW}(\mathcal E/-)\) は骨格の p` | [5.6](5.6.md#nbw3-f-06-straightening-l85) |
| 86 / `nbw3-f-06-straightening-l86` | `まず同値類の全単射を得て、ホモトピー圏の同値（7.4.2）、∞ 圏の同値へと後で引き上げる。` | [5.6](5.6.md#nbw3-f-06-straightening-l86) |
| 88 / `nbw3-f-06-straightening-l88` | `Kerodonいまの形式化 本命Cat∞ 値（空間値は特殊な場合）空間値（Cat∞ 値は別系統で途中） 主役の向きu` | [5.6](5.6.md#nbw3-f-06-straightening-l88) |
| 134 / `nbw3-f-06-straightening-l134` | `対象は小さい ∞ 圏とその対象の組 \((A,a)\)。射 \((A,a)\to(B,b)\) は関手 \(F\co` | [5.5.5](5.5.5.md#nbw3-f-06-straightening-l134) |
| 135 / `nbw3-f-06-straightening-l135` | `射影 \((A,a)\mapsto A\)。cocartesian 辺は \(f\) が可逆なもの。\(A\) 上の` | [5.5.5](5.5.5.md#nbw3-f-06-straightening-l135) |
| 136 / `nbw3-f-06-straightening-l136` | `\(\mathrm{Un}(G)=B\times_{\mathrm{Cat}_\infty}\mathcal Z\)` | [5.5.5](5.5.5.md#nbw3-f-06-straightening-l136) |
| 137 / `nbw3-f-06-straightening-l137` | `空間値の \(\mathcal S_*\) では対応する射が \(F(a)\simeq b\) で、これが「すべての` | [5.5.5](5.5.5.md#nbw3-f-06-straightening-l137) |
| 142 / `nbw3-f-06-straightening-l142` | `Kerodon Construction 5.5.5.8。Hom を関手 ∞ 圏 \(\mathrm{Fun}(A,` | [5.5.5.8](5.5.5.8.md#nbw3-f-06-straightening-l142) |

### f-a-basics.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 30 / `nbw3-f-a-basics-l30` | `定義\(n\) 単体スライスとの関係 \(\mathrm{Hom}^R(x,y)\)（HTT 1.2.2、Lean ` | [4.6.5](4.6.5.md#nbw3-f-a-basics-l30) |
| 38 / `nbw3-f-a-basics-l38` | `\(\mathrm{Hom}^L,\mathrm{Hom}^R\) は左・右 fibration の点上のファイバー` | [4.6.5](4.6.5.md#nbw3-f-a-basics-l38) |
| 39 / `nbw3-f-a-basics-l39` | `\(\Delta^n\times\Delta^1\to\Delta^{n+1}\)、\((i,0)\mapsto i` | [4.6.5](4.6.5.md#nbw3-f-a-basics-l39) |
| 43 / `nbw3-f-a-basics-l43` | `HTT の定義は「\(\mathcal C_{x/}\to\mathcal C\) が trivial fibrat` | [4.7.3](4.7.3.md#nbw3-f-a-basics-l43) |
| 44 / `nbw3-f-a-basics-l44` | `充満部分圏（HTT 1.2.11）：頂点の集合 \(S\) に対し、すべての頂点が \(S\) に入る単体の全体。\` | [4.7.3](4.7.3.md#nbw3-f-a-basics-l44) |
| 45 / `nbw3-f-a-basics-l45` | `始対象全体の充満部分圏は空か可縮な Kan 複体（HTT 1.2.12.9）：射がすべて同値なので Kan 複体、\` | [4.7.3](4.7.3.md#nbw3-f-a-basics-l45) |
| 61 / `nbw3-f-a-basics-l61` | `射影 \(\mathcal C_{p/}\to\mathcal C\) が左 fibration であることを示せば` | [4.3.6.4](4.3.6.4.md#nbw3-f-a-basics-l61) |
| 63 / `nbw3-f-a-basics-l63` | `Joyal の補題（HTT 2.1.2.3）` | [4.3.6.4](4.3.6.4.md#nbw3-f-a-basics-l63) |
| 64 / `nbw3-f-a-basics-l64` | `\(A\subseteq B\) が単射、\(A'\subseteq B'\) が left anodyne なら ` | [4.3.6.4](4.3.6.4.md#nbw3-f-a-basics-l64) |
| 65 / `nbw3-f-a-basics-l65` | `\[\partial\Delta^m\star\Delta^n\ \cup\ \Delta^m\star\Lambd` | [4.3.6.4](4.3.6.4.md#nbw3-f-a-basics-l65) |
| 66 / `nbw3-f-a-basics-l66` | `面を \(S=S_1\sqcup S_2\) で表すと、左辺に入る条件「\(S_1\ne[m]\) または \(S_` | [4.3.6.4](4.3.6.4.md#nbw3-f-a-basics-l66) |
| 68 / `nbw3-f-a-basics-l68` | `\((m,n,j)\)合併に入る面結果 \((0,1,0)\)\(\{0,1\},\{1,2\}\)\(\Lambd` | [4.3.6.4](4.3.6.4.md#nbw3-f-a-basics-l68) |
| 76 / `nbw3-f-a-basics-l76` | `fat slice \(\mathcal C^{x/}\) は、\(\partial\Delta^1\subsete` | [4.3.6](4.3.6.md#nbw3-f-a-basics-l76) |
| 80 / `nbw3-f-a-basics-l80` | `3 単体は四角形と対角線 2 本で、二通りの三角形分割 \(\{012,023\}\)、\(\{013,123\}\` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l80) |
| 82 / `nbw3-f-a-basics-l82` | `01234 d₄d₂d₀d₃d₁ f₄∘(f₃∘(f₂∘f₁)) f₄∘((f₃∘f₂)∘f₁) (f₄∘(f₃∘f` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l82) |
| 115 / `nbw3-f-a-basics-l115` | `面頂点associator種類 \(d_0\)1234\(\alpha_{f_4,f_3,f_2}\circ f_1` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l115) |
| 124 / `nbw3-f-a-basics-l124` | `頂点を \((t,t^2,t^3,t^4)\) 上に置いて最後の座標を落とすと、像は三角両錐（頂点 1, 3、赤道 ` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l124) |
| 126 / `nbw3-f-a-basics-l126` | `\(\sigma\colon\Delta^n\to\mathcal C\) は \(\mathrm{Map}(\si` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l126) |
| 128 / `nbw3-f-a-basics-l128` | `012301302303 123012013023 n = 3：Map(0,3) は正方形 n = 4：Map(0,` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l128) |
| 148 / `nbw3-f-a-basics-l148` | `\(n=4\) の立方体の 6 面：座標 \(i=1,2,3\) を 0 に固定すると \(d_1,d_2,d_3\` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l148) |
| 149 / `nbw3-f-a-basics-l149` | `inner horn \(\Lambda^4_k\)（\(k=1,2,3\)）：欠けた面 \(d_k\) は立方体の` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l149) |
| 150 / `nbw3-f-a-basics-l150` | `左 horn \(\Lambda^4_0\)：欠けた \(d_0\) は \(f_1^*\colon\mathrm{` | [2.4.3](2.4.3.md#nbw3-f-a-basics-l150) |
| 156 / `nbw3-f-a-basics-l156` | `極限（HTT 1.2.13.4）：\(\mathcal C_{/p}\) の終対象。fat slice では \(\` | [7.1.3](7.1.3.md#nbw3-f-a-basics-l156) |
| 157 / `nbw3-f-a-basics-l157` | `関手性：極限錐全体の充満部分圏 \(\mathcal D\subseteq\mathrm{Fun}(K^{\tria` | [7.1.3](7.1.3.md#nbw3-f-a-basics-l157) |
| 159 / `nbw3-f-a-basics-l159` | `随伴の定義データ他の定義を導くのに必要なもの 対応（HTT 5.2.2.1）：\(\Delta^1\) 上の対応で ` | [7.1.3](7.1.3.md#nbw3-f-a-basics-l159) |
| 166 / `nbw3-f-a-basics-l166` | `随伴関手定理（HTT 5.5.2.9）：presentable の間で、右随伴を持つ ⇔ 小さい余極限を保つ。左随伴` | [7.1.3](7.1.3.md#nbw3-f-a-basics-l166) |

### f-b-literature-yoneda.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 63 / `nbw3-f-b-literature-yoneda-l63` | `節内容 7.1 極限と余極限定義（スライスの終対象）と形式的性質。定数図式、極限を保つこと、相対的な始・終対象と極限` | [7.1](7.1.md#nbw3-f-b-literature-yoneda-l63) |
| 73 / `nbw3-f-b-literature-yoneda-l73` | `7.4 は、一般の定義で定まる極限・余極限が \(\mathcal S\) と \(\mathrm{Cat}_\in` | [7.1](7.1.md#nbw3-f-b-literature-yoneda-l73) |
| 74 / `nbw3-f-b-literature-yoneda-l74` | `小節図式具体形 7.4.1\(C\to\mathcal S\) の極限分類する左 fibration の切断の空間 ` | [7.1](7.1.md#nbw3-f-b-literature-yoneda-l74) |
| 82 / `nbw3-f-b-literature-yoneda-l82` | `1 圏では、集合値なら極限は Grothendieck 構成の切断の集合、余極限はその \(\pi_0\)。\(\m` | [7.1](7.1.md#nbw3-f-b-literature-yoneda-l82) |
| 86 / `nbw3-f-b-literature-yoneda-l86` | `\(e\colon C'\to C\) が cofinal とは、どんな \(F\colon C\to\mathca` | [7.2](7.2.md#nbw3-f-b-literature-yoneda-l86) |
| 88 / `nbw3-f-b-literature-yoneda-l88` | `余極限を簡単にする：終対象 \(t\) があれば \(\operatorname{colim}_C F\simeq ` | [7.2](7.2.md#nbw3-f-b-literature-yoneda-l88) |
| 89 / `nbw3-f-b-literature-yoneda-l89` | `他の一般論の土台：Kan 拡張の各点公式、極限の推移性、Ind とコンパクト対象（密度、単一の filtered 図` | [7.2](7.2.md#nbw3-f-b-literature-yoneda-l89) |
| 90 / `nbw3-f-b-literature-yoneda-l90` | `不変性：cofinal は「制限が余極限を変えない」という極限の理論の中での同値の概念。モデル圏での「ホモトピー余極` | [7.2](7.2.md#nbw3-f-b-literature-yoneda-l90) |
| 91 / `nbw3-f-b-literature-yoneda-l91` | `1 圏の final functor は「\(c\downarrow e\) が空でなく連結」。∞ 版では連結が弱可` | [7.2](7.2.md#nbw3-f-b-literature-yoneda-l91) |
| 92 / `nbw3-f-b-literature-yoneda-l92` | `単射が left anodyne ⇔ left cofinal。§6 の「始対象の包含は left anodyne」` | [7.2](7.2.md#nbw3-f-b-literature-yoneda-l92) |
| 99 / `nbw3-f-b-literature-yoneda-l99` | `極限の一般化：各点の右 Kan 拡張は \(\mathrm{Ran}_fF(d)=\lim(d\downarrow ` | [7.3](7.3.md#nbw3-f-b-literature-yoneda-l99) |
| 100 / `nbw3-f-b-literature-yoneda-l100` | `整合的な関手を作る手段：\(C_0\subseteq C\) 上の関手を左 Kan 拡張した関手の全体は \(\ma` | [7.3](7.3.md#nbw3-f-b-literature-yoneda-l100) |
| 103 / `nbw3-f-b-literature-yoneda-l103` | `場面Kan 拡張としての捉え方 前層の普遍性余極限を保つ \(\mathcal P(A)\to\mathcal D\` | [7.3](7.3.md#nbw3-f-b-literature-yoneda-l103) |
| 111 / `nbw3-f-b-literature-yoneda-l111` | `関手を作る手段として、第 6 章 §8 の (a) 厳密な単体的関手、(b) straightening に加え、(` | [7.3](7.3.md#nbw3-f-b-literature-yoneda-l111) |
| 113 / `nbw3-f-b-literature-yoneda-l113` | `1 圏での主張∞ 版 極限は一点への Kan 拡張成り立つ（§4.4） \(G\) が左随伴を持つ ⇔ \(\mat` | [7.3](7.3.md#nbw3-f-b-literature-yoneda-l113) |
| 121 / `nbw3-f-b-literature-yoneda-l121` | `∞ では各点の Kan 拡張を定義に採るのが普通（Kerodon 7.3.1）。それが存在するとき制限の随伴になるこ` | [7.3](7.3.md#nbw3-f-b-literature-yoneda-l121) |
| 123 / `nbw3-f-b-literature-yoneda-l123` | `大域的には、\(\mathrm{Ran}_f\) は制限 \(f^*\colon\mathrm{Fun}(D,\ma` | [7.3](7.3.md#nbw3-f-b-literature-yoneda-l123) |
| 128 / `nbw3-f-b-literature-yoneda-l128` | `∞ 圏論の中では極限そのものが最初からホモトピー不変で、別の概念としてのホモトピー極限は要らない（∞ 極限を慣習的に` | [7.5](7.5.md#nbw3-f-b-literature-yoneda-l128) |
| 129 / `nbw3-f-b-literature-yoneda-l129` | `ホモトピー極限が意味を持つのは厳密な図式 \(C\to\mathrm{Kan}\)（または quasicategor` | [7.5](7.5.md#nbw3-f-b-literature-yoneda-l129) |
| 130 / `nbw3-f-b-literature-yoneda-l130` | `7.5 は、それが \(N(C)\to\mathcal S\)（または \(\mathcal{QC}\)）と見たとき` | [7.5](7.5.md#nbw3-f-b-literature-yoneda-l130) |
| 131 / `nbw3-f-b-literature-yoneda-l131` | `扱うのは Kan 複体と ∞ 圏の場合だけで、モデル構造も使わない。一般のモデル圏との比較は ModelBridge` | [7.5](7.5.md#nbw3-f-b-literature-yoneda-l131) |
| 156 / `nbw3-f-b-literature-yoneda-l156` | `部品 A：\(\mathrm{id}_b\) は \(B_{b/}\) の始対象` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l156) |
| 157 / `nbw3-f-b-literature-yoneda-l157` | `\(\partial\Delta^n\to B_{b/}\)（頂点 0 が \(\mathrm{id}_b\)）の延` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l157) |
| 160 / `nbw3-f-b-literature-yoneda-l160` | `部品 B：始対象の包含は left anodyne` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l160) |
| 161 / `nbw3-f-b-literature-yoneda-l161` | `始対象 \(x\) について \(\{x\}\hookrightarrow X\) は left anodyne。一` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l161) |
| 164 / `nbw3-f-b-literature-yoneda-l164` | `部品 C：left anodyne に沿った相対関手空間の制限は trivial fibration` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l164) |
| 165 / `nbw3-f-b-literature-yoneda-l165` | `\(i\colon K\hookrightarrow L\) が \(B\) 上の left anodyne、\(E` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l165) |
| 167 / `nbw3-f-b-literature-yoneda-l167` | `組み立て：A で \(\mathrm{id}_b\) が始対象、B で \(\{\mathrm{id}_b\}\ho` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l167) |
| 168 / `nbw3-f-b-literature-yoneda-l168` | `逆写像の直観：切断が与える \(\sigma_e\colon B_{b/}\to E\) は \(f\colon b` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l168) |
| 169 / `nbw3-f-b-literature-yoneda-l169` | `系（fibration レベルの Yoneda 埋め込み）：\(E=B_{c/}\) とすると \(\mathrm{` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l169) |
| 170 / `nbw3-f-b-literature-yoneda-l170` | `前層版：前層 ⇔ \(C\) 上の右 fibration、\(h_y\) ⇔ \(C_{/y}\to C\)、主張は` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l170) |
| 173 / `nbw3-f-b-literature-yoneda-l173` | `Hom 関手 \(C^{\mathrm{op}}\times C\to\mathcal S\) の作り方は三つ：tw` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l173) |
| 174 / `nbw3-f-b-literature-yoneda-l174` | `\[\mathrm{Map}(h_y,F)\xrightarrow[h_1]{\simeq}\mathrm{Fun}` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l174) |
| 175 / `nbw3-f-b-literature-yoneda-l175` | `段内容 \(h_1\)前層の写像空間 ≃ unstraightening の相対関手空間（最も重い入力） \(h_2` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l175) |
| 182 / `nbw3-f-b-literature-yoneda-l182` | `充満忠実性（yonedaInfinityMap_isFullyFaithful）は、同値 \(\mathrm{Map` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l182) |
| 188 / `nbw3-f-b-literature-yoneda-l188` | `始対象 \(x\) の持ち上げ条件：すべての \(n\ge 1\) について、頂点 0 が \(x\) の \(\p` | [4.7.3](4.7.3.md#nbw3-f-b-literature-yoneda-l188) |
| 190 / `nbw3-f-b-literature-yoneda-l190` | `join で翻訳：\(u\colon\partial\Delta^n\to B_{b/}\)（頂点 0 が \(\m` | [4.7.3](4.7.3.md#nbw3-f-b-literature-yoneda-l190) |
| 191 / `nbw3-f-b-literature-yoneda-l191` | `同定：\(\Delta^{n+1}\) の頂点を 0（錐）と \(1,\dots,n+1\) とすると、面 \(S\` | [4.7.3](4.7.3.md#nbw3-f-b-literature-yoneda-l191) |
| 192 / `nbw3-f-b-literature-yoneda-l192` | `最初の辺：頂点 0 が \(\mathrm{id}_b\) なので、horn の辺 \(0\to 1\) は \(s` | [4.7.3](4.7.3.md#nbw3-f-b-literature-yoneda-l192) |
| 193 / `nbw3-f-b-literature-yoneda-l193` | `Joyal の定理（HTT 1.2.4.3）：\(m\ge 2\) で \(\Lambda^m_0\to B\) の` | [4.7.3](4.7.3.md#nbw3-f-b-literature-yoneda-l193) |
| 195 / `nbw3-f-b-literature-yoneda-l195` | `例内容 \(n=1\)頂点 \(\mathrm{id}_b\) と \(f\colon b\to c\)。\(\La` | [4.7.3](4.7.3.md#nbw3-f-b-literature-yoneda-l195) |
| 200 / `nbw3-f-b-literature-yoneda-l200` | `一般の頂点 \(f\colon b\to c\) では最初の辺が \(f\) になるので、\(f\) が同値なら始対` | [4.7.3](4.7.3.md#nbw3-f-b-literature-yoneda-l200) |
| 204 / `nbw3-f-b-literature-yoneda-l204` | `切断：\(X_{x/}\to X\) は trivial fibration なので、\(\{x\}\hookrig` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l204) |
| 205 / `nbw3-f-b-literature-yoneda-l205` | `join へ：\(s\) は \(\tilde s\colon\Delta^0\star X\to X\)（錐の頂点` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l205) |
| 206 / `nbw3-f-b-literature-yoneda-l206` | `直積へ：fat join から join へのつぶす写像 \(c\colon\Delta^1\times X\to\` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l206) |
| 207 / `nbw3-f-b-literature-yoneda-l207` | `retract：\(j\colon(\{0\}\times X)\cup(\Delta^1\times\{x\})\` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l207) |
| 209 / `nbw3-f-b-literature-yoneda-l209` | `逆に、包含が left anodyne なら \(x\) は始対象で、両者は同値。ただし逆向きは直接の議論ではなく、` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l209) |
| 212 / `nbw3-f-b-literature-yoneda-l212` | `方法適用範囲使うもの選択部品 A 1. 持ち上げで切断を選ぶ（7.2）一般の始対象trivial fibration` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l212) |
| 218 / `nbw3-f-b-literature-yoneda-l218` | `参考：任意の \(K\) について錐の頂点の包含 \(\{\ast\}\hookrightarrow\Delta^0` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l218) |
| 221 / `nbw3-f-b-literature-yoneda-l221` | `単射が left anodyne ⇔ すべての左 fibration に対して左持ち上げ性質を持つ（small ob` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l221) |
| 223 / `nbw3-f-b-literature-yoneda-l223` | `底の取り替え：\(E'=X\times_SE\to X\) は左 fibration。必要なのは切断 \(\tau\` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l223) |
| 224 / `nbw3-f-b-literature-yoneda-l224` | `縮約：7.2 の \(h\)（\(B_{b/}\) なら \(s_0\) で具体的に）。` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l224) |
| 225 / `nbw3-f-b-literature-yoneda-l225` | `引き戻して持ち上げ：\(h^*E'\to\Delta^1\times X\) は左 fibration。\(A=(\` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l225) |
| 226 / `nbw3-f-b-literature-yoneda-l226` | `制限：\(\{1\}\times X\) に制限すると \(E'\to X\) の切断で、\((1,x)\in A\` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l226) |
| 228 / `nbw3-f-b-literature-yoneda-l228` | `直観：時刻 0 ではすべてが \(x\) に縮んでいるので \(e'\) を置くだけ。left fibration ` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l228) |
| 229 / `nbw3-f-b-literature-yoneda-l229` | `部品 B と C をまとめて：\(\mathrm{ev}_x\colon\mathrm{Fun}_{/X}(X,E'` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l229) |
| 230 / `nbw3-f-b-literature-yoneda-l230` | `証明の組み立て使うもの A → B（retract）→ CJoyal の定理、切断の選択、retract での閉性、` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l230) |
| 236 / `nbw3-f-b-literature-yoneda-l236` | `\(X=B_{b/}\) なら \(h\) が \(s_0\) で書けるので、最後の方法は Joyal の定理も切断` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l236) |
| 242 / `nbw3-f-b-literature-yoneda-l242` | `関手としてfibration として ∞ 圏\(\mathcal P(C)=\mathrm{Fun}(C^{\mat` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l242) |
| 249 / `nbw3-f-b-literature-yoneda-l249` | `\(\mathcal S\) は小さい Kan 複体の全体なので \(\mathcal P(C)\) は一つ上の宇宙` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l249) |
| 252 / `nbw3-f-b-literature-yoneda-l252` | `\[\mathrm{Map}_{\mathcal P(C)}(F,G)\;\simeq\;\mathrm{Fun}_` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l252) |
| 253 / `nbw3-f-b-literature-yoneda-l253` | `unstraightening が写像空間で充満忠実であることそのもので、形式化の Yoneda の証明の \(h_` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l253) |
| 257 / `nbw3-f-b-literature-yoneda-l257` | `左辺（\(K=C^{\mathrm{op}}\)）：写像空間の定義 (b) により \(\{F\}\times\ma` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l257) |
| 258 / `nbw3-f-b-literature-yoneda-l258` | `右辺：点は \(K\) 上の写像 \(\mathrm{Un}\,F\to\mathrm{Un}\,G\)。` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l258) |
| 259 / `nbw3-f-b-literature-yoneda-l259` | `橋渡し：\(\mathrm{Un}(\alpha)\) は \(\Delta^1\times K\) 上の左 fib` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l259) |
| 262 / `nbw3-f-b-literature-yoneda-l262` | `左 fibration から写像へ（transport）` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l262) |
| 263 / `nbw3-f-b-literature-yoneda-l263` | `\(Y\to\Delta^1\times K\) を左 fibration（両端 \(X_0,X_1\)）とする。\` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l263) |
| 266 / `nbw3-f-b-literature-yoneda-l266` | `写像から左 fibration へ（写像柱）` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l266) |
| 267 / `nbw3-f-b-literature-yoneda-l267` | `\(\varphi\colon X_0\to X_1\) に対し \(M_\varphi=(\Delta^1\tim` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l267) |
| 269 / `nbw3-f-b-literature-yoneda-l269` | `空間の同値にするには、すべての次元の単体で同じ対応を作る。\(n\) 単体は \(\Delta^n\) をパラメータ` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l269) |
| 272 / `nbw3-f-b-literature-yoneda-l272` | `場面関手の言葉fibration の言葉 Yoneda\(\mathrm{Map}(h_y,F)\)\(\mathr` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l272) |
| 279 / `nbw3-f-b-literature-yoneda-l279` | `関手の言葉の問いを fibration に移すと、多くは持ち上げや切断の問題になり、left anodyne・pus` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l279) |
| 288 / `nbw3-f-b-literature-yoneda-l288` | `∞ 関手 \(C^{\mathrm{op}}\to\mathcal S\) は単体的関手 \(\mathfrak C` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l288) |
| 291 / `nbw3-f-b-literature-yoneda-l291` | `値を \(X_c\) の代わりに \(\mathrm{St}(X)(c):=\mathrm{Fun}_{/N(C)}` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l291) |
| 293 / `nbw3-f-b-literature-yoneda-l293` | `厳密に関手的：\(f\colon c\to c'\) に対し \(f^\sharp\colon C_{c'/}\to` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l293) |
| 294 / `nbw3-f-b-literature-yoneda-l294` | `値は正しい：\(\mathrm{id}_c\) は \(C_{c/}\) の始対象なので、\(\mathrm{id}` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l294) |
| 295 / `nbw3-f-b-literature-yoneda-l295` | `射の作用：切断 \(\sigma\) を \(f^\sharp\) で制限して \(\mathrm{id}_{c'}` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l295) |
| 297 / `nbw3-f-b-literature-yoneda-l297` | `ファイバーを表現可能な fibration からの切断空間に置き換えることで、値を変えずに厳密な関手性を得る。選択は` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l297) |
| 301 / `nbw3-f-b-literature-yoneda-l301` | `定義：\(\mathrm{Fun}_{/S}(K,X)=\mathrm{Fun}(K,X)\times_{\math` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l301) |
| 302 / `nbw3-f-b-literature-yoneda-l302` | `Kan 複体（\(X\to S\) が左 fibration のとき）：(1) \(\mathrm{Fun}(K,X` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l302) |
| 303 / `nbw3-f-b-literature-yoneda-l303` | `写像空間として：\(N(C_{c/})\to N(C)\) 自身が左 fibration なので \(\mathrm` | [5.3.1](5.3.1.md#nbw3-f-b-literature-yoneda-l303) |
| 307 / `nbw3-f-b-literature-yoneda-l307` | `対象定義（コード） 単体の圏TransportSimplexCategory B：対象は \(B\) の単体 \(\` | [6.3.6.5](6.3.6.5.md#nbw3-f-b-literature-yoneda-l307) |
| 313 / `nbw3-f-b-literature-yoneda-l313` | `\(X\) を \(\mathrm{fv}\) で引き戻して第一段を適用すると \(W\) を反転する関手が得られ、` | [6.3.6.5](6.3.6.5.md#nbw3-f-b-literature-yoneda-l313) |
| 316 / `nbw3-f-b-literature-yoneda-l316` | `IsLocalization F W（F1B）：\(F\colon X\to D\) が \(W\) を可逆にし、す` | [6.3.6.5](6.3.6.5.md#nbw3-f-b-literature-yoneda-l316) |
| 319 / `nbw3-f-b-literature-yoneda-l319` | `主定理 transportSimplexFirstVertexMap_isLocalization。\(P(X)\)` | [6.3.6.5](6.3.6.5.md#nbw3-f-b-literature-yoneda-l319) |
| 320 / `nbw3-f-b-literature-yoneda-l320` | `部品内容ファイル 1. 標準単体切断 \(s\colon\Delta^n\to N(\cdot)\)（各頂点 \(i` | [6.3.6.5](6.3.6.5.md#nbw3-f-b-literature-yoneda-l320) |
| 327 / `nbw3-f-b-literature-yoneda-l327` | `組み立て（LocalizationAllBases）：0 次元の骨格（点の余積）から始め、\(n+1\) 次元の骨格` | [6.3.6.5](6.3.6.5.md#nbw3-f-b-literature-yoneda-l327) |
| 331 / `nbw3-f-b-literature-yoneda-l331` | `\(h_y=\mathrm{Map}(-,y)\) は \(x\) について反変なので \(C^{\mathrm{o` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l331) |
| 332 / `nbw3-f-b-literature-yoneda-l332` | `定義（形式化）：\(\mathrm{Tw}(C)\to C^{\mathrm{op}}\times C\)（左 fi` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l332) |
| 333 / `nbw3-f-b-literature-yoneda-l333` | `スライスとの比較：\(C_{/y}\to C\) は右 fibration、\(C^{\mathrm{op}}_{y` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l333) |
| 335 / `nbw3-f-b-literature-yoneda-l335` | `Hom 関手の値（定義）スライスの St（比較） \(y\) についての関手性ある（Yoneda 埋め込み）ない（\` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l335) |
| 341 / `nbw3-f-b-literature-yoneda-l341` | `\(C\) が普通の圏の脈体なら、スライスの St の値は \(\mathrm{Fun}_{/N(C^{\mathr` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l341) |
| 342 / `nbw3-f-b-literature-yoneda-l342` | `段整合性の処理 fibrationtransport と整合性は持ち上げ性質（Prop） 第一段\(c\mapsto` | [5.6.6](5.6.6.md#nbw3-f-b-literature-yoneda-l342) |
| 352 / `nbw3-f-b-literature-yoneda-l352` | `fibration 版 Yoneda（§6、§7）：\(\mathrm{Fun}_{/B}(B_{b/},E)\to` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l352) |
| 353 / `nbw3-f-b-literature-yoneda-l353` | `St の構成（9.3〜9.7）：第一段で値を切断空間 \(\mathrm{Fun}_{/N(C)}(N(C_{c/}` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l353) |
| 354 / `nbw3-f-b-literature-yoneda-l354` | `Map と Yoneda 埋め込み（9.8）：\(\mathrm{Tw}(C)\) の St を curry する。` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l354) |
| 355 / `nbw3-f-b-literature-yoneda-l355` | `関手版 Yoneda（§6.4）：\(\mathrm{Map}(h_y,F)\xrightarrow{h_1}\ma` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l355) |
| 357 / `nbw3-f-b-literature-yoneda-l357` | `fibration 版 Yoneda は二度使われる：St の値が正しいことを保証するため（2）と、関手版の値を計算` | [8.3.3](8.3.3.md#nbw3-f-b-literature-yoneda-l357) |
| 365 / `nbw3-f-b-literature-yoneda-l365` | `\(B\)：単体的集合（quasicategory でなくてよい）。\(p\colon E\to B\)：左 fib` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l365) |
| 366 / `nbw3-f-b-literature-yoneda-l366` | `\(E_b=\{b\}\times_BE\)：厳密な引き戻し。\(p\) は isofibration なので ∞ ` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l366) |
| 367 / `nbw3-f-b-literature-yoneda-l367` | `\(B_{b/}\)：join スライス（\(n\) 単体は頂点 0 が \(b\) の \(\Delta^{n+1` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l367) |
| 368 / `nbw3-f-b-literature-yoneda-l368` | `\(\mathrm{Fun}_{/B}(B_{b/},E)=\mathrm{Fun}(B_{b/},E)\times` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l368) |
| 369 / `nbw3-f-b-literature-yoneda-l369` | `評価写像：\(\mathrm{id}_b=s_0(b)\) は \(b\) の上にあるので \(i\colon\{\` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l369) |
| 373 / `nbw3-f-b-literature-yoneda-l373` | `内部 Hom の普遍性 \(\{K\to\mathrm{Fun}(L,E)\}\cong\{K\times L\to` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l373) |
| 374 / `nbw3-f-b-literature-yoneda-l374` | `\[\{K\to\mathrm{Fun}_{/B}(L,E)\}\cong\{g\colon K\times L\t` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l374) |
| 375 / `nbw3-f-b-literature-yoneda-l375` | `（\(K\times L\) を \(L\) 経由で \(B\) 上にあるとみたときの \(B\) 上の写像）。\(` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l375) |
| 376 / `nbw3-f-b-literature-yoneda-l376` | `持ち上げ問題読み替え後 上の写像 \(u\colon\partial\Delta^n\to\mathrm{Fun}_` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l376) |
| 383 / `nbw3-f-b-literature-yoneda-l383` | `\(\tilde u,\tilde v\) は合併 \((\partial\Delta^n\times L)\cup` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l383) |
| 386 / `nbw3-f-b-literature-yoneda-l386` | `\(j_n\) は単射 \(\partial\Delta^n\subseteq\Delta^n\) と \(i\) ` | [4.2.5.4](4.2.5.4.md#nbw3-f-b-literature-yoneda-l386) |
| 389 / `nbw3-f-b-literature-yoneda-l389` | `\(X=B_{b/}\)。\(\Delta^1\times X\) の \(n\) 単体 \((\alpha,\si` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l389) |
| 390 / `nbw3-f-b-literature-yoneda-l390` | `\[\rho_k\colon[n+1]\to[n+1],\quad\rho_k(j)=\begin{cases}0&` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l390) |
| 391 / `nbw3-f-b-literature-yoneda-l391` | `錐の頂点と最初の \(k\) 個の頂点をまとめて \(b\) につぶす操作。\(\rho_k\) は単調で 0 を ` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l391) |
| 392 / `nbw3-f-b-literature-yoneda-l392` | `制限値理由 \(\{1\}\times X\)（\(k=0\)）恒等\(\rho_0=\mathrm{id}\) \` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l392) |
| 398 / `nbw3-f-b-literature-yoneda-l398` | `\(j\colon(\{0\}\times X)\cup(\Delta^1\times\{\mathrm{id}_b` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l398) |
| 399 / `nbw3-f-b-literature-yoneda-l399` | `\[\text{縮約 }h\text{（式）}\Rightarrow i\text{ は left anodyne}` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l399) |
| 400 / `nbw3-f-b-literature-yoneda-l400` | `使うのは相対関手空間の普遍性、pushout-product の補題、retract での閉性、\(h\) の式だけ` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l400) |
| 403 / `nbw3-f-b-literature-yoneda-l403` | `\(X\) が quasicategory で \(x\) が始対象なら \(\{x\}\hookrightarro` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l403) |
| 404 / `nbw3-f-b-literature-yoneda-l404` | `一般の始対象スライス \(B_{b/}\) と \(\mathrm{id}_b\) 縮約 \(h\)trivial ` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l404) |
| 409 / `nbw3-f-b-literature-yoneda-l409` | `逆向き（包含が left anodyne なら始対象）も成り立ち同値だが、直接の議論では示せず、left anody` | [4.2.5](4.2.5.md#nbw3-f-b-literature-yoneda-l409) |
| 414 / `nbw3-f-b-literature-yoneda-l414` | `\(C\) は quasicategory、\(p\colon K\to C\)、錐 \(\bar p\colon\` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l414) |
| 415 / `nbw3-f-b-literature-yoneda-l415` | `定義種類 (1)\(\bar p\) は \(C_{/p}\) の終対象（HTT 1.2.13.4）スライスの終対象` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l415) |
| 426 / `nbw3-f-b-literature-yoneda-l426` | `定義でなく計算公式：\(\mathcal S\) では \(\lim F\simeq\mathrm{Fun}_{/K` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l426) |
| 430 / `nbw3-f-b-literature-yoneda-l430` | `\(C_{/p}\)：\(n\) 単体は \(p\) を延長する \(\Delta^n\star K\to C\)。` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l430) |
| 431 / `nbw3-f-b-literature-yoneda-l431` | `\(\mathrm{Hom}^R_C(Y,X)=\{Y\}\times_CC_{/X}\)、錐の空間 \(\math` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l431) |
| 432 / `nbw3-f-b-literature-yoneda-l432` | `\(D\) の対象 \(x\) が終対象 ⇔ すべての \(y\) で \(\mathrm{Hom}^R_D(y,x` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l432) |
| 433 / `nbw3-f-b-literature-yoneda-l433` | `(3) は zigzag \(\mathrm{Hom}^R_C(Y,X)\xleftarrow{\sim}\{Y\}` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l433) |
| 437 / `nbw3-f-b-literature-yoneda-l437` | `補題内容 A（join の持ち上げ）単射 \(A\subseteq B\)、\(q\colon B\to C\)。\` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l437) |
| 445 / `nbw3-f-b-literature-yoneda-l445` | `\(C_{/p}\) 上の同型 \((C_{/p})_{/\bar p}\cong C_{/\bar p}\)：左辺` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l445) |
| 449 / `nbw3-f-b-literature-yoneda-l449` | `\(r\colon C_{/\bar p}\to C_{/p}\) は右 fibration（補題 A で \(i=` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l449) |
| 450 / `nbw3-f-b-literature-yoneda-l450` | `\(r\) は \(C\) 上の右 fibration どうしの写像。\(r_Y\) は Kan 複体の間の右 fi` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l450) |
| 451 / `nbw3-f-b-literature-yoneda-l451` | `(2) ⇔ \(r\) のファイバーがすべて可縮（補題 B）⇔ 各 \(r_Y\) のファイバーがすべて可縮 ⇔ 各` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l451) |
| 453 / `nbw3-f-b-literature-yoneda-l453` | `重いのは補題 B の ⇐ だけで、残りは join の組合せ論と持ち上げ。` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l453) |
| 456 / `nbw3-f-b-literature-yoneda-l456` | `場面使い方 右随伴は極限を保つ\(\mathrm{Map}(Y,GX)\simeq\mathrm{Map}(FY,X` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l456) |
| 464 / `nbw3-f-b-literature-yoneda-l464` | `(1)/(2) で済むもの：錐としての一意性（終対象の空間が可縮）、cofinal な前合成での不変性、関手圏の極限` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l464) |
| 465 / `nbw3-f-b-literature-yoneda-l465` | `(3) の段階右辺必要なもの join 版\(\mathrm{Cone}(Y,p)\)持ち上げだけ（11.5） fa` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l465) |
| 471 / `nbw3-f-b-literature-yoneda-l471` | `形式化では定義に (1) か (2) を採り、(3) の join 版をすぐ示せる特徴づけとし、fat 版と極限公式` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l471) |
| 474 / `nbw3-f-b-literature-yoneda-l474` | `Kerodon は随伴（単位 \(\eta\) と、各点で \(\mathrm{Hom}(FX,Y)\to\math` | [7.1.3](7.1.3.md#nbw3-f-b-literature-yoneda-l474) |
| 479 / `nbw3-f-b-literature-yoneda-l479` | `\(F\colon C\to D\)、\(G\colon D\to C\) は quasicategory 間の関手` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l479) |
| 480 / `nbw3-f-b-literature-yoneda-l480` | `定義1 圏での対応物 (A) 単位自然変換 \(\eta\colon\mathrm{id}_C\to GF\) で、` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l480) |
| 488 / `nbw3-f-b-literature-yoneda-l488` | `(A)〜(C) と (E) は \(\mathrm{Map}\) の関手性なしに書ける。` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l488) |
| 491 / `nbw3-f-b-literature-yoneda-l491` | `同値議論 (A) ⇔ (E)\(X\downarrow G\to D\) は左 fibration で、\(Y\) ` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l491) |
| 501 / `nbw3-f-b-literature-yoneda-l501` | `\(G\) を固定すると左随伴 \((F,\eta)\) の空間は可縮（HTT 5.2.6、Riehl–Verity` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l501) |
| 505 / `nbw3-f-b-literature-yoneda-l505` | `(A)：自然性はデータ（\(F,G\) と自然変換 \(\eta\colon\Delta^1\times C\to ` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l505) |
| 506 / `nbw3-f-b-literature-yoneda-l506` | `注意：\(\eta\) を射の族 \(\eta_X\) にしてはいけない。1 圏でも、\(F\) が先に与えられてい` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l506) |
| 507 / `nbw3-f-b-literature-yoneda-l507` | `(E)：\(F\) は与えず、\(G\) だけが関手。始対象の空間が可縮であることが \(X\mapsto FX\)` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l507) |
| 508 / `nbw3-f-b-literature-yoneda-l508` | `(D)：関手 \(C^{\mathrm{op}}\times D\to\mathcal S\) の同値として自然性を` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l508) |
| 510 / `nbw3-f-b-literature-yoneda-l510` | `どれも整合性を条件にせず、データか普遍性に任せる作りで、極限を「スライスの終対象」と定義して錐の関手性を問わないのと` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l510) |
| 513 / `nbw3-f-b-literature-yoneda-l513` | `定義役割例 (A)与えた組が随伴であることを述べ、確かめる。Prop なので定義や API の中心向き再帰的局所化（` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l513) |
| 521 / `nbw3-f-b-literature-yoneda-l521` | `六関手の構成はほぼこの順に全部を通る：\(D^*\) が presentable なので各 \(f^*\) に右随伴` | [6.2.1](6.2.1.md#nbw3-f-b-literature-yoneda-l521) |

### f-c-spaces.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 59 / `nbw3-f-c-spaces-l59` | `\(\mathfrak C[K]=\operatorname{colim}_{\Delta^n\to K}\math` | [2.4.4](2.4.4.md#nbw3-f-c-spaces-l59) |
| 60 / `nbw3-f-c-spaces-l60` | `\(K\)\(\mathrm{Hom}_{\mathfrak C[K]}(0,2)\)意味 \(\Delta^2\)` | [2.4.4](2.4.4.md#nbw3-f-c-spaces-l60) |
| 66 / `nbw3-f-c-spaces-l66` | `一般の Hom は Dugger–Spivak の necklace（\(\Delta^{n_1}\vee\cdot` | [2.4.4](2.4.4.md#nbw3-f-c-spaces-l66) |
| 72 / `nbw3-f-c-spaces-l72` | `0 単体：対象。1 単体：\(\mathcal C(x,y)\) の頂点。` | [2.4.3](2.4.3.md#nbw3-f-c-spaces-l72) |
| 73 / `nbw3-f-c-spaces-l73` | `2 単体：\(f\colon x_0\to x_1\)、\(g\colon x_1\to x_2\)、\(h\col` | [2.4.3](2.4.3.md#nbw3-f-c-spaces-l73) |
| 74 / `nbw3-f-c-spaces-l74` | `3 単体：四つの 2 単体と \(\mathcal C(x_0,x_3)\) の正方形（二通りの貼り合わせのホモトピ` | [2.4.3](2.4.3.md#nbw3-f-c-spaces-l74) |
| 75 / `nbw3-f-c-spaces-l75` | `確かめ：Hom が離散な普通の圏なら立方体からの写像は定数で、\(N^{hc}(\mathcal C)=N(\mat` | [2.4.3](2.4.3.md#nbw3-f-c-spaces-l75) |
| 87 / `nbw3-f-c-spaces-l87` | `開いた箱の包含は anodyne だが inner anodyne ではないので、Hom が quasicatego` | [2.4.5](2.4.5.md#nbw3-f-c-spaces-l87) |
| 91 / `nbw3-f-c-spaces-l91` | `\(\mathcal S=N^{hc}(\mathcal Kan)\) の単体中身 対象小さい Kan 複体 射写像` | [5.5.3](5.5.3.md#nbw3-f-c-spaces-l91) |
| 99 / `nbw3-f-c-spaces-l99` | `\(hN^{hc}(\mathcal C)\) は Hom が \(\pi_0\mathcal C(x,y)\) の` | [5.5.3](5.5.3.md#nbw3-f-c-spaces-l99) |
| 100 / `nbw3-f-c-spaces-l100` | `\(\mathcal S\) 自身は一つ上の宇宙に入るが、局所小。形式化：SpaceInfinity := Simp` | [5.5.3](5.5.3.md#nbw3-f-c-spaces-l100) |
| 101 / `nbw3-f-c-spaces-l101` | `\(\mathrm{Cat}_\infty\)：\(\mathcal{QC}at\) の Hom を core \(` | [5.5.3](5.5.3.md#nbw3-f-c-spaces-l101) |
| 106 / `nbw3-f-c-spaces-l106` | `定義特徴づけ得意なこと他との同値に必要な定理 (a) \(N^{hc}(\mathcal Kan)\)単体が具体的単` | [3.1.6](3.1.6.md#nbw3-f-c-spaces-l106) |
| 113 / `nbw3-f-c-spaces-l113` | `(b) の \(\mathcal Kan_0\) は Kan 複体と写像の普通の圏。(c) は Cisinski の` | [3.1.6](3.1.6.md#nbw3-f-c-spaces-l113) |
| 118 / `nbw3-f-c-spaces-l118` | `\(\mathcal C\) が局所 Kan なら \(\mathcal C(x,y)\simeq\mathrm{H` | [4.6.7.5](4.6.7.5.md#nbw3-f-c-spaces-l118) |
| 119 / `nbw3-f-c-spaces-l119` | `\[J^n:=(\Delta^1)^n\big/(S\sim S\cup T),\qquad\mathrm{Hom}` | [4.6.7.5](4.6.7.5.md#nbw3-f-c-spaces-l119) |
| 120 / `nbw3-f-c-spaces-l120` | `\(S\) の類は \(m(S)=\min(S\setminus\{0\})\) で決まり、\(J^n\) の頂点は` | [4.6.7.5](4.6.7.5.md#nbw3-f-c-spaces-l120) |
| 121 / `nbw3-f-c-spaces-l121` | `\(n=2\)：正方形の頂点 \(\varnothing,\{1\},\{2\},\{1,2\}\) の \(m\)` | [4.6.7.5](4.6.7.5.md#nbw3-f-c-spaces-l121) |
| 124 / `nbw3-f-c-spaces-l124` | `\(\theta=r^*\colon\mathcal C(x,y)=\mathrm{Hom}(\Delta^\bul` | [4.6.7.5](4.6.7.5.md#nbw3-f-c-spaces-l124) |
| 128 / `nbw3-f-c-spaces-l128` | `構成内容 pinched 写像空間（4.6.5.1）\(\mathrm{Hom}^L_{\mathcal C}(X,` | [4.6.7.5](4.6.7.5.md#nbw3-f-c-spaces-l128) |
| 137 / `nbw3-f-c-spaces-l137` | `命題 4.6.7.23：\(\rho_K\) はすべての \(K\) でカテゴリー同値。有限に帰着（\(\Phi\)` | [4.6.7.23](4.6.7.23.md#nbw3-f-c-spaces-l137) |
| 138 / `nbw3-f-c-spaces-l138` | `定理 4.6.7.8 ⇒ 4.6.7.5：\(\mathrm{Hom}^L\) は ∞ 圏（4.6.7.25：内部 ` | [4.6.7.8](4.6.7.8.md#nbw3-f-c-spaces-l138) |
| 142 / `nbw3-f-c-spaces-l142` | `主定理は F1/Coherent/HomEquivalence.lean の coherentHomComparis` | [4.6.7](4.6.7.md#nbw3-f-c-spaces-l142) |
| 143 / `nbw3-f-c-spaces-l143` | `Kerodonリポジトリ（F1/Coherent/）内容 \(\Phi(\Delta^n)\)（4.6.7.27）R` | [4.6.7](4.6.7.md#nbw3-f-c-spaces-l143) |
| 155 / `nbw3-f-c-spaces-l155` | `(i) 標準単体：blunt join を使わず直接縮約する。区間の切断 coherentResolutionSec` | [4.6.7](4.6.7.md#nbw3-f-c-spaces-l155) |
| 156 / `nbw3-f-c-spaces-l156` | `(ii) 一般の \(K\)：汎用補題 isPrecompositionEquivalence_natCompone` | [4.6.7](4.6.7.md#nbw3-f-c-spaces-l156) |
| 157 / `nbw3-f-c-spaces-l157` | `(iii) \(\rho\) から \(\theta\)：Kerodon の写像柱の代わりに、厳密な左逆 coher` | [4.6.7](4.6.7.md#nbw3-f-c-spaces-l157) |
| 159 / `nbw3-f-c-spaces-l159` | `論点Kerodon形式化 写像空間の向き左 pinched右 pinched（旗の順序を反転） 標準単体blunt ` | [4.6.7](4.6.7.md#nbw3-f-c-spaces-l159) |
| 170 / `nbw3-f-c-spaces-l170` | `段仮定quasicategory \(Z=\mathcal C(X,Y)\) で通るか \(N^{hc}(\math` | [4.6.7.8](4.6.7.8.md#nbw3-f-c-spaces-l170) |
| 180 / `nbw3-f-c-spaces-l180` | `一般化するなら、Kerodon 4.6.7.8 の方式（写像柱で「同型の転置は同型」を処理）、転置の可逆性を直接示す` | [4.6.7.8](4.6.7.8.md#nbw3-f-c-spaces-l180) |
| 219 / `nbw3-f-c-spaces-l219` | `\(n=0\)：\(\Delta^1\)（\(\bar0\to0\)）。頂点は \(C\) の射 \(f\colon` | [8.1.1.2](8.1.1.2.md#nbw3-f-c-spaces-l219) |
| 220 / `nbw3-f-c-spaces-l220` | `\(n=1\)：\(\Delta^3\)、\(x_1\xrightarrow{u}x_0\xrightarrow{f` | [8.1.1.2](8.1.1.2.md#nbw3-f-c-spaces-l220) |
| 221 / `nbw3-f-c-spaces-l221` | `辺意味 \((\bar1,\bar0)=u\)\(C^{\mathrm{op}}\) 成分（\(C^{\mathrm` | [8.1.1.2](8.1.1.2.md#nbw3-f-c-spaces-l221) |
| 229 / `nbw3-f-c-spaces-l229` | `四つの三角形と 3 単体が \(f_1\simeq v\circ f_0\circ u\) をすべての括弧の付け方で` | [8.1.1.2](8.1.1.2.md#nbw3-f-c-spaces-l229) |
| 230 / `nbw3-f-c-spaces-l230` | `\(n=2\)：\(\Delta^5\)、\(x_2\to x_1\to x_0\xrightarrow{f_0}y` | [8.1.1.2](8.1.1.2.md#nbw3-f-c-spaces-l230) |
| 233 / `nbw3-f-c-spaces-l233` | `左 horn \(\Lambda^n_i\)（\(0\le i<n\)）の持ち上げで与えられるのは、\(\Lambd` | [8.1.1.11](8.1.1.11.md#nbw3-f-c-spaces-l233) |
| 234 / `nbw3-f-c-spaces-l234` | `\[D=\bigcup_{\tau\subseteq\Lambda^n_i}(\tau^{\mathrm{op}}\` | [8.1.1.11](8.1.1.11.md#nbw3-f-c-spaces-l234) |
| 235 / `nbw3-f-c-spaces-l235` | `で、\(D\subseteq\Delta^{2n+1}\) が inner anodyne であることを示す（Ker` | [8.1.1.11](8.1.1.11.md#nbw3-f-c-spaces-l235) |
| 237 / `nbw3-f-c-spaces-l237` | `\(n=1\)、\(i=0\)：\(D\) は三辺 \(u\)、\(f_0\)、\(v\)、つまり \(\Delta` | [8.1.1.11](8.1.1.11.md#nbw3-f-c-spaces-l237) |
| 238 / `nbw3-f-c-spaces-l238` | `\(n=1\)、\(i=1\)（右 horn）：\(D\) は \(u\)、\(f_1\)、\(v\)。欠けた辺 \` | [8.1.1.11](8.1.1.11.md#nbw3-f-c-spaces-l238) |
| 239 / `nbw3-f-c-spaces-l239` | `\(n=2\)、\(i=0\)：\(D\) は 3 単体 \(\bar1\bar0\,01\) と \(\bar2\` | [8.1.1.11](8.1.1.11.md#nbw3-f-c-spaces-l239) |
| 240 / `nbw3-f-c-spaces-l240` | `一般の \(n\)：形式化は組合せ論の判定法で処理する（TwistedArrow/HornLifting、Simpl` | [8.1.1.11](8.1.1.11.md#nbw3-f-c-spaces-l240) |
| 244 / `nbw3-f-c-spaces-l244` | `\((x,y)\) 上のファイバーの \(n\) 単体は、左半分がすべて \(x\)、右半分がすべて \(y\) の` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l244) |
| 246 / `nbw3-f-c-spaces-l246` | `0 単体：射 \(f\colon x\to y\)。` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l246) |
| 247 / `nbw3-f-c-spaces-l247` | `1 単体：3 単体 \(x\xrightarrow{\mathrm{id}}x\to y\xrightarrow{\` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l247) |
| 249 / `nbw3-f-c-spaces-l249` | `比較写像（cosliceTwistedHomMap）：左半分を錐点につぶす崩壊 \((\Delta^n)^{\mat` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l249) |
| 250 / `nbw3-f-c-spaces-l250` | `証明（TwistedHomRows、TwistedHomDiagonal、Joins/CosliceTwistedH` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l250) |
| 252 / `nbw3-f-c-spaces-l252` | `左の大きさ \(m\) と右の大きさ \(n\) を別々に動かした二重単体集合 \(R_{m,n}=\{(\Delt` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l252) |
| 253 / `nbw3-f-c-spaces-l253` | `\(m\) を固定した行は、退化単体 \(\sigma\)（\(x\) の \(m\) 単体）の下のスライス \(C` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l253) |
| 254 / `nbw3-f-c-spaces-l254` | `各行で同値なら対角でも同値（localized_diagonal_map）。` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l254) |
| 255 / `nbw3-f-c-spaces-l255` | `\(R\) の対角 \(R_{n,n}\) は \(\mathrm{Tw}(C)_{(x,y)}\)、定数の側の対角` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l255) |
| 257 / `nbw3-f-c-spaces-l257` | `自然性の問題は行ごとに \(m\) を固定して避け、対角補題が全体をまとめる。` | [8.1.1](8.1.1.md#nbw3-f-c-spaces-l257) |
| 270 / `nbw3-f-c-spaces-l270` | `比較議論形式化 (a) \(\mathrm{id}_x\) は \(\mathrm{Tw}_x=\{x\}\time` | [8.1.2](8.1.2.md#nbw3-f-c-spaces-l270) |
| 280 / `nbw3-f-c-spaces-l280` | `方法内容難点 Tw の St（採用）11.1〜11.7一般の底の St が要る \(\mathfrak C[C]\)` | [8.1.2](8.1.2.md#nbw3-f-c-spaces-l280) |
| 287 / `nbw3-f-c-spaces-l287` | `流れ「fibration 版 Yoneda → St → Map → 関手版 Yoneda」の中で、\(\mathr` | [8.1.2](8.1.2.md#nbw3-f-c-spaces-l287) |
| 288 / `nbw3-f-c-spaces-l288` | `比較鍵 ファイバー ≃ \(\mathrm{Hom}^L\)行ごとの同値（スライスの頂点への制限）と対角補題 左 f` | [8.1.2](8.1.2.md#nbw3-f-c-spaces-l288) |

### f-d-adjoint-presentable.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 27 / `nbw3-f-d-adjoint-presentable-l27` | `\(C,D\) を presentable ∞ 圏とする（HTT 5.5.2.9）。` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l27) |
| 29 / `nbw3-f-d-adjoint-presentable-l29` | `\(F\colon C\to D\) が右随伴をもつ ⇔ \(F\) は小さい余極限を保つ。` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l29) |
| 30 / `nbw3-f-d-adjoint-presentable-l30` | `\(G\colon D\to C\) が左随伴をもつ ⇔ \(G\) はアクセシブルで、小さい極限を保つ。` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l30) |
| 32 / `nbw3-f-d-adjoint-presentable-l32` | `どちらも「随伴 = 各点の表現可能性」（随伴の (E)）に帰着する。` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l32) |
| 34 / `nbw3-f-d-adjoint-presentable-l34` | `1 の向き：各 \(Y\) で \(\mathrm{Map}_D(F(-),Y)\colon C^{\mathrm{` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l34) |
| 35 / `nbw3-f-d-adjoint-presentable-l35` | `2 の向き：各 \(X\) で \(\mathrm{Map}_C(X,G(-))\colon D\to\mathca` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l35) |
| 40 / `nbw3-f-d-adjoint-presentable-l40` | `部品内容どこで使うか \(\mathrm{Map}\) の関手性Hom 関手（Tw の St、補章 3 §11）、表` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l40) |
| 53 / `nbw3-f-d-adjoint-presentable-l53` | `Map の関手性（St・Tw）──┐ 随伴 (E)⇒(C) ──────────┤ 𝒮 と 𝒫(C₀) の極限・余極` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l53) |
| 63 / `nbw3-f-d-adjoint-presentable-l63` | `presentable 圏は「余極限の側では小さいデータで生成されるが、極限の側ではそうでない」非対称な概念で、アク` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l63) |
| 65 / `nbw3-f-d-adjoint-presentable-l65` | `\(C\) は小さい \(C_0=C^\kappa\) から余極限で生成され（\(C\simeq\mathrm{In` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l65) |
| 67 / `nbw3-f-d-adjoint-presentable-l67` | `\(G\) の左随伴には各 \(X\) でコンマ圏 \(X\downarrow G\)（対象 \((Y,X\to G` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l67) |
| 69 / `nbw3-f-d-adjoint-presentable-l69` | `\(\kappa\) を十分大きくとり、\(X\) が \(\kappa\)-コンパクト、\(G\) が \(\ka` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l69) |
| 70 / `nbw3-f-d-adjoint-presentable-l70` | `任意の \(Y\) は \(\kappa\)-コンパクト対象の \(\kappa\)-filtered 余極限 \(` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l70) |
| 71 / `nbw3-f-d-adjoint-presentable-l71` | `\(G\) は \(\kappa\)-filtered 余極限を保つので \(GY\simeq\operatorna` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l71) |
| 72 / `nbw3-f-d-adjoint-presentable-l72` | `\(X\) は \(\kappa\)-コンパクトなので \(X\to GY\) はある \(X\to GY_i\) ` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l72) |
| 73 / `nbw3-f-d-adjoint-presentable-l73` | `\(\kappa\)-コンパクトな \(Y'\) をもつ \((Y',X\to GY')\) が弱始的で、\(D^\` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l73) |
| 74 / `nbw3-f-d-adjoint-presentable-l74` | `その上で極限をとれば、\(D\) の極限と \(G\) の極限保存から始対象が得られる。` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l74) |
| 76 / `nbw3-f-d-adjoint-presentable-l76` | `アクセシブル性は 3 の一点にだけ効く。1 圏では Freyd の一般随伴関手定理の解集合条件そのもの。極限を保つだ` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l76) |
| 77 / `nbw3-f-d-adjoint-presentable-l77` | `左随伴になる条件右随伴になる条件 presentable 圏の間余極限を保つ極限を保ち、かつアクセシブル 理由余極限` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l77) |
| 83 / `nbw3-f-d-adjoint-presentable-l83` | `\(\mathrm{Pr}^R\) の射の定義にアクセシブル性が入っているのもこの非対称のためで、\(\mathrm` | [9.5.2](9.5.2.md#nbw3-f-d-adjoint-presentable-l83) |
| 87 / `nbw3-f-d-adjoint-presentable-l87` | `注意：以前「再帰的局所化」と書いたのは誤記で、正しくは反射的局所化（reflective localization）` | [9.5.1](9.5.1.md#nbw3-f-d-adjoint-presentable-l87) |
| 89 / `nbw3-f-d-adjoint-presentable-l89` | `用語定義 \(C_0\)\(C\) の小さい充満部分圏で \(C\) を余極限で生成するもの。標準的には十分大きい正` | [9.5.1](9.5.1.md#nbw3-f-d-adjoint-presentable-l89) |
| 100 / `nbw3-f-d-adjoint-presentable-l100` | `(1)⇒(2)（表現可能性定理の手順 1）：比較的初等的。\(C_0=C^\kappa\)、\(\nu\colon ` | [9.5.1](9.5.1.md#nbw3-f-d-adjoint-presentable-l100) |
| 101 / `nbw3-f-d-adjoint-presentable-l101` | `(3)⇒(1) で使う「局所化の存在」（HTT 5.5.4.15）：任意の小さい \(S\) で \(S\)-局所対` | [9.5.1](9.5.1.md#nbw3-f-d-adjoint-presentable-l101) |
| 103 / `nbw3-f-d-adjoint-presentable-l103` | `表現可能性定理には (1)⇒(2) しか要らない。presentability の理論全体では Lurie–Simp` | [9.5.1](9.5.1.md#nbw3-f-d-adjoint-presentable-l103) |
| 106 / `nbw3-f-d-adjoint-presentable-l106` | `\(C\) を presentable、\(H\colon C^{\mathrm{op}}\to\mathcal S` | [9.5.1.8](9.5.1.8.md#nbw3-f-d-adjoint-presentable-l106) |
| 108 / `nbw3-f-d-adjoint-presentable-l108` | `候補：\(\tilde H:=H&#124;_{C_0^{\mathrm{op}}}\in\mathcal P(C_` | [9.5.1.8](9.5.1.8.md#nbw3-f-d-adjoint-presentable-l108) |
| 109 / `nbw3-f-d-adjoint-presentable-l109` | `鍵の計算：任意の \(F\in\mathcal P(C_0)\) で自然に \(\mathrm{Map}_{\mat` | [9.5.1.8](9.5.1.8.md#nbw3-f-d-adjoint-presentable-l109) |
| 110 / `nbw3-f-d-adjoint-presentable-l110` | `\(\tilde H\) は局所対象：\(f\colon F\to F'\) が \(L\)-同値なら \(LF\s` | [9.5.1.8](9.5.1.8.md#nbw3-f-d-adjoint-presentable-l110) |
| 111 / `nbw3-f-d-adjoint-presentable-l111` | `表現：\(X\in C\) について 2 を \(F=\nu X\) に適用し \(L\nu X\simeq X\)` | [9.5.1.8](9.5.1.8.md#nbw3-f-d-adjoint-presentable-l111) |
| 113 / `nbw3-f-d-adjoint-presentable-l113` | `自然性：\(H\) と \(\mathrm{Map}_C(-,Y)\) はどちらも \(C_0^{\mathrm{o` | [9.5.1.8](9.5.1.8.md#nbw3-f-d-adjoint-presentable-l113) |
| 114 / `nbw3-f-d-adjoint-presentable-l114` | `概念一言で証明での役割 \(C_0=C^\kappa\)余極限で \(C\) を生成する小さい部分圏前層を小さい圏の` | [9.5.1.8](9.5.1.8.md#nbw3-f-d-adjoint-presentable-l114) |

### fibered-descent.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 25 / `nbw3-fibered-descent-l25` | `圏 \(\mathcal C\) から \(\mathrm{Cat}\) への擬関手 \(F\) は次のデータと条件` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l25) |
| 27 / `nbw3-fibered-descent-l27` | `各対象 \(X\) に圏 \(F(X)\)、各射 \(f\colon X\to Y\) に関手 \(F(f)\)。` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l27) |
| 28 / `nbw3-fibered-descent-l28` | `合成可能な \(X\xrightarrow{f}Y\xrightarrow{g}Z\) ごとに可逆な自然変換 \(\` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l28) |
| 29 / `nbw3-fibered-descent-l29` | `結合性：\(W\xrightarrow{f}X\xrightarrow{g}Y\xrightarrow{h}Z\) ` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l29) |
| 33 / `nbw3-fibered-descent-l33` | `単位性：\(\mu_{f,\mathrm{id}}\circ(F(f)\,\eta_X)=\mathrm{id}\)` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l33) |
| 35 / `nbw3-fibered-descent-l35` | `種類\(\mu,\eta\) 厳密な関手恒等変換 擬関手可逆な自然変換 lax 関手可逆とは限らない自然変換` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l35) |
| 41 / `nbw3-fibered-descent-l41` | `\(\mu\) は「同型が存在する」という条件ではなく、指定されたデータである。選び方が違えば一般に違う擬関手になる` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l41) |
| 44 / `nbw3-fibered-descent-l44` | `列の長さ擬関手（\(\mathrm{Cat}\) 値）∞ 版（\(\mathrm{Cat}_\infty\) 値） ` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l44) |
| 51 / `nbw3-fibered-descent-l51` | `\(\mathrm{Cat}\) は 2 圏で自然変換の間には等しいかどうかしかないので、長さ 3 で等式になって止` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l51) |
| 54 / `nbw3-fibered-descent-l54` | `方法1 圏∞ 圏 ① 全データを書く\(\mu,\eta\) を与えて等式を確かめる（手で可能）\(N(\mathc` | [5.6.1](5.6.1.md#nbw3-fibered-descent-l54) |

### presentable-route.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 44 / `nbw3-presentable-route-l44` | `定理（HTT Cor. 5.5.2.9）．\(\mathcal C,\mathcal D\) を presentab` | [9.5.2.1](9.5.2.1.md#nbw3-presentable-route-l44) |
| 46 / `nbw3-presentable-route-l46` | `\(F\) が右随伴を持つ ⇔ \(F\) が小さい余極限を保つ。` | [9.5.2.1](9.5.2.1.md#nbw3-presentable-route-l46) |
| 47 / `nbw3-presentable-route-l47` | `\(F\) が左随伴を持つ ⇔ \(F\) が小さい極限を保ち、accessible（ある \(\kappa\) に` | [9.5.2.1](9.5.2.1.md#nbw3-presentable-route-l47) |
| 49 / `nbw3-presentable-route-l49` | `「⇒」は随伴の一般論。中身は「⇐」で、1 は次の二つの組み合わせである。` | [9.5.2.1](9.5.2.1.md#nbw3-presentable-route-l49) |
| 51 / `nbw3-presentable-route-l51` | `表現可能性定理（HTT Prop. 5.5.2.2）：\(\mathcal C\) が presentable なら` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l51) |
| 52 / `nbw3-presentable-route-l52` | `各点の判定：\(F\) が右随伴を持つ ⇔ 各 \(d\) について \(c\mapsto\mathrm{Map}(` | [9.5.2.1](9.5.2.1.md#nbw3-presentable-route-l52) |
| 68 / `nbw3-presentable-route-l68` | `1 圏∞ 圏 定義\(\mathcal P(A)=\mathrm{Fun}(A^{\mathrm{op}},\mat` | [8.3.3](8.3.3.md#nbw3-presentable-route-l68) |
| 76 / `nbw3-presentable-route-l76` | `直観的には「\(A\) の対象の形式的な余極限を全部付け加えたもの」。余極限は各点で計算できるので、\(\mathc` | [8.3.3](8.3.3.md#nbw3-presentable-route-l76) |
| 78 / `nbw3-presentable-route-l78` | `\(A\)1 圏の \(\mathcal P(A)\)∞ 圏の \(\mathcal P(A)\) 一点\(\mat` | [8.3.3](8.3.3.md#nbw3-presentable-route-l78) |
| 89 / `nbw3-presentable-route-l89` | `定理（1 圏：古典、∞ 圏：HTT Thm 5.1.5.6）．\(A\) を小さい（∞）圏、\(\mathcal E` | [8.4.3](8.4.3.md#nbw3-presentable-route-l89) |
| 100 / `nbw3-presentable-route-l100` | `\(A\) と \(\mathcal E\) の役割` | [8.4.3](8.4.3.md#nbw3-presentable-route-l100) |
| 102 / `nbw3-presentable-route-l102` | `\(A\)：任意の小さい（∞）圏。小ささは、\(\mathcal P(A)\) の Hom（写像空間）が小さくなるこ` | [8.4.3](8.4.3.md#nbw3-presentable-route-l102) |
| 103 / `nbw3-presentable-route-l103` | `\(\mathcal E\)：小さい余極限をすべて持つ任意の（∞）圏。大きくてよい（\(\mathrm{Set}\)` | [8.4.3](8.4.3.md#nbw3-presentable-route-l103) |
| 104 / `nbw3-presentable-route-l104` | `定理は、そのような組 \((A,\mathcal E)\) ごとに成り立つ。「\(\mathcal P(A)\) は` | [8.4.3](8.4.3.md#nbw3-presentable-route-l104) |
| 105 / `nbw3-presentable-route-l105` | `表現可能性定理（§5）では、\(A\) を \(\mathcal C\) の \(\kappa\)-コンパクト対象の` | [8.4.3](8.4.3.md#nbw3-presentable-route-l105) |
| 110 / `nbw3-presentable-route-l110` | `ステップ1 圏∞ 圏 ① 米田自然変換の定義から直接関手版の米田。Hom 関手の構成に straightening ` | [8.4.3](8.4.3.md#nbw3-presentable-route-l110) |
| 118 / `nbw3-presentable-route-l118` | `② の計算．1 圏では \[ \mathrm{Hom}\Bigl(\operatorname*{colim}_{\m` | [8.4.3](8.4.3.md#nbw3-presentable-route-l118) |
| 128 / `nbw3-presentable-route-l128` | `④ の右随伴．\(\mathrm{Hom}_{\mathcal E}(\Phi F,e)\cong\lim_{\ma` | [8.4.3](8.4.3.md#nbw3-presentable-route-l128) |
| 133 / `nbw3-presentable-route-l133` | `二段階で示す。段階 I は \(\mathcal C=\mathcal P(A)\) の場合、段階 II は一般の場` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l133) |
| 137 / `nbw3-presentable-route-l137` | `(a) presentable なら、小さい \(A\)（\(\kappa\)-コンパクト対象）と反射的局所化 \(` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l137) |
| 138 / `nbw3-presentable-route-l138` | `(b) §4 の普遍性。` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l138) |
| 142 / `nbw3-presentable-route-l142` | `\(h:=H\circ y\in\mathcal P(A)\) と置く。1 圏では \[ H(F)\cong H\b` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l142) |
| 150 / `nbw3-presentable-route-l150` | `\(H':=H\circ L^{\mathrm{op}}\) は余極限を極限に送る（\(L\) は左随伴）。段階 I` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l150) |
| 151 / `nbw3-presentable-route-l151` | `\(h\) は局所的：単位 \(\eta_F\) について \(\mathrm{Hom}(\eta_F,h)=H(L` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l151) |
| 152 / `nbw3-presentable-route-l152` | `\(c\in\mathcal C\) について \(\mathrm{Hom}_{\mathcal C}(c,Lh)\` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l152) |
| 154 / `nbw3-presentable-route-l154` | `仮定の使われ方：「余極限を極限に送る」は生成元への帰着と \(L\) との合成で、presentable（\(A\)` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l154) |
| 157 / `nbw3-presentable-route-l157` | `論点1 圏∞ 圏 (a) 局所化として表すGabriel–UlmerLurie–Simpson。主張は同じで証明は重` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l157) |
| 164 / `nbw3-presentable-route-l164` | `表現可能性定理は「straightening → 米田 → \(\mathcal P(A)\) の普遍性」の積み重ね` | [9.5.1.8](9.5.1.8.md#nbw3-presentable-route-l164) |

### route-6ff-definition.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 111 / `nbw3-route-6ff-definition-l111` | `段内容重い入力 1\(\mathfrak C[\Delta^n]\)（写像空間 \(N(P_{i,j})\)、和集合` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l111) |
| 119 / `nbw3-route-6ff-definition-l119` | `段 5 のあと、cartesian 構造の一般的構成（HA §2.4.1）で \(\mathrm{Cat}_\inf` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l119) |
| 158 / `nbw3-route-6ff-definition-l158` | `流れは「一般論として \(N^{hc}\) を定義し、それを \(\mathrm{QCat}^\Delta\) に適` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l158) |
| 161 / `nbw3-route-6ff-definition-l161` | `\(\Delta\) は「単体的圏として見たもの」（Hom に単体的集合の構造を入れたもの、HTT の記法）。「小さ` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l161) |
| 162 / `nbw3-route-6ff-definition-l162` | `記号何かHom \(\mathrm{QCat}\)普通の圏関手の集合 \(\mathrm{QCat}^\Delta\` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l162) |
| 167 / `nbw3-route-6ff-definition-l167` | `普通の圏では足りない：\(N(\mathrm{QCat})\) では、準圏の同値 \(F\) は \(GF\sime` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l167) |
| 171 / `nbw3-route-6ff-definition-l171` | `\(\mathrm{QCat}^\Delta\) の Hom を \(\mathrm{Fun}^{\simeq}\)` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l171) |
| 172 / `nbw3-route-6ff-definition-l172` | `\(N^{hc}\) の辺は単体的関手 \(\mathfrak C[\Delta^1]\to\mathrm{QCat` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l172) |
| 173 / `nbw3-route-6ff-definition-l173` | `写像空間 \(\mathrm{Map}_{\mathrm{Cat}_\infty}(\mathcal C,\math` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l173) |
| 174 / `nbw3-route-6ff-definition-l174` | `低次元の確認：\(\mathrm{Map}_{\mathrm{Cat}_\infty}\) の道 \(F\to G\` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l174) |
| 178 / `nbw3-route-6ff-definition-l178` | `core を取るcore を取らない Hom\(\mathrm{Fun}^{\simeq}\)（Kan 複体）\(\` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l178) |
| 186 / `nbw3-route-6ff-definition-l186` | `失われるもの：\(\mathrm{Cat}_\infty\) の中で非可逆な自然変換が高次の射として見えない。lax` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l186) |
| 187 / `nbw3-route-6ff-definition-l187` | `六関手形式との関係：基底変換・射影公式の比較写像は可逆でなければならないので、値は core を取った \(\mat` | [5.5.3](5.5.3.md#nbw3-route-6ff-definition-l187) |
| 424 / `nbw3-route-6ff-definition-l424` | `(i) 各点の普遍射（最小限）：各 \(d\in\mathcal D\) に \(Gd\in\mathcal C\)` | [6.2.1](6.2.1.md#nbw3-route-6ff-definition-l424) |
| 429 / `nbw3-route-6ff-definition-l429` | `(ii) 単位と三角恒等式：自然変換 \(\eta\colon\mathrm{id}\Rightarrow GF\)` | [6.2.1](6.2.1.md#nbw3-route-6ff-definition-l429) |
| 430 / `nbw3-route-6ff-definition-l430` | `(iii) 両側 fibration（HTT Def. 5.2.2.1）：\(\Delta^1\) 上の carte` | [6.2.1](6.2.1.md#nbw3-route-6ff-definition-l430) |
| 431 / `nbw3-route-6ff-definition-l431` | `定義必要な道具向いている用途 (i) 各点の普遍射写像空間だけ「右随伴を持つ」という性質を述べる（定義に最適） (i` | [6.2.1](6.2.1.md#nbw3-route-6ff-definition-l431) |
| 437 / `nbw3-route-6ff-definition-l437` | `三つは同値。(i) から (ii)・(iii) を作るには \(d\mapsto Gd\) を関手にまとめる必要があ` | [6.2.1](6.2.1.md#nbw3-route-6ff-definition-l437) |

### route-classification.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 131 / `nbw3-route-classification-l131` | `鍵は二点：(1) 全ての普遍性は、ある ∞ 圏の始対象（終対象）として述べられる。(2) 始対象の条件は頂点 0 を` | [4.7.3](4.7.3.md#nbw3-route-classification-l131) |
| 132 / `nbw3-route-classification-l132` | `始対象（HTT Def. 1.2.12.1）：全ての \(n\ge1\) で、頂点 0 を \(x\) に送る \(` | [4.7.3](4.7.3.md#nbw3-route-classification-l132) |
| 133 / `nbw3-route-classification-l133` | `\(n\)与えられるもの得られるもの意味 1二点 \(x,z\)辺 \(x\to z\)射の存在 2三辺2 単体 \` | [4.7.3](4.7.3.md#nbw3-route-classification-l133) |
| 139 / `nbw3-route-classification-l139` | `全ての辺がすでに与えられているのでホーンではなく境界。` | [4.7.3](4.7.3.md#nbw3-route-classification-l139) |
| 140 / `nbw3-route-classification-l140` | `射 \(f\) が普遍的 = コスライスの始対象：\(\mathcal C_{x/}\) の \(n\) 単体は頂点` | [4.7.3](4.7.3.md#nbw3-route-classification-l140) |
| 145 / `nbw3-route-classification-l145` | `余極限（HTT Def. 1.2.13.4）：\(\bar p\colon K\star\Delta^0\to\ma` | [4.7.3](4.7.3.md#nbw3-route-classification-l145) |
| 146 / `nbw3-route-classification-l146` | `相対的な普遍性：cocartesian 辺は「底の射を固定したまま \(x\) から出る射の中で始対象」で相対的な ` | [4.7.3](4.7.3.md#nbw3-route-classification-l146) |
| 147 / `nbw3-route-classification-l147` | `普遍性どの ∞ 圏の始／終対象か拡張条件 始対象 \(x\)\(\mathcal C\)頂点 0 を固定した \(\` | [4.7.3](4.7.3.md#nbw3-route-classification-l147) |
| 231 / `nbw3-route-classification-l231` | `なぜ必要か：実際の議論ではホーン以外の包含（\(\{0\}\hookrightarrow\Delta^n\)、\(\` | [3.1.2](3.1.2.md#nbw3-route-classification-l231) |
| 232 / `nbw3-route-classification-l232` | `弱飽和クラス：押し出し・超限合成・レトラクトで閉じたクラス。基本補題：任意のクラス \(P\) について「全ての \` | [3.1.2](3.1.2.md#nbw3-route-classification-l232) |
| 233 / `nbw3-route-classification-l233` | `名前生成元の弱飽和閉包右持ち上げ性質を持つもの アノダイン全てのホーンKan fibration 内アノダイン内ホー` | [3.1.2](3.1.2.md#nbw3-route-classification-l233) |
| 239 / `nbw3-route-classification-l239` | `内アノダイン ⊂ 左アノダイン ⊂ アノダイン。ある写像 \(i\) に対する \(p\) の持ち上げ性質を示すには` | [3.1.2](3.1.2.md#nbw3-route-classification-l239) |
| 241 / `nbw3-route-classification-l241` | `例：` | [3.1.2](3.1.2.md#nbw3-route-classification-l241) |
| 243 / `nbw3-route-classification-l243` | `\(\{0\}\hookrightarrow\Delta^2\) は左アノダイン：\(\{0\}\hookright` | [3.1.2](3.1.2.md#nbw3-route-classification-l243) |
| 244 / `nbw3-route-classification-l244` | `spine \(\mathrm{Sp}^n\hookrightarrow\Delta^n\) は内アノダイン（Joy` | [3.1.2](3.1.2.md#nbw3-route-classification-l244) |
| 245 / `nbw3-route-classification-l245` | `非例：\(\partial\Delta^1\hookrightarrow\Delta^1\) はアノダインでない（ア` | [3.1.2](3.1.2.md#nbw3-route-classification-l245) |
| 248 / `nbw3-route-classification-l248` | `Joyal の積の補題（HTT Cor. 2.3.2.4、Prop. 2.1.2.7）：\(A\hookrighta` | [3.1.2](3.1.2.md#nbw3-route-classification-l248) |
| 250 / `nbw3-route-classification-l250` | `帰結（指数随伴 \(\mathrm{Hom}(A\times K,X)=\mathrm{Hom}(A,\mathrm` | [3.1.2](3.1.2.md#nbw3-route-classification-l250) |
| 251 / `nbw3-route-classification-l251` | `帰結意味 \(\mathcal C\) が準圏なら \(\mathrm{Fun}(K,\mathcal C)\) も` | [3.1.2](3.1.2.md#nbw3-route-classification-l251) |
| 259 / `nbw3-route-classification-l259` | `「選択の空間が可縮」の具体的な意味：左 fibration \(p\)、\(e\in E\)（\(b\) の上）、\` | [3.1.2](3.1.2.md#nbw3-route-classification-l259) |
| 260 / `nbw3-route-classification-l260` | `\(n\)\(\partial\Delta^n\to L(e,u)\) が埋まる意味 0空から点持ち上げが存在（輸送` | [3.1.2](3.1.2.md#nbw3-route-classification-l260) |
| 267 / `nbw3-route-classification-l267` | `離散 opfibration では持ち上げの集合が一点、左 fibration では可縮な Kan 複体。「一意に存` | [3.1.2](3.1.2.md#nbw3-route-classification-l267) |
| 268 / `nbw3-route-classification-l268` | `何を固定するか：` | [3.1.2](3.1.2.md#nbw3-route-classification-l268) |
| 269 / `nbw3-route-classification-l269` | `固定動く空間可縮か \(e\) と \(u\)終点\(L(e,u)\)可縮 \(e\) だけ\(u\) と終点\(u` | [3.1.2](3.1.2.md#nbw3-route-classification-l269) |
| 276 / `nbw3-route-classification-l276` | `終点を固定しないのが正しい：輸送は「\(e\) を \(u\) に沿って押し出した先」を決める操作で、終点は結果とし` | [3.1.2](3.1.2.md#nbw3-route-classification-l276) |
| 311 / `nbw3-route-classification-l311` | `定義：辺 \(f\colon x\to y\) が同値 ⟺ \([f]\) が \(h\mathcal C\) で同` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l311) |
| 313 / `nbw3-route-classification-l313` | `定義についての質問：同じ境界の 2 単体が複数あったら、それらをつなぐ中身は要るか。要らない。境界 \((f,g,\` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l313) |
| 314 / `nbw3-route-classification-l314` | `証拠の形空間 同じ \(g\) と二つのホモトピー（quasi-inverse）一般に可縮でない（二つの 2 単体の` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l314) |
| 322 / `nbw3-route-classification-l322` | `定理（Joyal）：\(\mathcal C\) 準圏、\(n\ge2\)。\(\sigma_0\colon\Lam` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l322) |
| 323 / `nbw3-route-classification-l323` | `\(n=2\)（手で）：\(\Lambda^2_0\) は \(f\colon x\to y\) と \(h\col` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l323) |
| 324 / `nbw3-route-classification-l324` | `\(n=3\)（意味）：\(\Lambda^3_0\) は「\(f\) を右から合成した後の関係から \(f\) を` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l324) |
| 326 / `nbw3-route-classification-l326` | `join・スライス・制限写像（ここで初めて正式に定義）：` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l326) |
| 328 / `nbw3-route-classification-l328` | `join：\((K\star L)_n=K_n\sqcup L_n\sqcup\bigsqcup_{i+j+1=n}` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l328) |
| 329 / `nbw3-route-classification-l329` | `下のスライス \(\mathcal C_{p/}\)（\(p\colon K\to\mathcal C\)）：\(n` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l329) |
| 330 / `nbw3-route-classification-l330` | `上のスライス \(\mathcal C_{/p}\)：\(\Delta^n\star K\to\mathcal C\` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l330) |
| 331 / `nbw3-route-classification-l331` | `制限写像：\(K'\subseteq K\) から \(\mathcal C_{p/}\to\mathcal C_{` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l331) |
| 333 / `nbw3-route-classification-l333` | `join とホーンの計算：\(\Delta^m\star\Delta^n\) の面は \(j\le m\) で \(` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l333) |
| 334 / `nbw3-route-classification-l334` | `\[ (\partial\Delta^m\star\Delta^n)\cup(\Delta^m\star\Lambd` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l334) |
| 337 / `nbw3-route-classification-l337` | `前者は \(i\lt n\) なら、後者は \(i\gt0\) なら内ホーン。弱飽和性で片側を一般の単射に広げ：任意` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l337) |
| 338 / `nbw3-route-classification-l338` | `最初の方針（下のスライス）：\(\Delta^n=\Delta^{\{0,1\}}\star\Delta^{n-2}` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l338) |
| 340 / `nbw3-route-classification-l340` | `証明（循環しない形、Kerodon Prop. 4.4.2.13 の双対）：反対側の上のスライスを取ると、問題が辺一` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l340) |
| 342 / `nbw3-route-classification-l342` | `右 fibration は同値を反映する：\(\theta\colon E\to B\) 右 fibration、\` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l342) |
| 343 / `nbw3-route-classification-l343` | `右 fibration は始点を指定して同値を持ち上げる：\(\bar v\colon\rho(Y)\to\bar ` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l343) |
| 344 / `nbw3-route-classification-l344` | `本証明：\(\Delta^n=\Delta^1\star\Delta^{n-2}\)、\(g:=\sigma_0&#` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l344) |
| 346 / `nbw3-route-classification-l346` | `\(n=2\) では \(\mathcal C_{/g_0}=\mathcal C\)、\(\theta=\math` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l346) |
| 347 / `nbw3-route-classification-l347` | `スライス示すべきこと 最初の方針\(f\) の下 \(\mathcal C_{f/}\to\mathcal C_{x` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l347) |
| 352 / `nbw3-route-classification-l352` | `高次の情報はスライス \(\mathcal C_{/g}\) に押し込まれ、問題は 1 次元に落ちる。結果として最初` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l352) |
| 353 / `nbw3-route-classification-l353` | `系：(1) 準圏が Kan 複体 ⟺ \(h\mathcal C\) が亜群（⇒ は \(\Lambda^2_0\)` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l353) |
| 356 / `nbw3-route-classification-l356` | `Lean での扱い（作業ツリー、HEAD d4520692f）：Kerodon の向きのまま最後のホーン \(\La` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l356) |
| 357 / `nbw3-route-classification-l357` | `内容宣言ファイル 同値（\(h\mathcal C\) で同型）IsInvertibleEdgeCore/Inver` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l357) |
| 372 / `nbw3-route-classification-l372` | `積 \(\Delta^m\times\Delta^n\) をセルごとに埋める版（内ホーンは準圏性、\(\Lambda` | [4.4.2.6](4.4.2.6.md#nbw3-route-classification-l372) |
| 375 / `nbw3-route-classification-l375` | `定義：全ての辺が同値な単体からなる部分単体的集合（面で閉じ、退化辺は恒等なので退化でも閉じる）。` | [4.4.3](4.4.3.md#nbw3-route-classification-l375) |
| 377 / `nbw3-route-classification-l377` | `準圏：内ホーンを \(\mathcal C\) で埋めると、\(n=2\) の新しい辺は同値の合成なので同値、\(n` | [4.4.3](4.4.3.md#nbw3-route-classification-l377) |
| 378 / `nbw3-route-classification-l378` | `Kan 複体：ホモトピーを示す 2 単体 \((f,\mathrm{id},f')\) も逆元とその証拠も \(\m` | [4.4.3](4.4.3.md#nbw3-route-classification-l378) |
| 379 / `nbw3-route-classification-l379` | `普遍性：Kan 複体 \(K\) からの写像は必ず \(\mathcal C^{\simeq}\) を経由（\(K\` | [4.4.3](4.4.3.md#nbw3-route-classification-l379) |
| 381 / `nbw3-route-classification-l381` | `\(\mathcal C\)\(\mathcal C^{\simeq}\) \(N(D)\)\(N(D^{\sime` | [4.4.3](4.4.3.md#nbw3-route-classification-l381) |
| 388 / `nbw3-route-classification-l388` | `注意：\(\mathrm{Fun}(K,\mathcal C)^{\simeq}\)（全ての関手と自然同値）と \(` | [4.4.3](4.4.3.md#nbw3-route-classification-l388) |
| 389 / `nbw3-route-classification-l389` | `定理 I での役割：弱い形は空間の同値（分類空間型）で、\(\mathrm{Map}(B,\mathcal S):=` | [4.4.3](4.4.3.md#nbw3-route-classification-l389) |
| 391 / `nbw3-route-classification-l391` | `Lean での扱い（F1/Categories/）：` | [4.4.3](4.4.3.md#nbw3-route-classification-l391) |
| 392 / `nbw3-route-classification-l392` | `内容宣言ファイル 定義（全ての辺への制限が IsInvertibleEdge）quasicategoryCoreQu` | [4.4.3](4.4.3.md#nbw3-route-classification-l392) |
| 402 / `nbw3-route-classification-l402` | `Kan 性の証明は「内ホーンは準圏性、外ホーンは Joyal の定理で \(\mathcal C\) で埋め、cor` | [4.4.3](4.4.3.md#nbw3-route-classification-l402) |
| 414 / `nbw3-route-classification-l414` | `比較：\(\Delta^n\times\Delta^1\to\Delta^{n+1}\)、\((i,0)\mapst` | [4.6](4.6.md#nbw3-route-classification-l414) |
| 415 / `nbw3-route-classification-l415` | `合成：厳密な合成はない。\(\mathrm{Fun}(\Delta^2,\mathcal C)\to\mathrm{` | [4.6](4.6.md#nbw3-route-classification-l415) |
| 416 / `nbw3-route-classification-l416` | `使われ方：充満忠実（1.6）、段 3 の \(\mathcal S\) の写像空間の比較、段 6 の充満忠実性。` | [4.6](4.6.md#nbw3-route-classification-l416) |
| 418 / `nbw3-route-classification-l418` | `模型の比較（質問への答え）：模型 3 が一番すっきりするという感覚は正しく、現代的な扱いもその方向。ただし計算には ` | [4.6](4.6.md#nbw3-route-classification-l418) |
| 419 / `nbw3-route-classification-l419` | `模型長所短所主な使われ方 \(\mathrm{Fun}(\Delta^1,\mathcal C)\) の fiber` | [4.6](4.6.md#nbw3-route-classification-l419) |
| 426 / `nbw3-route-classification-l426` | `現代的な扱い：Kerodon は模型 3 を定義とし pinched を同値な計算模型とする（HTT は \(\ma` | [4.6](4.6.md#nbw3-route-classification-l426) |
| 427 / `nbw3-route-classification-l427` | `四つ目の模型 \(\mathfrak C[\mathcal C](x,y)\)：\(N^{hc}\) の左随伴 \(` | [4.6](4.6.md#nbw3-route-classification-l427) |
| 428 / `nbw3-route-classification-l428` | `質問：\(\mathcal C\) が準圏であることは重要か。模型によって違う。` | [4.6](4.6.md#nbw3-route-classification-l428) |
| 429 / `nbw3-route-classification-l429` | `模型任意の単体的集合 \(S\) で \(\mathrm{Hom}^R\)、\(\mathrm{Hom}^L\)、\` | [4.6](4.6.md#nbw3-route-classification-l429) |
| 434 / `nbw3-route-classification-l434` | `例：\(S=\Lambda^2_1\)（\(0\to1\to2\)）では \(\mathrm{Hom}^R_S(0,` | [4.6](4.6.md#nbw3-route-classification-l434) |
| 436 / `nbw3-route-classification-l436` | `Lean での扱い：Kerodon §4.6.5 に沿って右 pinched 写像空間（＝ \(\mathrm{Ho` | [4.6](4.6.md#nbw3-route-classification-l436) |
| 450 / `nbw3-route-classification-l450` | `成分の定義：\(\mathrm{Fun}(K,\mathcal C)\) の辺は \(\alpha\colon\De` | [4.4.4](4.4.4.md#nbw3-route-classification-l450) |
| 451 / `nbw3-route-classification-l451` | `条件中身 \(\alpha\) が \(\mathrm{Fun}(K,\mathcal C)\) で同値逆向きの辺 ` | [4.4.4](4.4.4.md#nbw3-route-classification-l451) |
| 456 / `nbw3-route-classification-l456` | `定理：\(\alpha\) が同値 ⟺ 全ての頂点 \(k\) で \(\alpha_k\) が同値。後者のばらばら` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l456) |
| 458 / `nbw3-route-classification-l458` | `(⇒)：\(\mathrm{ev}_k\) は同型を保つ。` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l458) |
| 459 / `nbw3-route-classification-l459` | `(⇐)（Kerodon §4.4.4）：1 圏のように逆元を集めると高次の整合性の選択になるので、代わりに 3.2 ` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l459) |
| 461 / `nbw3-route-classification-l461` | `帰結：\(\mathrm{Fun}(K,\mathcal C)^{\simeq}\) の辺は自然同値（3.3 の表の` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l461) |
| 463 / `nbw3-route-classification-l463` | `Lean での扱い：形式化の証明は上とは別の組み立て。` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l463) |
| 465 / `nbw3-route-classification-l465` | `\(\mathcal C\) の同値な辺を頂点とする \(\mathrm{Fun}(\Delta^1,\mathca` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l465) |
| 466 / `nbw3-route-classification-l466` | `始点評価 \(P\to\mathcal C\) は自明 Kan fibration（trivialKanFibrat` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l466) |
| 467 / `nbw3-route-classification-l467` | `定値 path の切断 \(\mathcal C\to P\) は圏同値で、前合成 \(\mathrm{Fun}(P` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l467) |
| 468 / `nbw3-route-classification-l468` | `各点で同値な \(\alpha\) は \(K\to P\) を経由するので、普遍の場合の前合成として同値（func` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l468) |
| 470 / `nbw3-route-classification-l470` | `定理は isInvertibleEdge_iff_evaluateFunctorAt（Core/FunctorEdg` | [4.4.4.4](4.4.4.4.md#nbw3-route-classification-l470) |
| 477 / `nbw3-route-classification-l477` | `(⇐)（Kerodon Theorem 4.8.4.1）：1 圏のように \(x_d\) と同型を選んで \(G\)` | [4.8.4.1](4.8.4.1.md#nbw3-route-classification-l477) |
| 485 / `nbw3-route-classification-l485` | `定理 I での使われ方：強い形 \(\mathrm{Fun}(B,\mathcal S)\simeq\mathrm{` | [4.8.4.1](4.8.4.1.md#nbw3-route-classification-l485) |
| 487 / `nbw3-route-classification-l487` | `Lean での扱い：` | [4.8.4.1](4.8.4.1.md#nbw3-route-classification-l487) |
| 488 / `nbw3-route-classification-l488` | `内容宣言ファイル 同値QCatEquivalence、IsQCatEquivalenceCore/Equivalen` | [4.8.4.1](4.8.4.1.md#nbw3-route-classification-l488) |
| 496 / `nbw3-route-classification-l496` | `鍵の補題の高次元部分は Core/FullyFaithfulBoundary.lean（全境界の持ち上げ）。` | [4.8.4.1](4.8.4.1.md#nbw3-route-classification-l496) |
| 562 / `nbw3-route-classification-l562` | `fiber の定義：\(b\colon\Delta^0\to B\) に沿った厳密な引き戻し \(E_b:=\Del` | [5.2](5.2.md#nbw3-route-classification-l562) |
| 563 / `nbw3-route-classification-l563` | `(a) 点上の左 fibration は Kan：内ホーンで準圏、\(\Lambda^2_0\) を \((u,\m` | [5.2](5.2.md#nbw3-route-classification-l563) |
| 564 / `nbw3-route-classification-l564` | `(b) 全ての辺が cocartesian：\(\Lambda^n_0\) の持ち上げは最初の辺が何でも定義に含まれ` | [5.2](5.2.md#nbw3-route-classification-l564) |
| 565 / `nbw3-route-classification-l565` | `(c) 同値を反映する（3.2）。特に fiber の中の辺は全て \(E\) の同値。(d) 写像空間では \(\` | [5.2](5.2.md#nbw3-route-classification-l565) |
| 566 / `nbw3-route-classification-l566` | `質問：厳密な fiber は ∞ 圏的な fiber と一致するか。左 fibration（底が準圏）では一致する。` | [5.2](5.2.md#nbw3-route-classification-l566) |
| 567 / `nbw3-route-classification-l567` | `意味\(E_b\) と理由 \(\mathrm{sSet}\) の引き戻し定義— \(\mathrm{QCat}\)` | [5.2](5.2.md#nbw3-route-classification-l567) |
| 574 / `nbw3-route-classification-l574` | `モデル構造なしの形：∞ 圏的 fiber は \(\Delta^0\times_BP(B)\times_BE\)（\` | [5.2](5.2.md#nbw3-route-classification-l574) |
| 576 / `nbw3-route-classification-l576` | `Lean での扱い：fiber は vertexFiber（引き戻し）。` | [5.2](5.2.md#nbw3-route-classification-l576) |
| 577 / `nbw3-route-classification-l577` | `内容宣言ファイル 左ホーンが埋まれば KankanComplex_of_leftHornFillersCore/Le` | [5.2](5.2.md#nbw3-route-classification-l577) |
| 587 / `nbw3-route-classification-l587` | `構成：\(u\colon b\to b'\) について \(h\colon\Delta^1\times E_b\to` | [5.2](5.2.md#nbw3-route-classification-l587) |
| 588 / `nbw3-route-classification-l588` | `一意性：\(h\) の選び方は自明 Kan fibration \(\mathrm{Fun}(\Delta^1\ti` | [5.2](5.2.md#nbw3-route-classification-l588) |
| 589 / `nbw3-route-classification-l589` | `関手性：(1) \((\mathrm{id}_b)_!\simeq\mathrm{id}\)（射影を取る）。(2) ` | [5.2](5.2.md#nbw3-route-classification-l589) |
| 590 / `nbw3-route-classification-l590` | `左 fibration\(u_!\) 離散 opfibration\(F(u)\) \(\mathcal C_{x/` | [5.2](5.2.md#nbw3-route-classification-l590) |
| 597 / `nbw3-route-classification-l597` | `失われる情報：\(B(\mathbb Z/2)\) 上では \(hB\to h\mathrm{Kan}\) はホモト` | [5.2](5.2.md#nbw3-route-classification-l597) |
| 599 / `nbw3-route-classification-l599` | `Lean での扱い：` | [5.2](5.2.md#nbw3-route-classification-l599) |
| 600 / `nbw3-route-classification-l600` | `内容宣言ファイル 左アノダイン × 単射leftAnodyneExtensions_unionProdCore/Pa` | [5.2](5.2.md#nbw3-route-classification-l600) |
| 609 / `nbw3-route-classification-l609` | `形式的に閉じる操作（右持ち上げ性質のクラスなので）：引き戻し（fiber は \((E\times_BB')_{b'` | [5.2](5.2.md#nbw3-route-classification-l609) |
| 610 / `nbw3-route-classification-l610` | `局所性：\(p\) が左 fibration ⟺ 全ての単体 \(\sigma\colon\Delta^n\to B` | [5.2](5.2.md#nbw3-route-classification-l610) |
| 611 / `nbw3-route-classification-l611` | `関手の ∞ 圏への上げ：\(K\subseteq L\) 単射なら \(\mathrm{Fun}(L,E)\to\m` | [5.2](5.2.md#nbw3-route-classification-l611) |
| 612 / `nbw3-route-classification-l612` | `双対：\(p\) 左 ⟺ \(p^{\mathrm{op}}\) 右（\(\Lambda^n_i\leftright` | [5.2](5.2.md#nbw3-route-classification-l612) |
| 614 / `nbw3-route-classification-l614` | `Lean での扱い：leftFibrations は deriving IsMultiplicative, IsSt` | [5.2](5.2.md#nbw3-route-classification-l614) |
| 617 / `nbw3-route-classification-l617` | `定理：\(B\) 上の左 fibration の間の \(B\) 上の写像 \(f\colon E\to E'\) ` | [5.1.6](5.1.6.md#nbw3-route-classification-l617) |
| 618 / `nbw3-route-classification-l618` | `(1)⇒(2)：\(B\) 上の逆写像とホモトピーを fiber に制限する。` | [5.1.6](5.1.6.md#nbw3-route-classification-l618) |
| 619 / `nbw3-route-classification-l619` | `(2)⇒(1)：\(\mathrm{LFib}(B)\) での米田の議論に帰着：全ての左 fibration \(X` | [5.1.6](5.1.6.md#nbw3-route-classification-l619) |
| 621 / `nbw3-route-classification-l621` | `単体一つ：\(\{0\}\subset\Delta^n\) が左アノダインなので \(\mathrm{Fun}_B(` | [5.1.6](5.1.6.md#nbw3-route-classification-l621) |
| 622 / `nbw3-route-classification-l622` | `境界：制限 \(\mathrm{Fun}_B(\Delta^n,E)\to\mathrm{Fun}_B(\parti` | [5.1.6](5.1.6.md#nbw3-route-classification-l622) |
| 623 / `nbw3-route-classification-l623` | `セルごとに組み立てる：骨格に沿って \(\mathrm{Fun}_B(X_k,E)=\mathrm{Fun}_B(X` | [5.1.6](5.1.6.md#nbw3-route-classification-l623) |
| 624 / `nbw3-route-classification-l624` | `同値の意味：\(hN^{hc}(D)=\pi_0D\) なので、\(\mathrm{LFib}(B)\) の辺の同値` | [5.1.6](5.1.6.md#nbw3-route-classification-l624) |
| 626 / `nbw3-route-classification-l626` | `使われ方：1.4 の写像空間の模型の比較（fiber ごとに同値）を回収。段 6・7 で「\(\mathrm{Un}` | [5.1.6](5.1.6.md#nbw3-route-classification-l626) |
| 628 / `nbw3-route-classification-l628` | `Lean での扱い：(3)（全空間の圏同値）を経由し、「標準単体上の比較による十分条件」で示す。` | [5.1.6](5.1.6.md#nbw3-route-classification-l628) |
| 629 / `nbw3-route-classification-l629` | `内容宣言ファイル 全ての準圏への前合成が同値IsPrecompositionEquivalenceCore/Prec` | [5.1.6](5.1.6.md#nbw3-route-classification-l629) |
| 638 / `nbw3-route-classification-l638` | `上の説明は後合成で米田の議論をしたが、形式化は前合成（全空間の圏同値）を経由して最後に \(\mathrm{LFib` | [5.1.6](5.1.6.md#nbw3-route-classification-l638) |
| 641 / `nbw3-route-classification-l641` | `主張：\(\Delta^1\) 上の左 fibration は本質的に Kan 複体の間の写像 \(u_!\colo` | [5.2.4](5.2.4.md#nbw3-route-classification-l641) |
| 643 / `nbw3-route-classification-l643` | `左 fibration → 写像：2.3 の輸送。` | [5.2.4](5.2.4.md#nbw3-route-classification-l643) |
| 644 / `nbw3-route-classification-l644` | `写像 → \(\Delta^1\) 上の対象：写像柱 \(M(\varphi):=(\Delta^1\times K` | [5.2.4](5.2.4.md#nbw3-route-classification-l644) |
| 645 / `nbw3-route-classification-l645` | `比較：\(h\) と包含 \(E_1\subset E\) から \(c\colon M(u_!)\to E\)。任` | [5.2.4](5.2.4.md#nbw3-route-classification-l645) |
| 647 / `nbw3-route-classification-l647` | `帰結：\(E\simeq E'\) in \(\mathrm{LFib}(\Delta^1)\) ⟺ \(u_!\)` | [5.2.4](5.2.4.md#nbw3-route-classification-l647) |
| 649 / `nbw3-route-classification-l649` | `Lean での扱い：写像柱は押し出し pushout (prismEndpoint 1 K) f で、置き換えずに比` | [5.2.4](5.2.4.md#nbw3-route-classification-l649) |
| 650 / `nbw3-route-classification-l650` | `内容宣言ファイル 端点の包含と比較transportCylinderEndpointInclusion、transp` | [5.2.4](5.2.4.md#nbw3-route-classification-l650) |
| 659 / `nbw3-route-classification-l659` | `段 2 で押さえること：\(\mathrm{LFib}(B)=N^{hc}\)（相対関手の空間を Hom とする単体` | [5.2.4](5.2.4.md#nbw3-route-classification-l659) |
| 688 / `nbw3-route-classification-l688` | `\(\mathrm{Kan}\) の Hom は \(\mathrm{Fun}(K,L)\)（\(L\) が Kan` | [2.4.3](2.4.3.md#nbw3-route-classification-l688) |
| 689 / `nbw3-route-classification-l689` | `次元新しい Hom\(\mathcal S\) の単体 0—Kan 複体 1\((0,1)=\Delta^0\)写像` | [2.4.3](2.4.3.md#nbw3-route-classification-l689) |
| 696 / `nbw3-route-classification-l696` | `\(hN^{hc}(D)=\pi_0D\)：辺 \(f,g\) がホモトピック ⟺ 境界 \((f,\mathrm{` | [2.4.3](2.4.3.md#nbw3-route-classification-l696) |
| 697 / `nbw3-route-classification-l697` | `1 圏のナーブとの比較：\(N(\mathrm{Kan})\subset\mathcal S\)（ホモトピーを恒等に` | [2.4.3](2.4.3.md#nbw3-route-classification-l697) |
| 699 / `nbw3-route-classification-l699` | `Lean での扱い：辺と豊穣圏の射の対応 coherentNerveEdgeToHom、coherentNerveE` | [2.4.3](2.4.3.md#nbw3-route-classification-l699) |
| 702 / `nbw3-route-classification-l702` | `主張（Kerodon Theorem 4.6.7.5）：局所 Kan な \(\mathcal C\) について比較` | [4.6.7.5](4.6.7.5.md#nbw3-route-classification-l702) |
| 704 / `nbw3-route-classification-l704` | `\(\mathrm{Hom}^L\) は \(\mathcal C(X,Y)\) だけで決まる：\(n\) 単体は懸` | [4.6.7.5](4.6.7.5.md#nbw3-route-classification-l704) |
| 705 / `nbw3-route-classification-l705` | `\(\Phi(\Delta^n)\) は太らせた \(\Delta^n\)：\(\Phi(\Delta^0)=\De` | [4.6.7.5](4.6.7.5.md#nbw3-route-classification-l705) |
| 706 / `nbw3-route-classification-l706` | `鍵の補題（Prop. 4.6.7.23）：\(\rho_K\) は圏同値。有限な \(K\) に帰着（フィルター余極` | [4.6.7.5](4.6.7.5.md#nbw3-route-classification-l706) |
| 707 / `nbw3-route-classification-l707` | `結論：内アノダインな \(A\to B\) で \(\Phi(A)\to\Phi(B)\) は単射かつ圏同値なので ` | [4.6.7.5](4.6.7.5.md#nbw3-route-classification-l707) |
| 709 / `nbw3-route-classification-l709` | `直観：\(N^{hc}\mathcal C\) の写像空間の単体は \(\mathcal C(X,Y)\) の単体を` | [4.6.7.5](4.6.7.5.md#nbw3-route-classification-l709) |
| 711 / `nbw3-route-classification-l711` | `Lean での扱い：比較写像 coherentHomComparisonObj など（F1/Coherent/Hom` | [4.6.7.5](4.6.7.5.md#nbw3-route-classification-l711) |
| 714 / `nbw3-route-classification-l714` | `3.3 を \(\mathrm{Kan}\) に適用して \(\mathrm{Map}_{\mathcal S}(K` | [4.6.7](4.6.7.md#nbw3-route-classification-l714) |
| 715 / `nbw3-route-classification-l715` | `写像空間値意味 \(\mathrm{Map}_{\mathcal S}(\Delta^0,K)\)\(K\)一点から` | [4.6.7](4.6.7.md#nbw3-route-classification-l715) |
| 722 / `nbw3-route-classification-l722` | `合成は写像の合成と一致：合成は自明 Kan fibration \(\{\Delta^2\to\mathcal S\` | [4.6.7](4.6.7.md#nbw3-route-classification-l722) |
| 723 / `nbw3-route-classification-l723` | `\(\mathrm{Map}_{\mathcal S}(\Delta^0,-)\) は恒等関手：fibration ` | [4.6.7](4.6.7.md#nbw3-route-classification-l723) |
| 725 / `nbw3-route-classification-l725` | `Lean での扱い：coherentHomEquivalence（F1/Coherent/HomEquivalenc` | [4.6.7](4.6.7.md#nbw3-route-classification-l725) |
| 728 / `nbw3-route-classification-l728` | `\(\mathrm{Cat}_\infty=N^{hc}(\mathrm{QCat}^\Delta)\)、Hom は` | [5.5.3](5.5.3.md#nbw3-route-classification-l728) |
| 729 / `nbw3-route-classification-l729` | `core で失うもの：\(\mathrm{Fun}(\mathcal C,\mathcal D)\) は Kan で` | [5.5.3](5.5.3.md#nbw3-route-classification-l729) |
| 730 / `nbw3-route-classification-l730` | `点で表現される関手は core：\(\mathrm{Map}_{\mathrm{Cat}_\infty}(\Delt` | [5.5.3](5.5.3.md#nbw3-route-classification-l730) |
| 731 / `nbw3-route-classification-l731` | `\(\mathcal S\subset\mathrm{Cat}_\infty\)：Kan 複体では \(\mathr` | [5.5.3](5.5.3.md#nbw3-route-classification-l731) |
| 732 / `nbw3-route-classification-l732` | `\(\mathcal S\)\(\mathrm{Cat}_\infty\) 写像空間\(\mathrm{Fun}(K` | [5.5.3](5.5.3.md#nbw3-route-classification-l732) |
| 740 / `nbw3-route-classification-l740` | `Lean での扱い：QCat、qCat_sHom_kanComplex（F1/Categories/QCatSimp` | [5.5.3](5.5.3.md#nbw3-route-classification-l740) |
| 743 / `nbw3-route-classification-l743` | `対象大きさ Kan 複体、準圏宇宙 \(u\) \(\mathcal S_u=N^{hc}(\mathrm{Kan}` | [5.5.3](5.5.3.md#nbw3-route-classification-l743) |
| 751 / `nbw3-route-classification-l751` | `底が小さいとき：\(\mathrm{Fun}(B,\mathcal S_u)\) には \(B\) を \(u+1\` | [5.5.3](5.5.3.md#nbw3-route-classification-l751) |
| 752 / `nbw3-route-classification-l752` | `底が大きいとき：普遍左 fibration \(\mathcal S_{u,*}\to\mathcal S_u\) ` | [5.5.3](5.5.3.md#nbw3-route-classification-l752) |
| 753 / `nbw3-route-classification-l753` | `選択の独立性：小さい代表を選ぶので、その選択によらないことも示す必要がある。` | [5.5.3](5.5.3.md#nbw3-route-classification-l753) |
| 756 / `nbw3-route-classification-l756` | `Lean での扱い：F1 の README に同じ規約（\(u\) の対象の coherent nerve は \(` | [5.5.3](5.5.3.md#nbw3-route-classification-l756) |
| 758 / `nbw3-route-classification-l758` | `段 3 で押さえること：局所 Kan な単体的圏の \(N^{hc}\) は準圏（内ホーンの延長は蓋のない箱から立方` | [5.5.3](5.5.3.md#nbw3-route-classification-l758) |

### route-yoneda.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 47 / `nbw3-route-yoneda-l47` | `証明は短く、四つの同値を合成するだけである。` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l47) |
| 48 / `nbw3-route-yoneda-l48` | `lemma yonedaPresheafEvaluation_isQCatEquivalence ... := by` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l48) |
| 58 / `nbw3-route-yoneda-l58` | `数学として書くと次のようになる。\(\mathrm{Un}(G)\to C^{\mathrm{op}}\) は前層 ` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l58) |
| 59 / `nbw3-route-yoneda-l59` | `\[ \mathrm{Map}(h_y,F)\;\xrightarrow[h_1]{\ \simeq\ }\;\ma` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l59) |
| 63 / `nbw3-route-yoneda-l63` | `h₁ 写像空間の比較：前層の間の写像空間は、unstraightening の間の相対関手空間と同値（F1/Cohe` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l63) |
| 64 / `nbw3-route-yoneda-l64` | `h₂ 宇宙の調整：大きい unstraightening と小さい模型の相対関手空間は厳密に同型（F1/SmallL` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l64) |
| 65 / `nbw3-route-yoneda-l65` | `h₃ 表現可能前層での評価：任意の左 fibration \(p\colon E\to C^{\mathrm{op}` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l65) |
| 66 / `nbw3-route-yoneda-l66` | `h₄ fiber の値：\(\mathrm{Un}(F)\) の \(y\) での fiber は \(F(y)\)` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l66) |
| 70 / `nbw3-route-yoneda-l70` | `lemma representableUnstraighteningEvaluation_isQCatEquival` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l70) |
| 78 / `nbw3-route-yoneda-l78` | `二段に分かれる。` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l78) |
| 80 / `nbw3-route-yoneda-l80` | `表現可能前層の unstraightening は coslice：比較写像 \(C^{\mathrm{op}}_{` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l80) |
| 81 / `nbw3-route-yoneda-l81` | `coslice は恒等点を始対象に持つ：\(\mathrm{Fun}_{/C^{\mathrm{op}}}(C^{\` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l81) |
| 83 / `nbw3-route-yoneda-l83` | `古典的な Yoneda の補題の証明（「\(\mathrm{id}_y\) の行き先で自然変換が決まる」）が、2 の` | [8.3.3](8.3.3.md#nbw3-route-yoneda-l83) |

### sixff-foundations.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 53 / `nbw3-sixff-foundations-l53` | `局所化は余極限の側をすべて担う道具で、API は「構成」ではなく「判定法と普遍性」を中心に切る。極限 = 切断（安い` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l53) |
| 55 / `nbw3-sixff-foundations-l55` | `C → C[W⁻¹] が Dwyer–Kan 局所化 ⇔ 任意の ∞-圏 D について Fun(C[W⁻¹], D)` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l55) |
| 57 / `nbw3-sixff-foundations-l57` | `1-圏版（Gabriel–Zisman）は射集合がジグザグの商。Mathlib には Riou による Catego` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l57) |
| 58 / `nbw3-sixff-foundations-l58` | `∞ 版は写像空間がジグザグ全体の空間（ハンモック空間）で、高次の情報を保つ。` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l58) |
| 59 / `nbw3-sixff-foundations-l59` | `ho(C[W⁻¹]) ≃ (ho C)[W⁻¹]。Mathlib の DerivedCategory（K(A) を擬` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l59) |
| 62 / `nbw3-sixff-foundations-l62` | `種類例作り方形式化の重さ 反射的（Bousfield）局所化層化 PShv → Shv充満部分圏 + 左随伴 L軽い` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l62) |
| 66 / `nbw3-sixff-foundations-l66` | `反射的局所化は W = {f &#124; L(f) が同値} の Dwyer–Kan 局所化。可能な限り反射的な形` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l66) |
| 67 / `nbw3-sixff-foundations-l67` | `一般的な存在には、逆射の形式的な貼り付けと Joyal モデル構造での fibrant 置換が要り、これはまだ Ma` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l67) |
| 70 / `nbw3-sixff-foundations-l70` | `充満忠実な右随伴があれば局所化（反射的局所化。層化はこれで済む）。` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l70) |
| 71 / `nbw3-sixff-foundations-l71` | `ファイバーが弱可縮なファイブレーション：p: E → B が余デカルト（デカルト）ファイブレーションで各ファイバーが` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l71) |
| 72 / `nbw3-sixff-foundations-l72` | `Quillen の定理 A の ∞ 版：各 b でコンマ ∞-圏 E_{/b} が弱可縮なら p は共終。余極限の計` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l72) |
| 76 / `nbw3-sixff-foundations-l76` | `S 値：colim F ≃ &#124;∫F&#124;（すべての射で局所化）` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l76) |
| 77 / `nbw3-sixff-foundations-l77` | `Cat_∞ 値：colim F ≃ ∫F[余デカルト射⁻¹]（HTT 3.3.4）` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l77) |
| 78 / `nbw3-sixff-foundations-l78` | `Set 値：π₀(∫F) はその0-切断` | [6.3.1](6.3.1.md#nbw3-sixff-foundations-l78) |

### unstraightening-analogy.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 50 / `nbw3-unstraightening-analogy-l50` | `点付き圏の射 \((\mathcal C,c)\to(\mathcal D,d)\) の取り方で、\(\mathca` | [5.5.2](5.5.2.md#nbw3-unstraightening-analogy-l50) |
| 51 / `nbw3-unstraightening-analogy-l51` | `射の定義\(\mathcal C\) 上の fiber 厳密：\(F(c)=d\)離散圏 \(\mathrm{Ob}` | [5.5.2](5.5.2.md#nbw3-unstraightening-analogy-l51) |
| 58 / `nbw3-unstraightening-analogy-l58` | `fiber をちょうど \(\mathcal C\) にしたければ lax 版を使う。\(\mathrm{Cat}_` | [5.5.2](5.5.2.md#nbw3-unstraightening-analogy-l58) |
| 60 / `nbw3-unstraightening-analogy-l60` | `∞ で \(\mathcal S\) を使う理由：\(\mathcal S_*=\mathcal S_{*/}\) ` | [5.5.2](5.5.2.md#nbw3-unstraightening-analogy-l60) |
| 64 / `nbw3-unstraightening-analogy-l64` | `1 圏：厳密な引き戻しと擬引き戻し（iso-comma）がある。(2,1) 圏としての正しい概念は後者だが、片方が ` | [5.5.2](5.5.2.md#nbw3-unstraightening-analogy-l64) |
| 65 / `nbw3-unstraightening-analogy-l65` | `∞：正しいのはホモトピー引き戻し。準圏の模型では \(\mathcal S_*\to\mathcal S\) が左 ` | [5.5.2](5.5.2.md#nbw3-unstraightening-analogy-l65) |
| 71 / `nbw3-unstraightening-analogy-l71` | `どの段でも示したいことは次の形である。` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l71) |
| 73 / `nbw3-unstraightening-analogy-l73` | `\(\mathrm{Un}\colon\mathrm{Fun}(B,\mathcal V)\to(\text{fib` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l73) |
| 74 / `nbw3-unstraightening-analogy-l74` | `充満忠実：\(\mathrm{Hom}(F,G)\simeq\mathrm{Hom}_{/B}(\mathrm{Un` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l74) |
| 75 / `nbw3-unstraightening-analogy-l75` | `本質的全射で、同値になる。` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l75) |
| 79 / `nbw3-unstraightening-analogy-l79` | `変換 \(\alpha\colon F\Rightarrow G\) を \(B\times[1]\to\mathc` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l79) |
| 82 / `nbw3-unstraightening-analogy-l82` | `段Hom 側整合性「cocartesian 射を保つ」条件 集合\(\prod_b\mathrm{Hom}(X_b,` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l82) |
| 90 / `nbw3-unstraightening-analogy-l90` | `離散 opfibration で手で確かめると、充満忠実性の中身が見える。\(B\) 上の関手 \(\Phi\col` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l90) |
| 92 / `nbw3-unstraightening-analogy-l92` | `本質的全射まで含めると、\(\mathcal S\) は左 fibration を分類する：\(\mathrm{Ma` | [5.6.2](5.6.2.md#nbw3-unstraightening-analogy-l92) |
| 97 / `nbw3-unstraightening-analogy-l97` | `straightening は fibration \(p\colon E\to B\) から関手を作る。見方は二つ` | [5.6](5.6.md#nbw3-unstraightening-analogy-l97) |
| 99 / `nbw3-unstraightening-analogy-l99` | `(A) 分類写像：\(\chi(b)=E_b\)、\(\chi(u)=u_!\)（輸送）。難しいのは整合的な関手にま` | [5.6](5.6.md#nbw3-unstraightening-analogy-l99) |
| 100 / `nbw3-unstraightening-analogy-l100` | `(B) 表現可能関手の Un からの写像： \[ \mathrm{St}(E)(b)\ :=\ \mathrm{Ho` | [5.6](5.6.md#nbw3-unstraightening-analogy-l100) |
| 106 / `nbw3-unstraightening-analogy-l106` | `段(A) の結果(B) 集合そのまま関手\(\mathrm{Un}(h^b)=\{b\}\)、\(\mathrm{H` | [5.6](5.6.md#nbw3-unstraightening-analogy-l106) |
| 114 / `nbw3-unstraightening-analogy-l114` | `(B) の要点は、持ち上げを一本選ぶ代わりに「\(b\) から出るすべての射に沿う持ち上げ全体」を一度に保持すること` | [5.6](5.6.md#nbw3-unstraightening-analogy-l114) |
| 116 / `nbw3-unstraightening-analogy-l116` | `注意：準圏の模型では、辺 \(u\colon b\to b'\) から \(B_{b'/}\to B_{b/}\) ` | [5.6](5.6.md#nbw3-unstraightening-analogy-l116) |
| 118 / `nbw3-unstraightening-analogy-l118` | `往復：\(\mathrm{St}(\mathrm{Un}F)(b)=\mathrm{Map}_{/B}(\mathr` | [5.6](5.6.md#nbw3-unstraightening-analogy-l118) |

### unstraightening.html

| 元の行・ブロックID | 段落の先頭 | 行き先 |
| --- | --- | --- |
| 35 / `nbw3-unstraightening-l35` | `すべての unstraightening の元になるのは、一点空間 \(\ast\in\mathcal S\) の下` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l35) |
| 36 / `nbw3-unstraightening-l36` | `noncomputable def PointedSpaceInfinity : SSet.{u + 1} := s` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l36) |
| 40 / `nbw3-unstraightening-l40` | `場所：F1/PointedSpaces（Kerodon Construction 5.5.2.1、Prop. 5.5` | [5.5.2.1](5.5.2.1.md#nbw3-unstraightening-l40) |
| 43 / `nbw3-unstraightening-l43` | `noncomputable def pointedSpaceFiberValueEquivalence (s : S` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l43) |
| 46 / `nbw3-unstraightening-l46` | `\(\mathcal S\) の頂点 \(s\)（Kan 複体 \(K\) を表す）上の fiber は \(K\)` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l46) |
| 48 / `nbw3-unstraightening-l48` | `coslice \(\mathcal S_{\ast/}\) の \(s\) 上の fiber は、左 pinche` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l48) |
| 49 / `nbw3-unstraightening-l49` | `左の写像空間を右の写像空間に移す（第 2 章の pinchedHomLeftRightEquivalence）。` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l49) |
| 50 / `nbw3-unstraightening-l50` | `coherent nerve の写像空間は元の単体的圏の Hom と同値（coherentHomEquivalenc` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l50) |
| 52 / `nbw3-unstraightening-l52` | `つまり「\(\mathcal S_*\to\mathcal S\) の fiber が \(K\) になる」のは、「` | [5.5.2.2](5.5.2.2.md#nbw3-unstraightening-l52) |
| 56 / `nbw3-unstraightening-l56` | `noncomputable def leftUnstraightening {C : SSet.{u + 1}} (` | [5.6.2.9](5.6.2.9.md#nbw3-unstraightening-l56) |
| 61 / `nbw3-unstraightening-l61` | `\[ \begin{array}{ccc} \mathrm{Un}(F) & \longrightarrow & \` | [5.6.2.9](5.6.2.9.md#nbw3-unstraightening-l61) |
| 68 / `nbw3-unstraightening-l68` | `場所：F1/LeftUnstraightening（Kerodon Example 5.6.2.9）。単体的集合とし` | [5.6.2.9](5.6.2.9.md#nbw3-unstraightening-l68) |
| 70 / `nbw3-unstraightening-l70` | `左 fibration：左 fibration は引き戻しで保たれる。底 \(C\) が quasicategory` | [5.6.2.9](5.6.2.9.md#nbw3-unstraightening-l70) |
| 71 / `nbw3-unstraightening-l71` | `fiber：\(\mathrm{Un}(F)_c\) は \(\mathcal S_*\) の \(F(c)\) 上` | [5.6.2.9](5.6.2.9.md#nbw3-unstraightening-l71) |
| 72 / `nbw3-unstraightening-l72` | `底変換：\(k\colon D\to C\) について \(\mathrm{Un}(F\circ k)\cong D` | [5.6.2.5](5.6.2.5.md#nbw3-unstraightening-l72) |
| 73 / `nbw3-unstraightening-l73` | `底についての関手性：\(\alpha\colon C\to D\) が \(G\circ\alpha=F\) を満た` | [5.6.2](5.6.2.md#nbw3-unstraightening-l73) |
| 76 / `nbw3-unstraightening-l76` | `この定義の利点` | [5.6.2](5.6.2.md#nbw3-unstraightening-l76) |
| 77 / `nbw3-unstraightening-l77` | `HTT §2.2.1 では unstraightening を、単体的圏の側の straightening の右随伴` | [5.6.2](5.6.2.md#nbw3-unstraightening-l77) |
| 82 / `nbw3-unstraightening-l82` | `\(\mathcal S\) は宇宙 \(u+1\) にあるので、\(\mathrm{Un}(F)\) も SSet` | [5.6.2](5.6.2.md#nbw3-unstraightening-l82) |
| 84 / `nbw3-unstraightening-l84` | `小ささ：底が各次数で \(u\)-小さければ、引き戻しの単体も \(u\)-小さい（pullback_simplex` | [5.6.2](5.6.2.md#nbw3-unstraightening-l84) |
| 85 / `nbw3-unstraightening-l85` | `縮小：各次数を Shrink して宇宙 \(u\) に戻したものが smallLeftUnstraightening` | [5.6.2](5.6.2.md#nbw3-unstraightening-l85) |
| 87 / `nbw3-unstraightening-l87` | `前層（\(C^{\mathrm{op}}\) 上の関手）の場合は、\(C^{\mathrm{op}}\) 上の左 u` | [5.6.2](5.6.2.md#nbw3-unstraightening-l87) |
| 91 / `nbw3-unstraightening-l91` | `変換 \(H\colon F\Rightarrow G\)（\(\Delta^1\times B\to\mathca` | [5.6.2](5.6.2.md#nbw3-unstraightening-l91) |
| 92 / `nbw3-unstraightening-l92` | `\[ \begin{array}{ccc} \{0\}\times\mathrm{Un}(F) & \xrighta` | [5.6.2](5.6.2.md#nbw3-unstraightening-l92) |
| 99 / `nbw3-unstraightening-l99` | `上の辺は引き戻しの第一射影（\(\mathrm{Un}(F)\) の各点が持っている \(F(b)\) の点）。左の` | [5.6.2](5.6.2.md#nbw3-unstraightening-l99) |
| 100 / `nbw3-unstraightening-l100` | `内容Lean場所 持ち上げの選択空間は可縮leftUnstraighteningTransformationChoi` | [5.6.2](5.6.2.md#nbw3-unstraightening-l100) |
| 107 / `nbw3-unstraightening-l107` | `第 3 章の cocartesian transport と同じ型の議論で、「選択空間が可縮」によって選び方の任意性` | [5.6.2](5.6.2.md#nbw3-unstraightening-l107) |
| 112 / `nbw3-unstraightening-l112` | `定理. 任意の底 \(B\) と \(F,G\colon B\to\mathcal S\) について、比較写像` | [5.6.6](5.6.6.md#nbw3-unstraightening-l112) |
| 113 / `nbw3-unstraightening-l113` | `\[ M\colon\ \mathrm{Map}_{\mathrm{Fun}(B,\mathcal S)}(F,G)` | [5.6.6](5.6.6.md#nbw3-unstraightening-l113) |
| 116 / `nbw3-unstraightening-l116` | `は同値（leftUnstraighteningMappingSpaceMap_isQCatEquivalence、F` | [5.6.6](5.6.6.md#nbw3-unstraightening-l116) |
| 120 / `nbw3-unstraightening-l120` | `§4 の持ち上げを、変換一本ずつではなく変換の空間 \(T\) 全体に対して一度に行う（F1/LeftUnstrai` | [5.6.6](5.6.6.md#nbw3-unstraightening-l120) |
| 123 / `nbw3-unstraightening-l123` | `lemma leftUnstraighteningMappingSpaceMap_isQCatEquivalence` | [5.6.6](5.6.6.md#nbw3-unstraightening-l123) |
| 135 / `nbw3-unstraightening-l135` | `普遍的な族：相対関手空間 \(Y\) の恒等射を uncurry すると、\(Y\) をパラメーターとする相対射の族` | [5.6.6](5.6.6.md#nbw3-unstraightening-l135) |
| 136 / `nbw3-unstraightening-l136` | `族の復元：この族から、\(Y\) をパラメーターとする変換の族 \(t\colon Y\to T\) を作る（exi` | [5.6.6](5.6.6.md#nbw3-unstraightening-l136) |
| 137 / `nbw3-unstraightening-l137` | `\(M\circ t\cong\mathrm{id}\)：「変換の族が相対射の族を実現する」という証拠（Unstra` | [5.6.6](5.6.6.md#nbw3-unstraightening-l137) |
| 138 / `nbw3-unstraightening-l138` | `\(t\circ M\cong\mathrm{id}\)：復元した族を \(M\) で戻すと元の普遍的な族と比較でき` | [5.6.6](5.6.6.md#nbw3-unstraightening-l138) |
| 140 / `nbw3-unstraightening-l140` | `Yoneda の議論と同じ「普遍元」の型の証明である。2 で straightening の構成（分類写像）を使って` | [5.6.6](5.6.6.md#nbw3-unstraightening-l140) |
| 143 / `nbw3-unstraightening-l143` | `\(M\) が変換 \(\alpha\) に対応させる射 \(\mathrm{Un}(F)\to\mathrm{Un` | [5.6.6](5.6.6.md#nbw3-unstraightening-l143) |
| 147 / `nbw3-unstraightening-l147` | `通常の圏 \(C\) 上の strict な図式 \(F\colon C\to\mathrm{Kan}\) には、古` | [5.3.3.1](5.3.3.1.md#nbw3-unstraightening-l147) |
| 149 / `nbw3-unstraightening-l149` | `F1/DirectKanUnstraightening：weighted nerve から、図式自身の cohere` | [5.3.3.1](5.3.3.1.md#nbw3-unstraightening-l149) |
| 150 / `nbw3-unstraightening-l150` | `F1/OppositeKanUnstraightening：値を反転した coherent 図式の unstraig` | [5.3.3.1](5.3.3.1.md#nbw3-unstraightening-l150) |
| 151 / `nbw3-unstraightening-l151` | `F1/LocalUnstraighteningStrictification：標準単体上の一般の coherent ` | [5.3.3.1](5.3.3.1.md#nbw3-unstraightening-l151) |
| 153 / `nbw3-unstraightening-l153` | `これらは主に、straightening の本質的全射性（「任意の coherent 図式は何かの straight` | [5.3.3.1](5.3.3.1.md#nbw3-unstraightening-l153) |
| 157 / `nbw3-unstraightening-l157` | `向き内容Lean \(\mathrm{St}(\mathrm{Un}F)\cong F\)余単位の成分。本質的全射性` | [5.6](5.6.md#nbw3-unstraightening-l157) |
| 163 / `nbw3-unstraightening-l163` | `注意：Un は ∞ 関手としてはまとめられていない` | [5.6](5.6.md#nbw3-unstraightening-l163) |
| 164 / `nbw3-unstraightening-l164` | `straightening は ∞ 圏の射 leftStraighteningInfinityMap : LFib(` | [5.6](5.6.md#nbw3-unstraightening-l164) |
| 169 / `nbw3-unstraightening-l169` | `Yoneda の補題：h₁（§5）、h₂（§3）、h₄（§2 の fiber）。表現可能前層の unstraight` | [5.6](5.6.md#nbw3-unstraightening-l169) |
| 170 / `nbw3-unstraightening-l170` | `\(\mathcal S\) の極限・余極限（第 5 章 §3）：極限 = \(\mathrm{Un}(F)\) の` | [5.6](5.6.md#nbw3-unstraightening-l170) |
| 171 / `nbw3-unstraightening-l171` | `straightening の同値定理：本質的全射性（§7 の余単位）。` | [5.6](5.6.md#nbw3-unstraightening-l171) |
