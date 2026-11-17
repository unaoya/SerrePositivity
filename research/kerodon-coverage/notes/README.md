# NB-W1：第1章の本文原稿の試し

2026-11-17。仮の形。Kerodon 原典の本文は写していない。

## 原稿の規則

- `1.x.y.z.md` は実在する項目番号。冒頭に item-tags.csv の Tag だけをリンクし、本文外の「照合先」に既存 review の宣言名をバッククォートで記す。新しい対応判定はしない。
- `1.x.md`・`1.x.y.md` は導入・つなぎ。項目番号が決まらないからといって、章外の定義をここへ押し込まない。空の項目原稿や第1章180項目すべての原稿は作らない。
- 見出し以下は凍結中の t-01〜t-05 の本文。旧「定義 1.1」等の番号、文言、数式の `\( \)`・`\[ \]` はそのまま。HTML の実体参照を可視文字へ戻し、p/li/table の構造を Markdown に移した。旧番号を Kerodon 番号へ読み替えない。
- 出典位置は HTML コメントに元パス・行・ブロックIDを置く。各段落の直前の `<a id="…"></a>` は移設後のリンク用。これは数式上の引用とは別の転記来歴である。
- 元のリンクの表示文言は保存し、内部・ページ間リンクの行き先だけをこのディレクトリの該当ブロックへ変更した。未配置先には issues.md の保留本文を指す。元リンクと移設先の全対照は git 外の証拠にある。
- ナビゲーション、ページタイトル、CSS、KaTeX/JavaScript、head 要素は本文に含めない。環境の見出しは本文のまとまりを示すため残す。Lean のコード実行・宣言の改名・加筆、対応表や生成器の変更はしない。入力本文に Lean 宣言名の code 要素はなく、本文外の照合先だけを既存 review から付けた。
- 章外の段落も消さず、issues.md の「未配置本文」に全文を保留する。これを第1章の原稿として生成器へ渡してはいけない。

## 元ページの略記

- `t-01`：`t-01-definitions.html`
- `t-02`：`t-02-kan-category.html`
- `t-03`：`t-03-coherent-nerve.html`
- `t-04`：`t-04-join-slice.html`
- `t-05`：`t-05-fibrations.html`

## 段落の行き先

p を段落、li を箇条書きの項、tr を表のデータ行として数える。見出しは別数にせず各まとまりの先頭へ付ける。同じ段落を複数の項目へ重複転記しない。式だけの p も独立に数える。各行のブロックIDと元の行番号で、先頭が「で定める」等の行も区別する。

| 元ページ・行 / ブロックID | 段落の先頭の数語 | 行き先 |
| --- | --- | --- |
| t-01:26 / `t01-conv-universe-1` | `第 III 部を通して、Grothendieck 宇宙 \(\mathbb U\) を一つ固定する。\(\mat` | [原稿](1.1.md#t01-conv-universe-1) |
| t-01:33 / `t01-def-delta-1` | `\(n\ge0\) について、\([n]=\{0,1,\dots,n\}\) に通常の大小関係 \(0<1<\c` | [原稿](1.1.0.2.md#t01-def-delta-1) |
| t-01:35 / `t01-def-delta-2` | `対象：\([n]\)（\(n\ge0\)）。` | [原稿](1.1.0.2.md#t01-def-delta-2) |
| t-01:36 / `t01-def-delta-3` | `射：\(\mathrm{Hom}_\Delta([m],[n])\) は、順序を保つ写像 \(\theta\co` | [原稿](1.1.0.2.md#t01-def-delta-3) |
| t-01:37 / `t01-def-delta-4` | `合成：写像の合成。恒等射：恒等写像。` | [原稿](1.1.0.2.md#t01-def-delta-4) |
| t-01:45 / `t01-def-sset-1` | `単体的集合とは関手 \(X\colon\Delta^{\mathrm{op}}\to\mathrm{Set}\)` | [原稿](1.1.0.6.md#t01-def-sset-1) |
| t-01:52 / `t01-def-simplex-1` | `\(\Delta^n\) を \([n]\) が表現する関手 \(\Delta^n=\mathrm{Hom}_\` | [原稿](1.1.0.9.md#t01-def-simplex-1) |
| t-01:59 / `t01-def-subsset-1` | `単体的集合 \(X\) の部分単体的集合とは、各 \([m]\) について部分集合 \(A([m])\subse` | [原稿](1.1.0.14.md#t01-def-subsset-1) |
| t-01:66 / `t01-def-union-1` | `単体的集合 \(X\) の部分単体的集合の族 \((A_j)_{j\in J}\) について、その和 \(\bi` | [原稿](1.1.0.14.md#t01-def-union-1) |
| t-01:67 / `t01-def-union-2` | `\[\Bigl(\bigcup_{j\in J}A_j\Bigr)([m])=\bigcup_{j\in J}A` | [原稿](1.1.0.14.md#t01-def-union-2) |
| t-01:68 / `t01-def-union-3` | `で定める。これは \(X\) の部分単体的集合である。` | [原稿](1.1.0.14.md#t01-def-union-3) |
| t-01:75 / `t01-def-face-1` | `\(0\le j\le n\) について、\(\Delta^n\) の部分単体的集合 \(\partial_j\` | [原稿](1.2.4.md#t01-def-face-1) |
| t-01:76 / `t01-def-face-2` | `\[\partial_j\Delta^n([m])=\{\theta\colon[m]\to[n]\mid j\` | [原稿](1.2.4.md#t01-def-face-2) |
| t-01:77 / `t01-def-face-3` | `で定め、\(\Delta^n\) の \(j\) 番目の面という。` | [原稿](1.2.4.md#t01-def-face-3) |
| t-01:84 / `t01-def-horn-1` | `\(n\ge1\)、\(0\le i\le n\) とする。\(\Delta^n\) の部分単体的集合 \(\L` | [原稿](1.2.4.1.md#t01-def-horn-1) |
| t-01:86 / `t01-def-horn-2` | `部分単体的集合として直接：\(\Lambda^n_i([m])=\{\theta\colon[m]\to[n]\` | [原稿](1.2.4.1.md#t01-def-horn-2) |
| t-01:87 / `t01-def-horn-3` | `面の和として：\(\Lambda^n_i=\bigcup_{j\ne i}\partial_j\Delta^n\` | [原稿](1.2.4.1.md#t01-def-horn-3) |
| t-01:89 / `t01-def-horn-4` | `両者は一致する。\(\theta([m])\cup\{i\}\ne[n]\) は、\(\theta([m])\)` | [原稿](1.2.4.1.md#t01-def-horn-4) |
| t-01:96 / `t01-def-quasicategory-1` | `単体的集合 \(X\) が quasicategory であるとは、すべての \(0<i<n\) について、任意` | [原稿](1.4.0.1.md#t01-def-quasicategory-1) |
| t-01:103 / `t01-def-kan-1` | `単体的集合 \(X\) が Kan 複体であるとは、すべての \(0\le i\le n\) について、任意の射` | [原稿](1.2.5.1.md#t01-def-kan-1) |
| t-02:27 / `t02-def-product-1` | `単体的集合 \(X,Y\) の積 \(X\times Y\) を` | [原稿](1.5.3.md#t02-def-product-1) |
| t-02:28 / `t02-def-product-2` | `\[(X\times Y)([m])=X([m])\times Y([m]),\qquad (X\times Y` | [原稿](1.5.3.md#t02-def-product-2) |
| t-02:29 / `t02-def-product-3` | `で定める（\(\theta\colon[m]\to[m']\)）。射影 \(X\times Y\to X\)、\` | [原稿](1.5.3.md#t02-def-product-3) |
| t-02:36 / `t02-def-fun-1` | `\(\theta\colon[m]\to[n]\) について、\(\theta_*\colon\Delta^m\` | [原稿](1.5.3.1.md#t02-def-fun-1) |
| t-02:37 / `t02-def-fun-2` | `\[\mathrm{Fun}(X,Y)([n])=\mathrm{Hom}_{\mathrm{sSet}}(X\` | [原稿](1.5.3.1.md#t02-def-fun-2) |
| t-02:38 / `t02-def-fun-3` | `で定める。` | [原稿](1.5.3.1.md#t02-def-fun-3) |
| t-02:45 / `t02-def-postcomposition-1` | `単体的集合 \(K\) と射 \(q\colon X\to S\) について、射 \(q_*\colon\mat` | [原稿](1.5.3.md#t02-def-postcomposition-1) |
| t-02:52 / `t02-thm-adjunction-1` | `単体的集合 \(X\) を固定すると、単体的集合 \(Z,Y\) について自然な全単射` | [原稿](1.5.3.2.md#t02-thm-adjunction-1) |
| t-02:53 / `t02-thm-adjunction-2` | `\[\mathrm{Hom}_{\mathrm{sSet}}(Z\times X,Y)\cong\mathrm{` | [原稿](1.5.3.2.md#t02-thm-adjunction-2) |
| t-02:54 / `t02-thm-adjunction-3` | `がある。すなわち \((-)\times X\) は \(\mathrm{Fun}(X,-)\) の左随伴である` | [原稿](1.5.3.2.md#t02-thm-adjunction-3) |
| t-02:61 / `t02-def-composition-1` | `単体的集合 \(X,Y,Z\) について、合成 \(\circ\colon\mathrm{Fun}(Y,Z)\t` | [原稿](1.5.3.md#t02-def-composition-1) |
| t-02:62 / `t02-def-composition-2` | `\[g\circ f\colon X\times\Delta^n\xrightarrow{(f,\ \mathr` | [原稿](1.5.3.md#t02-def-composition-2) |
| t-02:63 / `t02-def-composition-3` | `で定める。恒等射 \(\mathrm{id}_X\) は、射影 \(X\times\Delta^0\to X\)` | [原稿](1.5.3.md#t02-def-composition-3) |
| t-02:70 / `t02-thm-composition-1` | `定義 2.5 の合成は単体的集合の射であり、結合的で、\(\mathrm{id}\) を単位とする。` | [原稿](1.5.3.md#t02-thm-composition-1) |
| t-02:77 / `t02-def-scat-1` | `単体的圏とは、対象の集合と、対象 \(x,y\) ごとの単体的集合 \(\mathcal C(x,y)\)、単体` | [未配置本文](issues.md#t02-def-scat-1) |
| t-02:84 / `t02-def-kan-category-1` | `単体的圏 \(\mathcal Kan\) を次で定める。` | [未配置本文](issues.md#t02-def-kan-category-1) |
| t-02:86 / `t02-def-kan-category-2` | `対象：小さい Kan 複体（定義 1.9、冒頭の規約）。` | [未配置本文](issues.md#t02-def-kan-category-2) |
| t-02:87 / `t02-def-kan-category-3` | `射の単体的集合：\(\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)\)（定義 2.2）。` | [未配置本文](issues.md#t02-def-kan-category-3) |
| t-02:88 / `t02-def-kan-category-4` | `合成と恒等射：定義 2.5。` | [未配置本文](issues.md#t02-def-kan-category-4) |
| t-02:90 / `t02-def-kan-category-5` | `定理 2.6 によりこれは単体的圏である。` | [未配置本文](issues.md#t02-def-kan-category-5) |
| t-02:97 / `t02-thm-kan-hom-kan-1` | `Kan 複体 \(X,Y\) について、\(\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y` | [未配置本文](issues.md#t02-thm-kan-hom-kan-1) |
| t-03:28 / `t03-def-sfunctor-1` | `単体的圏 \(\mathcal C,\mathcal D\) の間の単体的関手 \(F\colon\mathca` | [未配置本文](issues.md#t03-def-sfunctor-1) |
| t-03:35 / `t03-def-poset-nerve-1` | `半順序集合 \(P\) について、単体的集合 \(N(P)\) を、\(N(P)([m])\) を順序を保つ写像` | [原稿](1.3.1.1.md#t03-def-poset-nerve-1) |
| t-03:42 / `t03-def-path-category-1` | `\(n\ge0\) について、単体的圏 \(\mathfrak C[\Delta^n]\) を次で定める。` | [未配置本文](issues.md#t03-def-path-category-1) |
| t-03:44 / `t03-def-path-category-2` | `対象：\(0,1,\dots,n\)。` | [未配置本文](issues.md#t03-def-path-category-2) |
| t-03:45 / `t03-def-path-category-3` | `射の単体的集合：\(i\le j\) なら \(\mathfrak C[\Delta^n](i,j)=N(P_{` | [未配置本文](issues.md#t03-def-path-category-3) |
| t-03:46 / `t03-def-path-category-4` | `合成：和集合 \(P_{jk}\times P_{ij}\to P_{ik}\)、\((T,S)\mapsto ` | [未配置本文](issues.md#t03-def-path-category-4) |
| t-03:48 / `t03-def-path-category-5` | `\(\theta\colon[m]\to[n]\) について、単体的関手 \(\mathfrak C[\thet` | [未配置本文](issues.md#t03-def-path-category-5) |
| t-03:55 / `t03-def-hc-nerve-1` | `単体的圏 \(\mathcal C\) について、単体的集合 \(N^{hc}(\mathcal C)\) を` | [未配置本文](issues.md#t03-def-hc-nerve-1) |
| t-03:56 / `t03-def-hc-nerve-2` | `\[N^{hc}(\mathcal C)([n])=\mathrm{Hom}_{\mathrm{sCat}}(\` | [未配置本文](issues.md#t03-def-hc-nerve-2) |
| t-03:57 / `t03-def-hc-nerve-3` | `で定める。` | [未配置本文](issues.md#t03-def-hc-nerve-3) |
| t-03:64 / `t03-thm-hc-functor-1` | `単体的関手 \(F\colon\mathcal C\to\mathcal D\) に後合成 \(\sigma\m` | [未配置本文](issues.md#t03-thm-hc-functor-1) |
| t-03:71 / `t03-rem-size-scat-1` | `定理 3.5 の \(\mathrm{sCat}\) と \(\mathrm{sSet}\) は、大きさを制限し` | [未配置本文](issues.md#t03-rem-size-scat-1) |
| t-03:78 / `t03-thm-hc-quasicategory-1` | `単体的圏 \(\mathcal C\) のすべての射の単体的集合 \(\mathcal C(x,y)\) が K` | [未配置本文](issues.md#t03-thm-hc-quasicategory-1) |
| t-03:85 / `t03-def-spaces-1` | `\(\mathcal S=N^{hc}(\mathcal Kan)\) と定める（\(\mathcal Kan\` | [未配置本文](issues.md#t03-def-spaces-1) |
| t-03:92 / `t03-rem-size-spaces-1` | `\(\mathcal Kan\) の対象は小さい Kan 複体で、その全体は \(\mathbb U\) の部分` | [未配置本文](issues.md#t03-rem-size-spaces-1) |
| t-04:28 / `t04-def-extension-lin-1` | `有限な全順序集合 \(I\)（空でもよい）について、\(I\) が空でなければ \(&#124;I&#124;=n+1\) として唯` | [未配置本文](issues.md#t04-def-extension-lin-1) |
| t-04:29 / `t04-def-extension-lin-2` | `\[X^+(I)=\begin{cases}X([n])&(I\ne\varnothing)\\ \{\ast\` | [未配置本文](issues.md#t04-def-extension-lin-2) |
| t-04:30 / `t04-def-extension-lin-3` | `とおく。順序を保つ写像 \(\alpha\colon I\to J\) について、\(I\ne\varnothi` | [未配置本文](issues.md#t04-def-extension-lin-3) |
| t-04:37 / `t04-def-initial-segment-1` | `全順序集合 \(J\) の部分集合 \(I\) が始切片であるとは、\(i\in I\)、\(j\le i\) ` | [未配置本文](issues.md#t04-def-initial-segment-1) |
| t-04:44 / `t04-def-join-1` | `単体的集合 \(K,L\) の join \(K\star L\) を` | [未配置本文](issues.md#t04-def-join-1) |
| t-04:45 / `t04-def-join-2` | `\[(K\star L)([n])=\bigsqcup_{I\sqsubseteq[n]}K^+(I)\time` | [未配置本文](issues.md#t04-def-join-2) |
| t-04:46 / `t04-def-join-3` | `で定める（\(K^+\)、\(L^+\) は定義 4.1、始切片は定義 4.2）。\(\theta\colon[` | [未配置本文](issues.md#t04-def-join-3) |
| t-04:47 / `t04-def-join-4` | `\[\bigl(K^+(\theta&#124;_{I'})(\sigma),\ L^+(\theta&#124;_{[m]\set` | [未配置本文](issues.md#t04-def-join-4) |
| t-04:48 / `t04-def-join-5` | `に送る。ここで \(\theta&#124;_{I'}\colon I'\to I\)、\(\theta&#124;_{[m]\se` | [未配置本文](issues.md#t04-def-join-5) |
| t-04:55 / `t04-rem-join-formula-1` | `\([n]\) の始切片は \(\varnothing\)、\(\{0,\dots,p\}\)（\(0\le p` | [未配置本文](issues.md#t04-rem-join-formula-1) |
| t-04:56 / `t04-rem-join-formula-2` | `\[(K\star L)([n])=L([n])\ \sqcup\bigsqcup_{p+1+q=n}K([p]` | [未配置本文](issues.md#t04-rem-join-formula-2) |
| t-04:57 / `t04-rem-join-formula-3` | `となる（Kerodon Remark 4.3.3.19）。\(I=\varnothing\) の成分が \(L(` | [未配置本文](issues.md#t04-rem-join-formula-3) |
| t-04:64 / `t04-def-join-functor-1` | `単体的集合の射 \(f\colon K\to K'\)、\(g\colon L\to L'\) について、\(f` | [未配置本文](issues.md#t04-def-join-functor-1) |
| t-04:65 / `t04-def-join-functor-2` | `\[\iota_K\colon K\to K\star L,\quad\sigma\mapsto(\sigma,` | [未配置本文](issues.md#t04-def-join-functor-2) |
| t-04:66 / `t04-def-join-functor-3` | `を定める。` | [未配置本文](issues.md#t04-def-join-functor-3) |
| t-04:73 / `t04-def-slice-1` | `単体的集合 \(X,K\) と射 \(p\colon K\to X\) について、単体的集合 \(X_{/p}\` | [未配置本文](issues.md#t04-def-slice-1) |
| t-04:74 / `t04-def-slice-2` | `\[X_{/p}([n])=\{\sigma\colon\Delta^n\star K\to X\mid\sig` | [未配置本文](issues.md#t04-def-slice-2) |
| t-04:75 / `t04-def-slice-3` | `で定め、\(\theta\colon[m]\to[n]\) はそれぞれ \(\theta_*\star\math` | [未配置本文](issues.md#t04-def-slice-3) |
| t-04:82 / `t04-def-identity-vertex-1` | `単体的集合 \(B\) の頂点 \(b\colon\Delta^0\to B\) について、合成 \(\Delt` | [未配置本文](issues.md#t04-def-identity-vertex-1) |
| t-04:89 / `t04-def-slice-projection-1` | `単体的集合の射 \(X_{/p}\to X\) を、\(n\) 単体 \(\sigma\colon\Delta^` | [未配置本文](issues.md#t04-def-slice-projection-1) |
| t-04:96 / `t04-rem-size-slice-1` | `定義 4.5 は \(X\)、\(K\) の大きさを問わず、\(X_{/p}([n])\) は集合 \(\mat` | [未配置本文](issues.md#t04-rem-size-slice-1) |
| t-04:103 / `t04-thm-slice-quasicategory-1` | `\(X\) を quasicategory（定義 1.8）、\(K\) を単体的集合、\(p\colon K\t` | [未配置本文](issues.md#t04-thm-slice-quasicategory-1) |
| t-05:28 / `t05-def-boundary-1` | `\(n\ge0\) について、\(\Delta^n\) の部分単体的集合 \(\partial\Delta^n=` | [原稿](1.1.4.10.md#t05-def-boundary-1) |
| t-05:35 / `t05-def-lifting-1` | `単体的集合の射 \(q\colon E\to B\) が部分単体的集合の包含 \(A\subseteq A'\)` | [原稿](1.5.4.3.md#t05-def-lifting-1) |
| t-05:42 / `t05-def-fibrations-1` | `単体的集合の射 \(q\colon E\to B\) が、次の表の包含のすべてに対して右持ち上げ性質（定義 5.` | [原稿](1.5.md#t05-def-fibrations-1) |
| t-05:45 / `t05-def-fibrations-3` | `Kan fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(n\ge1\)、` | [未配置本文](issues.md#t05-def-fibrations-3) |
| t-05:46 / `t05-def-fibrations-4` | `inner fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(0<i<n\` | [未配置本文](issues.md#t05-def-fibrations-4) |
| t-05:47 / `t05-def-fibrations-5` | `左 fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(0\le i<n\)` | [未配置本文](issues.md#t05-def-fibrations-5) |
| t-05:48 / `t05-def-fibrations-6` | `右 fibration\(\Lambda^n_i\subseteq\Delta^n\)（\(0<i\le n\)` | [未配置本文](issues.md#t05-def-fibrations-6) |
| t-05:49 / `t05-def-fibrations-7` | `trivial Kan fibration\(\partial\Delta^n\subseteq\Delta^n` | [原稿](1.5.5.1.md#t05-def-fibrations-7) |
| t-05:57 / `t05-rem-fibration-point-1` | `\(\Delta^0\) は各段が一点の単体的集合で、任意の単体的集合 \(X\) から唯一の射 \(X\to\` | [原稿](1.2.5.md#t05-rem-fibration-point-1) |
| t-05:64 / `t05-def-contractible-1` | `単体的集合 \(X\) が可縮であるとは、\(X\to\Delta^0\) が trivial Kan fibr` | [原稿](1.5.5.8.md#t05-def-contractible-1) |

## 項目に置けなかった段落

段落ごとの全件は上表の「未配置本文」。次表はそれらを元の環境単位にまとめたもの（省略ではない）。

| 元のまとまり | ブロック数 | 理由・第1章外の候補 |
| --- | --- | --- |
| t-02 `def-scat` | 1 | 単体的圏・Kan 複体の単体的圏・局所 Kan 性は第2・3章の内容（2.4.1.1、3.1.6.1、3.1.3）。 |
| t-02 `def-kan-category` | 5 | 単体的圏・Kan 複体の単体的圏・局所 Kan 性は第2・3章の内容（2.4.1.1、3.1.6.1、3.1.3）。 |
| t-02 `thm-kan-hom-kan` | 1 | 単体的圏・Kan 複体の単体的圏・局所 Kan 性は第2・3章の内容（2.4.1.1、3.1.6.1、3.1.3）。 |
| t-03 `def-sfunctor` | 1 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-03 `def-path-category` | 5 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-03 `def-hc-nerve` | 3 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-03 `thm-hc-functor` | 1 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-03 `rem-size-scat` | 1 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-03 `thm-hc-quasicategory` | 1 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-03 `def-spaces` | 1 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-03 `rem-size-spaces` | 1 | 単体的関手・coherent nerve は第2章（2.4.1.11、2.4.3.5、2.4.5.1）、空間の∞圏は第3章（3.1.6.1）。 |
| t-04 `def-extension-lin` | 3 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `def-initial-segment` | 1 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `def-join` | 5 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `rem-join-formula` | 3 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `def-join-functor` | 3 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `def-slice` | 3 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `def-identity-vertex` | 1 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `def-slice-projection` | 1 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `rem-size-slice` | 1 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-04 `thm-slice-quasicategory` | 1 | join・slice とその準備は第4章。原文自身が 4.3.3.19・4.3.6.1 を明記する。 |
| t-05 `def-fibrations` | 4 | Kan・inner・左・右 fibration は第3・4章（3.1.1.1、4.1.1.1、4.2.1.1）。trivial Kan の行だけ第1章。 |

計 43 環境・88 ブロック。番号別・節別原稿へ 41、issues.md に保留 47。原稿 19 ファイル（項目 14、導入・つなぎ 5）。未記録の本文ブロックは0。
