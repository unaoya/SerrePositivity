# NB-W1 で分かったこと

2026-11-17。以下は転記の所見であり、文書設計の確定や数学本文の修正ではない。

## 粒度

1. **入力5ページと Kerodon 第1章の範囲が一致しない。** t-03 の「局所 Kan なら quasicategory」は 2.4.5.1、空間の∞圏は 3.1.6.1。t-04 は本文自身が Remark 4.3.3.19 と Proposition 4.3.6.1 を引く。これらを `1.5.md` 等へ入れると、第1章の導入という誤った分類になる。第1章に配置できない47ブロックは末尾に全文を保留し、README に全件の行き先を載せた。将来は第2〜4章の原稿へ移すか、第1章とは別の横断的解説を持つかの判断が必要。
2. **一段落が二つの項目を説明する。** t-01 `def-sset` は単体的集合の定義と射の自然変換を一つの p で説明し、1.1.0.6 と 1.1.0.7 にまたがる。文言を変えて二分せず、主たる定義の `1.1.0.6.md` に一度だけ置いた。`def-delta` も [n] の記法（1.1.0.1）と圏（1.1.0.2）を合わせ、`1.1.0.2.md` に置いた。項目と原稿を常に一対一にするより、主たる項目と副参照を区別する必要がある。
3. **一つの説明が複数の p に分かれる。** t-01 の和、面、horn、t-02 の写像単体的集合は「導入 → 式 → で定める」のまとまり。p 単位に追跡するが本文は同じ原稿内で順序を維持した。式だけを別ノードへ送ると「で定める。」の指示対象が消える。`1.2.4.1.md` は horn の二通りの定義と一致の説明をすべて保つ。
4. **項目表と review の粒度も異なる。** `1.1.0.9.md`（標準単体、Tag 04Z6）と `1.1.0.14.md`（部分単体的集合、Tag 000P）は item-tags.csv / items.csv に実在するが、180件の review/ch1.csv には行がない。似た項目の 1.1.0.12（米田の全単射）を標準単体の定義の代役にはしなかった。この2原稿は Tag だけを結び、Lean の状態は付けていない。
5. **導入・つなぎには補助的な構成も入る。** 宇宙の規約は `1.1.md`、horn を読むための面の記述は `1.2.4.md`、積・後合成・合成と単位の記述は `1.5.3.md`。後者は内部 Hom の説明を支えるが、豊穣圏の定義そのものは含めず保留した。一点への射と Kan / quasicategory の比較は `1.2.5.md` にまとめ、1.4.0.1 との関係はこの所見で明示する。節原稿は「その節の全数学の対応が済んだ」という意味ではない。
6. **表の一部だけが第1章に入る。** t-05 定義5.3の導入 p は `1.5.md`、trivial Kan の行は `1.5.5.1.md`、他4行は保留本文。表見出し「名前・包含」は各行の読解のため再掲した。元の「次の表」は文言どおり残るが、単独の導入原稿には表がない。この指示語の断絶を隠さず、将来の生成時には元の表を横断的解説として再構成するか、本文の修正を別途行う必要がある。

## 置き場所

- `research/kerodon-coverage/notes/` は、番号・Tag と本文外の Lean 宣言を伴う原稿の試験場所としては扱いやすい。`1.5.3.2.md` の冒頭には既存 review の随伴の宣言をそのまま置き、本文は積と写像単体的集合の随伴を説明する。形式化の判定と説明文を混同しないため、本文外の照合先と転記部分を分けた。状態の正本は review のまま。
- リポジトリの Documents 規則では research が数学の根拠として引くのは文献と Lean。原稿冒頭の数学上の引用は Kerodon の Tag と既存 review の Lean 名に限った。凍結 exposition のパスは転記来歴のコメント・移動表であり、新しい数学的根拠にはしていない。正式な形にする際、来歴情報を本文から分離して持つことは検討できる。
- ただし、保存した「定義2.2」等の参照は旧解説内の依存であり、移設後も原稿間リンク（保留本文へのリンクを含む）が残る。研究データが文献・Leanのみを引く規則に厳密に合わせるには、原稿間リンクを数学的な根拠とせず生成時の解説内参照として扱う区別が要る。現状をその区別の実装済みと見なさない。原文を変えない試しとして残し、正式採用の判断材料にする。
- `notes/` を恒久の正本にするか、横断的解説を別にするかは保留。blueprint に手書き原稿を置くこと、凍結 exposition を更新すること、対応表の理由へ解説を押し込むことは今回行っていない。issues.md は観察・保留本文であり、番号別本文として読み込んではいけない。

## Verso への変換

| 種類 | 入力中の例・有無 | 試しの Markdown と変換時の問題 |
| --- | --- | --- |
| 表 | t-05 `def-fibrations` の5種類の fibration | pipe table に移した。trivial Kan だけ別原稿、残り4行は保留。別ノードに切った表の再構成、見出しの重複、導入の「次の表」の参照先は生成側で要判断。表中の数式を単なるコードにしてはいけない。 |
| 図 | 対象5ページに img・svg・canvas・figure はない | 実図の変換例は得られなかった。t-02 の合成式の `\\xrightarrow` は画像ではなく数式として保存。画像パスや代替文の移設が解決済みとは言えない。 |
| 囲み | `<div class="box">` はないが、全43環境に `<div class="env definition/theorem/remark/convention">` と env-head/env-body がある | Markdown では元の見出しを `##` にし本文を続けた。色・枠は保存していない。たとえば「定理2.4」は Kerodon の Proposition 1.5.3.2 の原稿に入る。Verso の proposition ノードにさらに theorem を入れるのか、見出しだけにするのか、旧番号の表示をどうするかは未決。box 特有の入れ子は対象にない。 |
| pre の図 | 対象に pre 要素はない | ASCII 図・空白依存の図の移設は未試験。数式を pre やコードフェンスに落とす代用はしていない。対象にない図を作って検証済みとはしない。 |
| 数式の環境 | t-04 `def-extension-lin` の `\\begin{cases}`、t-02 の `\\xrightarrow`、集合の `\\mid`、join の `\\bigsqcup` | KaTeX の元の区切り `\( \)`・`\[ \]` と内部 TeX を保存した。HTML の `&amp;` は `&`、`&lt;` は `<` に戻す。元HTMLのエンコード済みバイト列と比較すると違うが、数式の可視ソースは同じ。Verso は現生成器の `esc()` を本文全体へそのままかけるとバックスラッシュ等をエスケープするため、数式・通常文・リンク・コードを分けて扱う必要がある。cases のレンダリング自体はビルドしていない。 |
| ページ間・ページ内リンク | t-03 空間の定義から t-02 定義2.8・定理2.9、t-04 slice から t-02 定義2.2 | 表示文言を保持し、リンクだけ移設先のブロックIDへ変えた。前者は保留本文、後者は `1.5.3.1.md` を指す。旧 `#def-fun` は別ページで同名になりうるので、元ページ名と id の組で解決した。Verso では Markdown ファイル名をそのまま公開URLにせず、ノードラベルと解説用アンカーへ変換する必要がある。 |
| Lean 宣言名 | 入力の本文には code 要素・Lean 宣言名がない | 原稿冒頭の照合先だけ既存 review からバッククォートで転記した。本文中のコードを含む HTML の変換はこの5ページでは試せていない。タグや数式と同じ一括エスケープをかける前に code を区別する必要がある。 |
| 来歴アンカー・箇条書き | `1.2.4.1.md` の二通りの horn と各 li の前のコメント・a 要素 | 追跡用IDは raw HTML。Markdownとして読めても、Verso が同じ anchor を出力する保証はない。各 li を独立追跡するため間にアンカーが入り、通常の Markdown レンダラーではリストが分割されうる。生成時には構造上の一つのリストを保持し、追跡メタデータを別管理する案が必要。 |

変換器の仕様はここで決めず、`blueprint/scripts/gen_kerodon.py` と生成済み Lean は未変更。Verso・Lean の実行、ビルド、ブラウザー描画の確認もしていない。

## 原文のまま残した注意点

- t-01 定義1.9は「すべての \(0\le i\le n\)」と書くが、同ページの horn の定義は \(n\ge1\)。定義1.9単独では正次数の条件が明示されない。quasicategory の内 horn では不等式が次数を制限するが、Kan 側はそうではない。これは量化範囲の記述上の不足として記録し、原稿を補筆しなかった。
- t-03 `def-path-category` の \(P_{ij}\) は「包含」で順序づける。既存 review/ch2.csv の2.4.3.5は、Lean の包含順と Kerodon の逆包含との規約差を記録する。したがってこの文章を Kerodon の定義そのものの写しとしてラベル付けしたり、既存 partial 判定を変更したりしない。今回は章外なので全文保留。
- t-05「可縮」は境界の全充填（終射が trivial Kan）という強い意味で、単体的集合の弱可縮性一般の言い換えではない。1.5.5.8に対応させ、旧見出しの語はそのまま残した。
- 旧解説番号「定義1.3」と Kerodon の Example 1.1.0.9 は番号も種類も違う。見出しは provenance を示す旧見出しであり、Kerodon の項目種別を上書きしない。


## 未配置本文（第1章への生成対象外）

本文の欠落を避けるための保留。旧番号・文言・数式を変えず転記した。元の各段落の行き先は README に列挙した。

## 定義 2.7 （単体的圏）

<!-- source: exposition/ja/infinity/t-02-kan-category.html:77; block: t02-def-scat-1 -->
<a id="t02-def-scat-1"></a>

単体的圏とは、対象の集合と、対象 \(x,y\) ごとの単体的集合 \(\mathcal C(x,y)\)、単体的集合の射としての合成 \(\mathcal C(y,z)\times\mathcal C(x,y)\to\mathcal C(x,z)\)、恒等射 \(\mathrm{id}_x\in\mathcal C(x,x)([0])\) の組で、合成が結合的かつ単位的であるものをいう。


## 定義 2.8 （Kan 複体のなす単体的圏 \(\mathcal Kan\)）

<!-- source: exposition/ja/infinity/t-02-kan-category.html:84; block: t02-def-kan-category-1 -->
<a id="t02-def-kan-category-1"></a>

単体的圏 \(\mathcal Kan\) を次で定める。

<!-- source: exposition/ja/infinity/t-02-kan-category.html:86; block: t02-def-kan-category-2 -->
<a id="t02-def-kan-category-2"></a>

- 対象：小さい Kan 複体（[定義 1.9](1.2.5.1.md#t01-def-kan-1)、[冒頭の規約](1.1.md#t01-conv-universe-1)）。

<!-- source: exposition/ja/infinity/t-02-kan-category.html:87; block: t02-def-kan-category-3 -->
<a id="t02-def-kan-category-3"></a>

- 射の単体的集合：\(\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)\)（[定義 2.2](1.5.3.1.md#t02-def-fun-1)）。

<!-- source: exposition/ja/infinity/t-02-kan-category.html:88; block: t02-def-kan-category-4 -->
<a id="t02-def-kan-category-4"></a>

- 合成と恒等射：[定義 2.5](1.5.3.md#t02-def-composition-1)。

<!-- source: exposition/ja/infinity/t-02-kan-category.html:90; block: t02-def-kan-category-5 -->
<a id="t02-def-kan-category-5"></a>

[定理 2.6](1.5.3.md#t02-thm-composition-1) によりこれは単体的圏である。


## 定理 2.9 （\(\mathcal Kan\) の射の単体的集合は Kan 複体）

<!-- source: exposition/ja/infinity/t-02-kan-category.html:97; block: t02-thm-kan-hom-kan-1 -->
<a id="t02-thm-kan-hom-kan-1"></a>

Kan 複体 \(X,Y\) について、\(\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)\) は Kan 複体である。


## 定義 3.1 （単体的関手）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:28; block: t03-def-sfunctor-1 -->
<a id="t03-def-sfunctor-1"></a>

単体的圏 \(\mathcal C,\mathcal D\) の間の単体的関手 \(F\colon\mathcal C\to\mathcal D\) とは、対象の対応 \(x\mapsto F(x)\) と、対象 \(x,y\) ごとの単体的集合の射 \(F_{x,y}\colon\mathcal C(x,y)\to\mathcal D(F(x),F(y))\) の組で、合成と恒等射を保つものをいう。単体的圏と単体的関手のなす圏を \(\mathrm{sCat}\) と書く。


## 定義 3.3 （\(\mathfrak C[\Delta^n]\)）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:42; block: t03-def-path-category-1 -->
<a id="t03-def-path-category-1"></a>

\(n\ge0\) について、単体的圏 \(\mathfrak C[\Delta^n]\) を次で定める。

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:44; block: t03-def-path-category-2 -->
<a id="t03-def-path-category-2"></a>

- 対象：\(0,1,\dots,n\)。

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:45; block: t03-def-path-category-3 -->
<a id="t03-def-path-category-3"></a>

- 射の単体的集合：\(i\le j\) なら \(\mathfrak C[\Delta^n](i,j)=N(P_{ij})\)。ここで \(P_{ij}\) は \(\{i,j\}\subseteq S\subseteq\{i,i+1,\dots,j\}\) をみたす部分集合 \(S\) の全体に包含で順序を入れた半順序集合。\(i>j\) なら空。

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:46; block: t03-def-path-category-4 -->
<a id="t03-def-path-category-4"></a>

- 合成：和集合 \(P_{jk}\times P_{ij}\to P_{ik}\)、\((T,S)\mapsto T\cup S\) が誘導する射 \(N(P_{jk})\times N(P_{ij})\to N(P_{ik})\)。恒等射は \(\{i\}\in P_{ii}\)。

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:48; block: t03-def-path-category-5 -->
<a id="t03-def-path-category-5"></a>

\(\theta\colon[m]\to[n]\) について、単体的関手 \(\mathfrak C[\theta]\colon\mathfrak C[\Delta^m]\to\mathfrak C[\Delta^n]\) を、対象を \(i\mapsto\theta(i)\)、射を \(S\mapsto\theta(S)\) で定める。これにより関手 \(\mathfrak C\colon\Delta\to\mathrm{sCat}\) が得られる。


## 定義 3.4 （homotopy coherent nerve）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:55; block: t03-def-hc-nerve-1 -->
<a id="t03-def-hc-nerve-1"></a>

単体的圏 \(\mathcal C\) について、単体的集合 \(N^{hc}(\mathcal C)\) を

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:56; block: t03-def-hc-nerve-2 -->
<a id="t03-def-hc-nerve-2"></a>

\[N^{hc}(\mathcal C)([n])=\mathrm{Hom}_{\mathrm{sCat}}(\mathfrak C[\Delta^n],\mathcal C),\qquad N^{hc}(\mathcal C)(\theta)(\sigma)=\sigma\circ\mathfrak C[\theta]\]

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:57; block: t03-def-hc-nerve-3 -->
<a id="t03-def-hc-nerve-3"></a>

で定める。


## 定理 3.5 （関手性）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:64; block: t03-thm-hc-functor-1 -->
<a id="t03-thm-hc-functor-1"></a>

単体的関手 \(F\colon\mathcal C\to\mathcal D\) に後合成 \(\sigma\mapsto F\circ\sigma\) を対応させることで、\(N^{hc}\) は関手 \(\mathrm{sCat}\to\mathrm{sSet}\) になる。


## 注意 （大きさ）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:71; block: t03-rem-size-scat-1 -->
<a id="t03-rem-size-scat-1"></a>

[定理 3.5](issues.md#t03-thm-hc-functor-1) の \(\mathrm{sCat}\) と \(\mathrm{sSet}\) は、大きさを制限しない、すべての単体的圏（対象が集合をなすもの）とすべての単体的集合の圏である。どちらも対象の全体は集合にならず、各 \(\mathrm{Hom}\) は集合だが小さいとは限らない。\(N^{hc}\) を単体的集合として定めるのに必要なのは \(\mathcal C\) の対象が集合をなすことで、\(\mathcal C\) が小さいことは要らない。


## 定理 3.6 （局所 Kan なら quasicategory）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:78; block: t03-thm-hc-quasicategory-1 -->
<a id="t03-thm-hc-quasicategory-1"></a>

単体的圏 \(\mathcal C\) のすべての射の単体的集合 \(\mathcal C(x,y)\) が Kan 複体であるとき（\(\mathcal C\) は局所 Kan であるという）、\(N^{hc}(\mathcal C)\) は quasicategory である。


## 定義 3.7 （空間の ∞ 圏 \(\mathcal S\)）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:85; block: t03-def-spaces-1 -->
<a id="t03-def-spaces-1"></a>

\(\mathcal S=N^{hc}(\mathcal Kan)\) と定める（\(\mathcal Kan\) は[定義 2.8](issues.md#t02-def-kan-category-1)）。[定理 2.9](issues.md#t02-thm-kan-hom-kan-1) により \(\mathcal Kan\) は局所 Kan なので、[定理 3.6](issues.md#t03-thm-hc-quasicategory-1) により \(\mathcal S\) は quasicategory である。


## 注意 （\(\mathcal S\) の大きさ）

<!-- source: exposition/ja/infinity/t-03-coherent-nerve.html:92; block: t03-rem-size-spaces-1 -->
<a id="t03-rem-size-spaces-1"></a>

\(\mathcal Kan\) の対象は小さい Kan 複体で、その全体は \(\mathbb U\) の部分集合として集合をなすが、小さくはない。したがって \(\mathcal S\) は単体的集合だが小さくない。一方、小さい Kan 複体 \(X,Y\) について \(\mathcal Kan(X,Y)=\mathrm{Fun}(X,Y)\) は小さい（宇宙は直積と冪集合で閉じている）。


## 定義 4.1 （有限全順序集合での値 \(X^+\)）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:28; block: t04-def-extension-lin-1 -->
<a id="t04-def-extension-lin-1"></a>

有限な全順序集合 \(I\)（空でもよい）について、\(I\) が空でなければ \(|I|=n+1\) として唯一の順序同型 \(r_I\colon I\xrightarrow{\cong}[n]\) をとる。単体的集合 \(X\) について

<!-- source: exposition/ja/infinity/t-04-join-slice.html:29; block: t04-def-extension-lin-2 -->
<a id="t04-def-extension-lin-2"></a>

\[X^+(I)=\begin{cases}X([n])&(I\ne\varnothing)\\ \{\ast\}&(I=\varnothing)\end{cases}\]

<!-- source: exposition/ja/infinity/t-04-join-slice.html:30; block: t04-def-extension-lin-3 -->
<a id="t04-def-extension-lin-3"></a>

とおく。順序を保つ写像 \(\alpha\colon I\to J\) について、\(I\ne\varnothing\) なら \(X^+(\alpha)=X(r_J\circ\alpha\circ r_I^{-1})\colon X^+(J)\to X^+(I)\)、\(I=\varnothing\) なら一点集合への唯一の写像とする。


## 定義 4.2 （始切片）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:37; block: t04-def-initial-segment-1 -->
<a id="t04-def-initial-segment-1"></a>

全順序集合 \(J\) の部分集合 \(I\) が始切片であるとは、\(i\in I\)、\(j\le i\) なら \(j\in I\) となることをいい、\(I\sqsubseteq J\) と書く（空集合と \(J\) 自身も始切片である）。順序を保つ写像 \(\theta\colon J'\to J\) と始切片 \(I\sqsubseteq J\) について、\(\theta^{-1}(I)\sqsubseteq J'\) である。


## 定義 4.3 （単体的集合の join）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:44; block: t04-def-join-1 -->
<a id="t04-def-join-1"></a>

単体的集合 \(K,L\) の join \(K\star L\) を

<!-- source: exposition/ja/infinity/t-04-join-slice.html:45; block: t04-def-join-2 -->
<a id="t04-def-join-2"></a>

\[(K\star L)([n])=\bigsqcup_{I\sqsubseteq[n]}K^+(I)\times L^+([n]\setminus I)\]

<!-- source: exposition/ja/infinity/t-04-join-slice.html:46; block: t04-def-join-3 -->
<a id="t04-def-join-3"></a>

で定める（\(K^+\)、\(L^+\) は[定義 4.1](issues.md#t04-def-extension-lin-1)、始切片は[定義 4.2](issues.md#t04-def-initial-segment-1)）。\(\theta\colon[m]\to[n]\) は、\(I\) の成分の元 \((\sigma,\tau)\) を、\(I'=\theta^{-1}(I)\) の成分の元

<!-- source: exposition/ja/infinity/t-04-join-slice.html:47; block: t04-def-join-4 -->
<a id="t04-def-join-4"></a>

\[\bigl(K^+(\theta|_{I'})(\sigma),\ L^+(\theta|_{[m]\setminus I'})(\tau)\bigr)\]

<!-- source: exposition/ja/infinity/t-04-join-slice.html:48; block: t04-def-join-5 -->
<a id="t04-def-join-5"></a>

に送る。ここで \(\theta|_{I'}\colon I'\to I\)、\(\theta|_{[m]\setminus I'}\colon[m]\setminus I'\to[n]\setminus I\) は \(\theta\) の制限である。


## 注意 （段ごとの公式）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:55; block: t04-rem-join-formula-1 -->
<a id="t04-rem-join-formula-1"></a>

\([n]\) の始切片は \(\varnothing\)、\(\{0,\dots,p\}\)（\(0\le p<n\)）、\([n]\) のいずれかなので、[定義 4.3](issues.md#t04-def-join-1) は段ごとには

<!-- source: exposition/ja/infinity/t-04-join-slice.html:56; block: t04-rem-join-formula-2 -->
<a id="t04-rem-join-formula-2"></a>

\[(K\star L)([n])=L([n])\ \sqcup\bigsqcup_{p+1+q=n}K([p])\times L([q])\ \sqcup\ K([n])\]

<!-- source: exposition/ja/infinity/t-04-join-slice.html:57; block: t04-rem-join-formula-3 -->
<a id="t04-rem-join-formula-3"></a>

となる（Kerodon Remark 4.3.3.19）。\(I=\varnothing\) の成分が \(L([n])\)、\(I=\{0,\dots,p\}\) の成分が \(K([p])\times L([q])\)、\(I=[n]\) の成分が \(K([n])\) である。この表示で \(\theta\) の作用を書くと、\(\theta\) の像が \(I\) と \([n]\setminus I\) のどちらに入るかで場合分けが要る。


## 定義 4.4 （join の関手性と包含）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:64; block: t04-def-join-functor-1 -->
<a id="t04-def-join-functor-1"></a>

単体的集合の射 \(f\colon K\to K'\)、\(g\colon L\to L'\) について、\(f\star g\colon K\star L\to K'\star L'\) を各成分で \((\sigma,\tau)\mapsto(f(\sigma),g(\tau))\) により定める（\(\ast\) は \(\ast\) に送る）。また包含

<!-- source: exposition/ja/infinity/t-04-join-slice.html:65; block: t04-def-join-functor-2 -->
<a id="t04-def-join-functor-2"></a>

\[\iota_K\colon K\to K\star L,\quad\sigma\mapsto(\sigma,\ast)\ (I=[n]\text{ の成分}),\qquad \iota_L\colon L\to K\star L,\quad\tau\mapsto(\ast,\tau)\ (I=\varnothing\text{ の成分})\]

<!-- source: exposition/ja/infinity/t-04-join-slice.html:66; block: t04-def-join-functor-3 -->
<a id="t04-def-join-functor-3"></a>

を定める。


## 定義 4.5 （スライスとコスライス）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:73; block: t04-def-slice-1 -->
<a id="t04-def-slice-1"></a>

単体的集合 \(X,K\) と射 \(p\colon K\to X\) について、単体的集合 \(X_{/p}\) と \(X_{p/}\) を

<!-- source: exposition/ja/infinity/t-04-join-slice.html:74; block: t04-def-slice-2 -->
<a id="t04-def-slice-2"></a>

\[X_{/p}([n])=\{\sigma\colon\Delta^n\star K\to X\mid\sigma\circ\iota_K=p\},\qquad X_{p/}([n])=\{\sigma\colon K\star\Delta^n\to X\mid\sigma\circ\iota_K=p\}\]

<!-- source: exposition/ja/infinity/t-04-join-slice.html:75; block: t04-def-slice-3 -->
<a id="t04-def-slice-3"></a>

で定め、\(\theta\colon[m]\to[n]\) はそれぞれ \(\theta_*\star\mathrm{id}_K\)、\(\mathrm{id}_K\star\theta_*\) の前合成で作用させる（\(\theta_*\) は[定義 2.2](1.5.3.1.md#t02-def-fun-1)、\(\star\) と \(\iota_K\) は[定義 4.3](issues.md#t04-def-join-1)・[定義 4.4](issues.md#t04-def-join-functor-1)）。\(X_{/p}\) をスライス、\(X_{p/}\) をコスライスという。


## 定義 4.6 （恒等頂点）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:82; block: t04-def-identity-vertex-1 -->
<a id="t04-def-identity-vertex-1"></a>

単体的集合 \(B\) の頂点 \(b\colon\Delta^0\to B\) について、合成 \(\Delta^0\star\Delta^0\to\Delta^0\xrightarrow{b}B\) は \(\Delta^0\) 上で \(b\) となるので、コスライス \(B_{b/}\) の頂点を定める。これを \(\mathrm{id}_b\) と書く。スライス \(B_{/b}\) の頂点 \(\mathrm{id}_b\) も同様に定める（[定義 4.5](issues.md#t04-def-slice-1)）。


## 定義 4.7 （スライスとコスライスの射影）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:89; block: t04-def-slice-projection-1 -->
<a id="t04-def-slice-projection-1"></a>

単体的集合の射 \(X_{/p}\to X\) を、\(n\) 単体 \(\sigma\colon\Delta^n\star K\to X\) を \(\sigma\circ\iota_{\Delta^n}\colon\Delta^n\to X\)、すなわち \(X([n])\) の元に送ることで定める。同様に \(X_{p/}\to X\) を、\(\sigma\colon K\star\Delta^n\to X\) を \(\sigma\circ\iota_{\Delta^n}\) に送ることで定める（\(\iota_{\Delta^n}\) は[定義 4.4](issues.md#t04-def-join-functor-1) の包含。\(\Delta^n\to X\) と \(X([n])\) の元は米田の補題で同一視する）。


## 注意 （大きさ）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:96; block: t04-rem-size-slice-1 -->
<a id="t04-rem-size-slice-1"></a>

[定義 4.5](issues.md#t04-def-slice-1) は \(X\)、\(K\) の大きさを問わず、\(X_{/p}([n])\) は集合 \(\mathrm{Hom}_{\mathrm{sSet}}(\Delta^n\star K,X)\) の部分集合である。\(X\) と \(K\) が小さければ \(X_{/p}\)、\(X_{p/}\) も小さい。[定義 4.1](issues.md#t04-def-extension-lin-1) では有限全順序集合の全体を一つの圏としては使わず、個々の \(I\) と \(\alpha\) に対して値を定めているだけである。


## 定理 4.8 （quasicategory のスライス）

<!-- source: exposition/ja/infinity/t-04-join-slice.html:103; block: t04-thm-slice-quasicategory-1 -->
<a id="t04-thm-slice-quasicategory-1"></a>

\(X\) を quasicategory（[定義 1.8](1.4.0.1.md#t01-def-quasicategory-1)）、\(K\) を単体的集合、\(p\colon K\to X\) を射とする。このとき \(X_{/p}\) と \(X_{p/}\) は quasicategory である（Kerodon Proposition 4.3.6.1）。


## 定義 5.3 （fibration）

<!-- source: exposition/ja/infinity/t-05-fibrations.html:45; block: t05-def-fibrations-3 -->
<a id="t05-def-fibrations-3"></a>

| 名前 | 包含 |
| --- | --- |
| Kan fibration | \(\Lambda^n_i\subseteq\Delta^n\)（\(n\ge1\)、\(0\le i\le n\)） |

<!-- source: exposition/ja/infinity/t-05-fibrations.html:46; block: t05-def-fibrations-4 -->
<a id="t05-def-fibrations-4"></a>

| 名前 | 包含 |
| --- | --- |
| inner fibration | \(\Lambda^n_i\subseteq\Delta^n\)（\(0<i<n\)） |

<!-- source: exposition/ja/infinity/t-05-fibrations.html:47; block: t05-def-fibrations-5 -->
<a id="t05-def-fibrations-5"></a>

| 名前 | 包含 |
| --- | --- |
| 左 fibration | \(\Lambda^n_i\subseteq\Delta^n\)（\(0\le i<n\)） |

<!-- source: exposition/ja/infinity/t-05-fibrations.html:48; block: t05-def-fibrations-6 -->
<a id="t05-def-fibrations-6"></a>

| 名前 | 包含 |
| --- | --- |
| 右 fibration | \(\Lambda^n_i\subseteq\Delta^n\)（\(0<i\le n\)） |
