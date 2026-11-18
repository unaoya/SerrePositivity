# 証明の方針

<!-- NB-W4: 凍結解説から転記。 -->

## アイデア：古典的な Cohen–Macaulay の場合

<!-- source: exposition/ja/exposition-ja.tex:137; block: paper-ja-L137 -->
<a id="paper-ja-L137"></a>

\(D\) と \(E\) がどちらも Cohen–Macaulay なら、高次の Tor が消えて \(\chi^R(D,E) = \operatorname{length}(D\otimes_R E) > 0\) となる。論文は本物の CM 加群の代わりに、長さ関数 \(\lambda\) の目で CM な巨大代数 \(C_D\)、\(C_E\)（**\(\lambda\)-CM 代数**、定義 4.14）を使い、次の古典的事実の \(\lambda\) 版で高次の項を消す。

<!-- source: exposition/ja/exposition-ja.tex:139; block: paper-ja-L139 -->
<a id="paper-ja-L139"></a>

- \(D\) 側：CM 加群の射影次元は低い（Auslander–Buchsbaum の公式）。\(\lambda\) 版は補題 5.14。

<!-- source: exposition/ja/exposition-ja.tex:140; block: paper-ja-L140 -->
<a id="paper-ja-L140"></a>

- \(E\) 側：巨大 CM 代数とテンソルすると、短い有限自由複体の高次ホモロジーが消える（Hochster による新交叉定理の議論）。\(\lambda\) 版は補題 5.10 と補題 6.11。

<!-- source: exposition/ja/exposition-ja.tex:141; block: paper-ja-L141 -->
<a id="paper-ja-L141"></a>

- 残る \(0\) 次の項が正であることは、巨大 CM 代数の非自明性 \(\mathfrak{m} B\ne B\) の \(\lambda\) 版（系 8.7）による。

## 基底と Galois 閉包：2段階の準備

<!-- source: exposition/ja/exposition-ja.tex:145; block: paper-ja-L145 -->
<a id="paper-ja-L145"></a>

\(D\) は正則でないので、比較を直接示せる場所（命題 7.2：\(K_0\) が Koszul 複体で生成される）としても、\(\lambda\)-平坦性を定義する場所（定義 4.9）としても使えない。そこで次の2段階の準備をする。

1. [正則な基底をとる（本論文 Lemma 2.2 の原稿）](../2.2.md#paper-ja-L147)

<!-- source: exposition/ja/exposition-ja.tex:148; block: paper-ja-L148 -->
<a id="paper-ja-L148"></a>

2. **Galois にする**：比べたい複体は \(D\) 上にあって \(A_D\) からは来ないので、その類を \(A_D\) に戻す必要がある。戻す手段は定理 7.3（有理 K 理論の降下）で、幾何ファイバーに推移的に作用する群が要る。\(D/A_D\) は Galois とは限らないので、\(\operatorname{Frac}(D)/\operatorname{Frac}(A_D)\) の Galois 閉包における \(A_D\) の整閉包 \(D'\) に上げ、Galois 群 \(G_D\) を得る。1段目で分離性を課したのはこのためである。代わりに \(\chi^R(D,E)\) が \(\chi^R(D',E')\) に変わり、ランクの因子 \(a_D = \operatorname{rank}_D D'\) がつく。

<!-- source: exposition/ja/exposition-ja.tex:150; block: paper-ja-L150 -->
<a id="paper-ja-L150"></a>

\(E\) についても同様に \(A_E\)、\(E'\)、\(G_E\)、\(a_E = \operatorname{rank}_E E'\) をとる（詳細は §9）。

## 記号

<!-- source: exposition/ja/exposition-ja.tex:153; block: paper-ja-L153 -->
<a id="paper-ja-L153"></a>

\(\sigma\in G_D\) に対し、\(C_D\) に \(R\to D'\xrightarrow{\sigma}D'\to C_D\) で \(R\) 作用を入れたものを \(C_D^\sigma\) と書く。\(C_E^\gamma\)（\(\gamma\in G_E\)）も同様。

## 2回の置き換え

<!-- source: exposition/ja/exposition-ja.tex:156; block: paper-ja-L156 -->
<a id="paper-ja-L156"></a>

\(\chi\) を変えずに \(D\) と \(E\) を1つずつ置き換える。個々の値はひねりで変わりうるが、Galois 共役の和をとると変わらない。

[置き換え 1（本論文の式 (5.3) の原稿）](../%285.3%29.md#paper-ja-L158)

<!-- source: exposition/ja/exposition-ja.tex:163–167; block: paper-ja-L163 -->
<a id="paper-ja-L163"></a>

**置き換え 2**（\(E'\to C_E\)、式 （9.1））．ランク無視の圏でのノルム比較（§6）により、各 \(\sigma\) について

\[
|G_E|\, \sum_i (-1)^i\, \lambda_D \operatorname{Tor}_i^R(C_D^\sigma, E') \;=\; \sum_{\gamma\in G_E} \chi_{\lambda_E}\bigl(\text{$C_D^\sigma$ の有限近似} \otimes C_E^\gamma\bigr). \tag{2.2}
\]

右辺の各項は、\(C_D^\sigma\) を有限長加群の列で近似し、その分解を \(\gamma\) でひねって \(C_E\) とテンソルした複体の列について、\(\lambda_E\) で測った Euler 特性を列の大きさ \(s_n\) で割って超極限をとったものである（§9）。直観的には「\(C_D^\sigma\) と \(C_E^\gamma\) の Tor を、\(\lambda_D\) と \(\lambda_E\) の両方で測った Euler 特性」である。

<!-- source: exposition/ja/exposition-ja.tex:169–172; block: paper-ja-L169 -->
<a id="paper-ja-L169"></a>

**正値性**（補題 9.6）．両側が CM もどきなので、（2.2） の右辺の各項は \(0\) 次の項だけになり、正。したがって

\[
|G_D|\, a_D a_E\, \chi^R(D,E) \;=\; \frac{1}{|G_E|}\sum_{\sigma\in G_D}\sum_{\gamma\in G_E} \chi_{\lambda_E}\bigl(\text{$C_D^\sigma$ の有限近似} \otimes C_E^\gamma\bigr) \;>\; 0.
\]

## ノルム比較の型

<!-- source: exposition/ja/exposition-ja.tex:175; block: paper-ja-L175 -->
<a id="paper-ja-L175"></a>

2回の置き換えは同じ型の議論である。右の因子 \(T\) を \(C_T\) に置き換えるため、左の因子の自由分解と \(T\) のテンソルとして「閉点に台をもつ対象」\(X\) を作り、

<!-- source: exposition/ja/exposition-ja.tex:177; block: paper-ja-L177 -->
<a id="paper-ja-L177"></a>

- 普通の長さで測ると元の \(\chi\)（Galois でひねっても変わらない）

<!-- source: exposition/ja/exposition-ja.tex:178; block: paper-ja-L178 -->
<a id="paper-ja-L178"></a>

- \(X\otimes C_T\) を \(\lambda\) で測ると置き換えた量（ひねりで変わりうる）

<!-- source: exposition/ja/exposition-ja.tex:180; block: paper-ja-L180 -->
<a id="paper-ja-L180"></a>

の2つが、共役の和の上で一致する。一致の理由は「正則な基底 \(A\) から来る類では一致する」と「共役の和は有理的に \(A\) から来る（定理 7.3、有理 K 理論の降下）」の組み合わせ。

<!-- source: exposition/ja/exposition-ja.tex:182–194; block: paper-ja-L182 -->
<a id="paper-ja-L182"></a>

|  | 置き換え 1 | 置き換え 2 |
| --- | --- | --- |
| 左の因子 | \(E'\) | \(C_D^\sigma\) |
| 置き換えるもの | \(D' \to C_D\) | \(E' \to C_E\) |
| 対象 \(X\) | \(E'\) の有限自由分解 \(\otimes\, D'\) | \(C_D^\sigma\) の有限近似の切り詰めた分解 \(\otimes\, E'\) の列 |
| 対象が住む圏 | \(\operatorname{Perf}_{\mathfrak{m}}(D')\) | \(P_{E'}^J\)（ランク無視の圏） |
| 比較定理 | 命題 7.5 | 定理 7.9 |

<!-- source: exposition/ja/exposition-ja.tex:196; block: paper-ja-L196 -->
<a id="paper-ja-L196"></a>

置き換え 2 で左の因子 \(C_D^\sigma\) が有限加群でないために、有限近似と「ランク \(o(s_n)\) を無視する圏」が必要になる。これが論文 §4 の存在理由である。

## 証明の骨格

<!-- source: exposition/ja/exposition-ja.tex:199; block: paper-ja-L199 -->
<a id="paper-ja-L199"></a>

以下では、二つの置き換えと正値性に共通する四つの道具を先に抽象的に述べ（§3）、評価先を長さ付き代数から作る（§4）。その上で、評価元を perfect 複体とランク無視の圏にとった二つの実現を一般論として作る（§5、§6）。ここまでが一般論である。そこに論文の状況（有限拡大のランク、Galois 群、降下の引用、\(\lambda\)-平坦性・\(\lambda\)-CM 性）を入れて論文の命題を導き（§7）、具体的な長さ付き代数（§8）を経て核の場合を示す（§9）。

<!-- source: exposition/ja/exposition-ja.tex:200–212; block: paper-ja-L200 -->
<a id="paper-ja-L200"></a>

| 共通の道具（§3） | 実現（§5 / §6） | 論文の状況（§7） | 核の場合（§9） |
| --- | --- | --- | --- |
| Euler 評価 | 系 5.7 / 系 6.5 |  |  |
| 共役和の比較 | 定理 5.9 / 定理 6.9 | 命題 7.5（Lemma 3.5c） / 定理 7.9（Thm 4.7） | 補題 9.2（置き換え 1） / 命題 9.5（置き換え 2） |
| 反復錐による消滅 | 補題 5.10、5.14 / 補題 6.11 | 命題 7.10（Lemma 5.3） | 補題 9.3 |
| 第零次の下界 | 補題 5.11 / 補題 6.12 | 命題 7.11（Lemma 5.6） | 補題 9.6 |
