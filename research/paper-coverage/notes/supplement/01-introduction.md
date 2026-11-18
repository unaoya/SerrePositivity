# はじめに

<!-- NB-W4: 凍結解説から転記。 -->

<!-- source: exposition/ja/exposition-ja.tex:55–59; block: paper-ja-L55 -->
<a id="paper-ja-L55"></a>

この文書は、プレプリント *Positivity of Serre's Intersection Multiplicity*
（OpenAI、2026-09-23。[openai/math](https://github.com/openai/math) のファミリー 193、コミット `adc7f124`）
の証明を、Lean 4 による形式化
[unaoya/SerrePositivity](https://github.com/unaoya/SerrePositivity)
で得た理解に基づいて整理し直した解説である。

<!-- source: exposition/ja/exposition-ja.tex:61; block: paper-ja-L61 -->
<a id="paper-ja-L61"></a>

この解説では、証明を次のように整理して述べる。

<!-- source: exposition/ja/exposition-ja.tex:63; block: paper-ja-L63 -->
<a id="paper-ja-L63"></a>

- Euler 評価、反復錐による消滅、第零次の下界、群作用による共役和比較を共通定理としてまとめる（§3）。評価先は長さ付き代数から作る（§4）。

<!-- source: exposition/ja/exposition-ja.tex:64; block: paper-ja-L64 -->
<a id="paper-ja-L64"></a>

- perfect 複体（§5）とランク無視の圏（§6）をその二つの実現とする。各節では具体的な圏と関手を作り、共通定理の仮定を確認して適用する。どちらも一般論であり、論文に固有の仮定を入れて論文の命題を導くのは §7 である。

<!-- source: exposition/ja/exposition-ja.tex:65; block: paper-ja-L65 -->
<a id="paper-ja-L65"></a>

- 長さの有限性、Koszul ホモロジーの消滅、比較に必要な降下を別々の入力とする。\(\lambda\)-平坦性・\(\lambda\)-CM 性（§4）は、それらを供給する十分条件として述べる。

<!-- source: exposition/ja/exposition-ja.tex:66; block: paper-ja-L66 -->
<a id="paper-ja-L66"></a>

- 具体的な代数の構成（§8）と核の場合への適用（§9）は別に述べる。

## 表記

<!-- source: exposition/ja/exposition-ja.tex:70; block: paper-ja-L70 -->
<a id="paper-ja-L70"></a>

命題の番号はこの解説の通し番号で、元論文の番号を括弧で併記する。

<!-- source: exposition/ja/exposition-ja.tex:79; block: paper-ja-L79 -->
<a id="paper-ja-L79"></a>

宣言名は名前空間 `SerrePositivity` を省略して書く。解説の定式化が Lean と異なる箇所は、その場で注意し、付録 A.4 にまとめる。
