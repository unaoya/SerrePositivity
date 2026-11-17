# K 理論の文献地図　停止点 0

対象の Lean は `research/k-maps` の基点 `f34f51cc4`。原典の版と目次は各文献のリンク先に記載した。

| 文献 | 定理・定義など | 式・図式 | 節・付録 | 小項目 | 計 | 引用行（番号つき／全体） | 旧表行 | route 記入行 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [本論文 §3・§4](paper/toc.md) | 13 | 21 | 11 | 17 | 62 | 2,004／2,004 | 29 | 31 |
| [KST](kst/toc.md) | 74 | 48 | 22 | 6 | 150 | 5,637／5,670 | 57 | 88 |
| [Land–Tamme](land-tamme/toc.md) | 88 | 24 | 11 | 9 | 132 | 11／21 | 44 | 75 |
| [Tamme](tamme/toc.md) | 28 | 19 | 3 | 0 | 50 | 133／245 | 12 | 25 |
| [BGT](bgt/toc.md) | 167 | 32 | 47 | 1 | 247 | 67／76 | 19 | 24 |
| 計 | 370 | 144 | 94 | 33 | 641 | 7,852／8,016 | 161 | 243 |

小項目は、旧表が独立に扱う証明段階や、引用を直接結び付けるための節内の項目。題名は内容の短い日本語要約。節の参照をその節内の全項目に配分せず、`§` の行で数えた。式と定理が同じ数字を持つ場合は、式の括弧を保持した。

## 引用索引

[citations.csv](citations.csv) は Git 管理下の Lean ファイル 31,532 本のモジュール文書 `/-! … -/` と宣言の docstring `/-- … -/` を対象とする。通常コメントと入れ子のコメントを除いた。同じファイル・物理行・文献・番号を一件とし、複数行に分かれた引用は番号表記の開始行に置いた。対象 5 文献に対する番号なしの言及は番号欄を空にした。本論文の文献名を省いた番号は `Paper/`、`Inputs/Descent.lean`、`KST/Descent/` の文脈から採った。文献名も番号も書かれていない対応は、この索引からは判定できない。

依頼文の引用対象欄は「六つ」とある一方、全項目の対象は 5 文献なので、索引には旧表の補助 12 文献についても明示的な番号を収録した。Stacks は旧表の 0815 のみ。補助文献の原典照合は段 3 の範囲。抽出規則は [extract_citations.py](extract_citations.py) にあり、リポジトリのルートから次のコマンドで索引を再現できる。

```sh
python3 research/k-coverage/maps/extract_citations.py .
```

補助文献の引用行数は Thomason–Trobaugh 1,341、Drinfeld 384、Stacks 237、Waldhausen 39、Neeman 22、Thomason 2、Balmer–Schlichting と Kuznetsov–Lunts 各 1、Barwick・9 人論文・Schlichting・Goodwillie 各 0。

### 原典番号とのずれ

- KST `§10-7` は [FiniteAffineCover.lean:99](../../../SerrePositivity/KST/DerivedGeometry/FiniteAffineCover.lean#L99) の 1 行。KST 原典の節でなく、[計画書の §10-7](../../../formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md) を指す。
- Land–Tamme `§1.2` は [DGLaxQuotientEnd.lean:11](../../../SerrePositivity/KST/SConstruction/DGLaxQuotientEnd.lean#L11) の 1 行。v3 の §1 に小節番号はない。文脈の ⊙ の構成は §1 の Theorem 1.3 の証明、Definition 1.2 は完全列・局所化不変量の定義。
- 本論文 `3.5a/b/c` の 27 行は Lean 側の分割。原典の Lemma 3.5 の証明に対応する小項目として数えた。別の 65 行は原典 §2 または §5 の実在する番号で、今回の項目表の範囲外。
- Tamme と BGT の番号つき引用はすべて各採録版の項目に解決した。BGT の `(a)` という表記は番号なしの言及に含めた。

## 旧表との対応

[route-crosswalk.csv](route-crosswalk.csv) に [旧表](../items.csv) の対象 161 行の行番号・項目・goal と、新表での対応先を記録した。複数の番号を挙げる行は該当する項目に分け、証明段階だけを指す行は証明段階に結んだ。残り 47 行は補助 12 文献の項目。対応先のない新規項目の `route` は空欄。

- KST 旧表の「Definition 2.1–2.5」のうち、2.2・2.5 は Remark。旧表の「Theorem C・Corollary D」のうち、C は KH の降下、D は最低次数の K 群と cdh コホモロジーの同定。K の cdh 層化と KH の比較は Theorem 6.3 にある。
- Land–Tamme Lemma 3.12 と Lemma B.2 は旧表内に `not_required` と `unknown` の両方があり、`route` は `unknown` とした。対応表に双方の行を残した。
- Tamme の (14) は lax 引き戻しの値の分裂。旧表では `required`。Theorem 18 は切除的正方形に対する降下で、別行の `not_required`。
- BGT v4 の Theorem 9.8 は非連結 K の共表現。§9.3 冒頭が局所化をその帰結として述べ、KST v4 の Theorem 2.10 もその帰結を引用する。BGT v3 で対応する共表現は Theorem 8.9。旧表 [5] の一括行は §9.3 冒頭の帰結に結び、8.7・9.8 の個別行の `not_required` を保存した。
