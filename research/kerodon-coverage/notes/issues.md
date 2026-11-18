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
- t-03 `def-path-category` の \(P_{ij}\) は「包含」で順序づける。既存 review/ch2.csv の2.4.3.5は、Lean の包含順と Kerodon の逆包含との規約差を記録する。したがってこの文章を Kerodon の定義そのものの写しとしてラベル付けしたり、既存 partial 判定を変更したりしない。NB-W2 で 2.4.3.1 の原稿へ移した。
- t-05「可縮」は境界の全充填（終射が trivial Kan）という強い意味で、単体的集合の弱可縮性一般の言い換えではない。1.5.5.8に対応させ、旧見出しの語はそのまま残した。
- 旧解説番号「定義1.3」と Kerodon の Example 1.1.0.9 は番号も種類も違う。見出しは provenance を示す旧見出しであり、Kerodon の項目種別を上書きしない。

## NB-W2 での配置

- 旧保留 47 ブロックはすべて原稿へ移した。正確な候補が Tag 表にだけある t-03 定理 3.5（2.4.3.7）と t-04 の増大・join の表示（4.3.3.12・4.3.3.19）は、節 2.4.3・4.3.3 に置いた。候補番号の items.csv 行を作る作業は別に残る。
- t-05 の左・右 fibration は Kerodon 4.2.1.1 の同じ定義の両側なので同じファイルで隣接させた。Kan・inner・trivial はそれぞれ別ファイル。README の元ブロック順で元の表の並びを追える。
- t-06 は単体的集合の**厳密な**引き戻しの次数ごとの計算。圏論的・ホモトピー引き戻しの項目には振らず、積の補助説明とファイバーの準備として節に置いた。
- t-10 の評価写像・左右の trivial Kan fibration は、一般の単体的集合の底を許す形である。Kerodon 4.2.5.4 の left anodyne に沿う制限に関係するが、ここは評価射としての説明なので §4.2.5 のつなぎにした。t-11 の straightening は 5.6.0.6 の左 fibration の分類で使う向きの解説で、同値類の全単射全体は述べていない。
- t-09 の極限・余極限、t-15 の米田の同値・充満忠実性は、原文で別の箇条書きなので項目を分けた。「次は同値」のように箇条書き全体を支配する導入と、式の前後で一文をなす段落は分けていない。t-15 の写像空間は 8.3.1.3 の反変側。
- t-14 の小ささの注意には、空の \(C\) では前層圏が終対象になる例外がある。原稿の文言は保存した。t-15 定義 15.1 は元から「（未記入）」だけで、評価射の本文を補っていない。

## NB-W2 の未配置本文

t-15 定義 15.1 は見出しだけではどの評価射を定義するか確定しない。本文は元の未記入表示を保持した。

## 定義 15.1 （評価写像）

<!-- source: exposition/ja/infinity/t-15-yoneda.html:28; block: t15-def-yoneda-evaluation-functor-1 -->
<a id="t15-def-yoneda-evaluation-functor-1"></a>

（未記入）

## NB-W3 の保留と転記上の所見

- `03-straightening.html` §3 と `unstraightening.html` §7 は、解説の ∞ 圏としての同値を §5.6 に置いた。Kerodon 5.6.0.6 の印刷本文が与えるのは同値類の全単射。解説が典拠として添える番号は原文のまま。
- `02-mapping-limits.html` §5 の三模型の表は、fat join・lax slice・錐の族の対比を一緒に読むため §4.6.2 に置いた。表中に 4.6.4.19 と 4.6.6.8 も残した。
- `f-a-basics.html` §3 の五角形と立方体は凍結ページ内の SVG。Markdown では元図へのリンクと図中のラベルを保持した。図形と矢印はリンク先で確認できる。
- 凍結原稿中の旧ファイル名は表示文言として残した。現チェックアウトにないローカルリンクの表示文言を保持し、リンクだけ外した。既存の対応表は更新していない。
- 変換は静的に確認した。長い表、Lean コードフェンス、SVG へのリンクは Markdown に保持した。Verso 出力は未確認。

### 対応を確定できなかった本文

#### f-01-simplicial-kan.html — 4. 塔と lim¹（Kan）

<!-- source: exposition/ja/infinity/f-01-simplicial-kan.html:184; block: nbw3-f-01-simplicial-kan-l184 -->
<a id="nbw3-f-01-simplicial-kan-l184"></a>

**保留理由**　Kerodon 7.6.5 に逐次極限の一般論はあるが、この塔の lim¹ の定義・全射条件・ exact sequence を一緒に扱う項目番号を確定できない。

- **非可換な lim¹**：群の塔 \(G_n\) と準同型 \(q_n : G_{n+1} \to G_n\) について、\(\prod_n G_n\) に「ねじれた共役」で作用させた軌道の集合（`TowerLimOne.limOne`、KST/Spectra/TowerLimOne.lean:51）。可換群なら、通常の \(\lim^1\) と一致する。

<!-- source: exposition/ja/infinity/f-01-simplicial-kan.html:185; block: nbw3-f-01-simplicial-kan-l185 -->
<a id="nbw3-f-01-simplicial-kan-l185"></a>

**保留理由**　Kerodon 7.6.5 に逐次極限の一般論はあるが、この塔の lim¹ の定義・全射条件・ exact sequence を一緒に扱う項目番号を確定できない。

- **Milnor の完全列**（KST/Spectra/TowerMilnorExactness.lean・TowerGroupLimitComparison.lean）：
\[
1 \to {\lim_n}^1 \pi_{r+2}(X_n) \xrightarrow{\ \delta\ } \pi_{r+1}(\lim_n X_n) \to \lim_n \pi_{r+1}(X_n) \to 1
\]
    右の写像の全射性は `limitGroupComparison_surjective`、\(\delta\) の単射性と「像 = 核」は `limOneBoundary` と `exists_limOneBoundary_iff` による。

<!-- source: exposition/ja/infinity/f-01-simplicial-kan.html:190; block: nbw3-f-01-simplicial-kan-l190 -->
<a id="nbw3-f-01-simplicial-kan-l190"></a>

**保留理由**　Kerodon 7.6.5 に逐次極限の一般論はあるが、この塔の lim¹ の定義・全射条件・ exact sequence を一緒に扱う項目番号を確定できない。

- **Mittag–Leffler**：塔が Mittag–Leffler 条件を満たせば、\(\lim^1\) は自明になり、ホモトピー群は極限と交換する（`subsingleton_of_mittagLeffler`・`limitGroupEquivOfMittagLeffler`）。

#### f-01-simplicial-kan.html — 6. 基本亜群と necklace

<!-- source: exposition/ja/infinity/f-01-simplicial-kan.html:210; block: nbw3-f-01-simplicial-kan-l210 -->
<a id="nbw3-f-01-simplicial-kan-l210"></a>

**保留理由**　基本亜群を necklace で表示する比較を一つの原典項目に確定できない。

- **基本亜群**：単体的集合 \(A\) の基本亜群を、ホモトピー圏の自由亜群として定義する（`simplicialFundamentalGroupoid`、KST/SConstruction/FundamentalGroupoidComparison.lean:21）。
    anodyne 射 \(A \to B\)（\(B\) は Kan）があれば、\(A\) の基本亜群は \(\mathrm{h}B\) と圏同値になる（`fundamentalGroupoidEquivalence`、FundamentalGroupoidEquivalence.lean:50）。これで \(\pi_1\) が自由亜群で表示できる。

<!-- source: exposition/ja/infinity/f-01-simplicial-kan.html:212; block: nbw3-f-01-simplicial-kan-l212 -->
<a id="nbw3-f-01-simplicial-kan-l212"></a>

**保留理由**　基本亜群を necklace で表示する比較を一つの原典項目に確定できない。

- **necklace**（Dugger–Spivak）：単体を頂点で貼り合わせた「数珠」の形の単体的集合。coherent nerve の写像空間を組合せ的に計算するのに使う（KST/SConstruction/Necklace*）。第 3 章以降の coherent nerve の話で再び出てくる。
