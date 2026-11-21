# EN-W1　豊穣化の一般論：文献との対応と、それに基づく計画

2026-11-21。調整役が、四つの文献の本文（`~/serre-evidence/references/`、Git の外）を読んで作った。番号と主張は本文から読み出したもので、記憶で書いたものは無い。決定の正本は [enrichment-w1.md](enrichment-w1.md)。この紙は、実装（段 3 以降）で「どの宣言が文献のどれに当たるか」を引くための対応表と、文献を読んで計画を直した所の記録。

## 0. 文献と略号

| 略号 | 文献 | 使う範囲 |
| --- | --- | --- |
| R | E. Riehl, *Categorical Homotopy Theory*, Cambridge University Press, 2014 | 第 3 章（§3.3〜§3.7）、§10.1。定理の主張の基準 |
| H | M. Hovey, *Model Categories*, AMS Mathematical Surveys and Monographs 63, 1999 | 第 4 章（§4.1、§4.2）。加群の定義（整合つき）と、モデル構造との両立の基準 |
| K | G. M. Kelly, *Basic Concepts of Enriched Category Theory*, Reprints in TAC 10, 2005 | 第 1 章〜第 3 章。豊穣圏どうしの構成（C-軽）の基準 |
| HS | M. Hovey, "Spectra and symmetric spectra in general model categories", arXiv:math/0004051v3 | §6、§7。対称スペクトルへの適用（段 4）の基準 |

Lean の docstring では、本体の規約（`@[cite KEY "番号"]` と略号表）で引く。略号表への登録は段 3a で行う。

## 1. 文献と Lean の間の、書き方の違い

実装の前に揃えておく。ここを曖昧にすると、主張が文献と左右逆になる。

| 事柄 | R・K | H・HS | Mathlib | 本体の決め方 |
| --- | --- | --- | --- | --- |
| 合成の順 | M(y, z) ⊗ M(x, y) → M(x, z)（R (3.4.6)、K §1.2） | 同左 | `eComp X Y Z : (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z)`（図式の順） | Mathlib の順。文献の順との行き来は組紐で行う（本体の `ReverseComposition`。段 3a で `BaseChange` に置く）。docstring には文献の式を、順が逆であることを断って書く |
| 作用の向き | 左：v ⊗ m（R Definition 3.7.2、10.1.3） | 右：X ⊗ K（H Definition 4.1.6 は右 C 加群。「左加群も定義できる」と断っている） | `MonoidalLeftAction`（左）。右は `MonoidalRightAction` | 左（R と Mathlib の左作用）。H を引くときは、左右を読み替えていることを docstring に書く。V は対称なので数学として同値 |
| 対称スペクトルの加群の向き | — | HS Definition 6.2 は右加群（Xₙ ⊗ K → Xₙ₊₁）。「[HSS] は左加群」と断っている | `Mod` は左加群 | 段 4 の設計で決める（§6 の未決 1） |
| 基底の圏への仮定 | 閉対称モノイダル圏 (V, ×, ∗)（記号は直積だが一般の対称モノイダル） | 閉対称モノイダル圏 | `MonoidalCategory`・`SymmetricCategory`・`MonoidalClosed` | 主張ごとに要る分だけ仮定する（対称性が要るのは、合成の順の行き来、反対圏、V 圏のテンソル）。文献より弱い仮定で示せるときは弱くし、その旨を書く |
| 通常の圏 | 豊穣圏から取り出す：C₀(x, y) := V(∗, C(x, y))（R Definition 3.4.5、K §1.3） | — | `ForgetEnrichment`。もとから圏があるときは `EnrichedOrdinaryCategory`（同値 `eHomEquiv` を持つ） | 決定 2：もとから圏である M は `EnrichedOrdinaryCategory` |
| テンソルの定義 | V の中の同型 M(v ⊗ m, n) ≅ V(v, M(m, n))（R Definition 3.7.2、K (3.42) の双対） | 加群＋二変数の随伴（H Definition 4.1.6、4.1.12） | 無い | 決定 2′（§3）：加群の側を基準の構造にし、V の中の同型を構成する |
| 整合の条件 | R Definition 10.1.3 は結合・単位の同型を「自然な同型」とだけ書き、整合を要求しない | H Definition 4.1.6 は三つの整合の図式（四重の結合、単位二つ）を要求 | `MonoidalLeftAction` は五角形と単位の整合を持つ | H に従う（整合つき）。R の定義は、そのままでは豊穣圏の結合律を示すのに足りない恐れがある |

## 2. 対応表

「Lean」の欄：**M**＝Mathlib にある（名前は ⑧ がソースで確かめたもの）、**本**＝本体にある、**書**＝新しく書く（ファイルは決定 5）、**要確認**＝Mathlib にあるかを段 2 の改訂で確かめる。

### 2.1 Riehl 第 3 章

| 番号 | 内容 | 一般論 | Lean |
| --- | --- | --- | --- |
| Definition 3.3.1 | V 圏 | 土台 | M `EnrichedCategory` |
| Definition 3.3.6、(3.3.7) | 閉モノイダル圏 | 土台 | M `MonoidalClosed` |
| Remark 3.3.9 | (3.3.7) は V の中の同型に持ち上がる | A1 の部品 | M（`MonoidalClosed` の内部 Hom の随伴。要確認） |
| Construction 3.3.14 | 基点付きの対象の圏の閉モノイダル構造（スマッシュ積） | 試験の例の前提 | 本 `Spectra/Pointed/` |
| Definition 3.4.1 | 緩いモノイダル関手 | 土台 | M `Functor.LaxMonoidal` |
| Lemma 3.4.3 | 基底の取り替え | A2 | M `TransportEnrichment`。本 `Transport`（元の対象の型に載せる版） |
| (3.4.4) の後の注意 | 取り替えると通常の圏が変わりうる（(3.4.4) が全単射なら変わらない） | A2 | M `TransportEnrichment.enrichedOrdinaryCategory`（単位からの射の全単射を要求）。同じ条件 |
| Definition 3.4.5 | 通常の圏 C₀ | 土台 | M `ForgetEnrichment`、`EnrichedOrdinaryCategory` |
| Lemma 3.4.9 | 閉対称モノイダル圏の、自己豊穣化の通常の圏はもとの圏 | A1 | M `enrichedOrdinaryCategorySelf` |
| Definition 3.5.1 | V 関手 | 土台 | M `EnrichedFunctor` |
| Example 3.5.4 | 表現可能な V 関手 | C-軽 | 書 `Representable`（M に一部。K §1.6） |
| Definition 3.5.8 | V 自然変換 | B6 の土台 | 要確認 |
| Proposition 3.5.10 | 通常の圏を取る操作は 2 関手 | 土台 | 要確認 |
| Lemma 3.5.12 | 同型の判定（表現可能関手が同型なら対象が同型。通常・V 値・V 関手のどの意味でも同じ） | B1・B2 の証明の道具 | M の米田（`Yoneda`・`Coyoneda` の忠実充満性）。**R の証明はすべてこれで同型を作る。§5 の証明の方針** |
| Definition 3.5.14 | V 随伴 | B6 | 書（要確認） |
| Definition 3.7.2 | テンソルを持つ：M(v ⊗ m, n) ≅ V(v, M(m, n)) | 基準の構造の豊穣圏の側 | 本 `EnrichedRepresentability` の `tensorIso` |
| Definition 3.7.3 | 余テンソルを持つ：M(m, nᵛ) ≅ V(v, M(m, n)) | 同上 | 本 `EnrichedRepresentability` の `cotensorIso` |
| Remark 3.7.4 | テンソル・余テンソル・Hom は二変数の V 随伴をなす | B1 の出力 | 書 `TensorCotensor` |
| Example 3.7.5 | 閉対称モノイダル圏は自分自身の上でテンソルと余テンソルを持つ | A1 の続き。B2 の出発点 | 書 `TensorCotensor`（自己作用 M `selfLeftAction` から） |
| Lemma 3.7.7 | テンソルを持つ V 圏では、∗ ⊗ m ≅ m、(v × w) ⊗ m ≅ v ⊗ (w ⊗ m) | B5（逆向き）。決定：書かない | — |
| Proposition 3.7.10 | テンソルと余テンソルを持つ V 圏の間の随伴 F ⊣ G について、V 随伴であること／F が V 関手で F(v ⊗ m) ≅ v ⊗ Fm／G が V 関手で G(nᵛ) ≅ (Gn)ᵛ、は互いに他を定める | B6 | 書 `Comparison` か新しいファイル（段 2 の改訂で決める） |
| Theorem 3.7.11 | 閉対称モノイダル圏の間の随伴 F : V ⇄ U : G で F が強モノイダルなら、**U でテンソルと余テンソルを持つ任意の豊穣圏 M** は、V で豊穣化されテンソルと余テンソルを持つ。v ⋆ m := Fv ⊗ m、{v, m} := m^{Fv}、M_V(m, n) := G M_U(m, n) | B2 | 書 `MonoidalAdjunction`。G が緩いモノイダルになることは M `Adjunction.rightAdjointLaxMonoidal` |
| Corollary 3.7.12 | F ⊣ G は、U に誘導された V 圏の構造について V 随伴 | B6 | 書 |
| Example 3.7.13 | (−)₊ : sSet ⇄ sSet∗ : U により、基点付き単体集合は単体集合で豊穣化され、K ⊗ X = K₊ ∧ X、余テンソル Y^K = sSet∗(K₊, Y)。写像空間は内部 Hom の基点を忘れたもの | 段 3d の試験 | 本 `PointedEnrichment.simplicialCategory`（いまは基底の取り替え。102 回置き直されている） |

### 2.2 Riehl §10.1

| 番号 | 内容 | 一般論 | Lean |
| --- | --- | --- | --- |
| (10.1.1) | 二変数の随伴 | 土台 | M `ParametrizedAdjunction`（片側ずつ。二つ組にする） |
| Remark 10.1.2 | 二変数の随伴が V の中の同型に持ち上がることは仮定しない。加群の構造の整合から従う | 決定 2′ の根拠 | — |
| Definition 10.1.3 | 閉じた V 加群：二変数の随伴 (⊗, {}, hom)、結合の同型 v ⊗ (w ⊗ m) ≅ (v × w) ⊗ m、単位の同型 ∗ ⊗ m ≅ m | **基準の構造** | 書 `OfAction`（M `MonoidalLeftAction` と二つの `ParametrizedAdjunction`。整合は H 4.1.6 に従う） |
| Proposition 10.1.4 | 閉じた V 加群は、与えた二変数の随伴がテンソル・余テンソル・Hom の随伴の下にあるような仕方で、**一意に**、テンソルと余テンソルを持つ V 圏になる。証明は演習 | A3・B1・B3 | 書 `OfAction`（豊穣圏を作る）、`TensorCotensor`（V の中の同型を構成する）。一意性は B4 で使う |
| Proposition 10.1.5 | 閉じた V 加群の間の関手 F について、V 関手であること／結合的で単位的な比較 v ⊗ Fm → F(v ⊗ m) を持つこと、は同値 | B6 | 書 |
| Remark 10.1.6 | 双対に、余テンソルの側の加群の構造でも書ける | 余テンソルの側 | B6 の中で必要な分だけ |

### 2.3 Hovey 第 4 章

| 番号 | 内容 | 一般論 | Lean |
| --- | --- | --- | --- |
| Definition 4.1.1〜4.1.5 | モノイダル圏、モノイダル関手、対称モノイダル | 土台 | M |
| Definition 4.1.6 | （右）C 加群：⊗ : D × C → D、結合 a、単位 r、三つの整合の図式 | 基準の構造の「作用」の部分 | M `MonoidalLeftAction`（左右を読み替える） |
| Definition 4.1.7 | C 加群の関手：F と自然な同型 FX ⊗ K → F(X ⊗ K)、二つの整合。加群の自然変換 | B6 | M（作用と両立する関手。`Monoidal/Action/LinearFunctor`。要確認） |
| Definition 4.1.8 | C 代数（C からの関手を持つモノイダル圏） | B2 の言い換え | — |
| Definition 4.1.12 | 二変数の随伴 (⊗, Hom_r, Hom_ℓ, φ_r, φ_ℓ) | 土台 | M `ParametrizedAdjunction` を二つ |
| Definition 4.1.13 | 閉モノイダル構造 | 土台 | M `MonoidalClosed` |
| Definition 4.1.14 | 閉モノイダル関手＝モノイダル関手であって随伴の左 | B2 の入力 | M `Functor.Monoidal`＋`Adjunction`（＋`Adjunction.IsMonoidal`） |
| §4.1 の末尾 | 閉じた加群、閉じた代数。加群の 2 圏の上の双対（余テンソルの側） | 基準の構造、B6 | 書 |
| Definition 4.2.1、Lemma 4.2.2 | Quillen の二変数の随伴（押し出し積）と、その三つの同値な言い方 | 使う側 | 本 `HomotopicalAlgebra/Enriched/TensorCotensor.lean`（`tensor_iff_cotensor_model`、`tensor_iff_mapping_model`） |
| Definition 4.2.6 | モノイダルモデル圏 | 使う側 | 本 |
| Corollary 4.2.10 | 基点付き単体集合は対称モノイダルモデル圏 | 使う側 | 本 |
| Definition 4.2.16 | モノイダル Quillen 随伴 | 使う側（段 4 の F₀） | 本（要確認） |
| Definition 4.2.18 | C モデル圏＝**C 加群**であって、作用が Quillen の二変数関手、単位の条件。sSet モデル圏＝単体的モデル圏。C-Quillen 関手＝加群の関手でもある Quillen 関手 | **使う側が受け取る構造** | 本（いまは結合を持たない `TensorCotensor` を受け取っている。決定 2′ で直す） |

### 2.4 Kelly（C-軽）

| 節 | 内容 | 一般論 | Lean |
| --- | --- | --- | --- |
| §1.2 | V 圏、V 関手、V 自然変換。充満部分圏 | 土台、`FullSubcategory` | M（充満部分圏は通常の圏つきの版がある）。書（通常の圏を指定しない版） |
| §1.3 | 通常の圏を取る 2 関手 | 土台 | M |
| §1.4 | V が対称のときの、V 圏のテンソル A ⊗ B と反対圏 | `Product`、反対圏 | 書 `Product`。反対圏は M `Enriched/Opposite` |
| §1.6 | V を V 圏と見る。表現可能な V 関手 | A1、`Representable` | M（自己豊穣化）。書 |
| §1.10 | 表現可能性。受け身の変数についての V 関手 | `Representable` | 書 |
| §1.11 | V 圏の随伴と同値 | B6 | 書 |
| §2.1 | V の中の end | `FunctorCategory` の前提 | M（`Enriched/FunctorCategory` が end を使う。要確認） |
| §2.2 | 関手の圏 [A, B]（**A が小さいとき**）と評価 | `FunctorCategory` | M（通常の関手圏の版）。書（豊穣関手の版） |
| §2.3 | [A ⊗ B, C] ≅ [A, [B, C]] | `Product` と `FunctorCategory` の関係 | 段 5 で要るかを決める |
| §2.6、§3.11、§3.12 | 宇宙を広げて、大きい A についても [A, B] を扱う | `FunctorCategory` の大きさの扱い | 段 5 の設計で、本体の dg 関手の圏（`dgFunctorHom`。全対象についての積）がどの仮定で書かれているかと照らす |
| §3.5 | 充満部分圏と極限 | — | 今回は要らない |
| §3.7 | テンソルと余テンソル（(3.42) 以下）。定義は V 自然な同型 | 基準の構造の豊穣圏の側 | 本 `EnrichedRepresentability` |
| §1.9、§2.4 | 米田 | 保留 | — |

### 2.5 Hovey の論文（段 4）

| 番号 | 内容 | 本体 |
| --- | --- | --- |
| Definition 6.1 | 対称列の圏 C^Σ、畳み込み | `Spectra/SymmetricSequence/` |
| Definition 6.2 | D：対称モノイダル（モデル）圏、C：D（モデル）圏、K ∈ D。Sp^Σ(C, K)＝C^Σ の中の、D^Σ の可換モノイド Sym(K) 上の加群。右加群。Sp^Σ(D, K) は双完備な閉対称モノイダル圏（単位は Sym(K)）。Sp^Σ(C, K) は Sp^Σ(D, K) の上で豊穣化され、テンソルと余テンソルを持つ | `GeneralSymmetricSpectrum C K`。**C＝D の場合だけ。左加群** |
| Definition 6.3 | Evₙ とその左随伴 Fₙ X = F̃ₙ X ⊗ Sym(K)。F₀ X = (X, X ⊗ K, …)。Fₙ X ∧ Fₘ Y ≅ Fₙ₊ₘ(X ⊗ Y)。F₀ : D → Sp^Σ(D, K) は対称モノイダル | `evaluation`、`freeAt`、`tensorFreeAtSum`。F₀ の強モノイダル構造は組み立てが要る（段 2 の報告） |
| Theorem 7.3 | 射影モデル構造で、Sp^Σ(D, K) は対称モノイダルモデル圏、Sp^Σ(C, K) は Sp^Σ(D, K) モデル圏 | `Spectra/ModelCategory/` |
| Theorem 7.11 の後の注意 | F₀ が対称モノイダルな Quillen 関手なので、Sp^Σ(C, K) は D モデル圏でもある | **決定 4 の道。R Theorem 3.7.11 を M = Sp^Σ(C, K)、U = Sp^Σ(D, K)、V = D で使う形** |

## 3. 文献を読んで直した決定（11-21、ユーザー承認）

### 決定 2′：基準の構造は「閉じた V 加群」

決定 2 と、その最初の修正を、次で置き換える。

- **基準の構造**は、R Definition 10.1.3 の閉じた V 加群（二変数の随伴＋テンソルの結合の同型＋単位の同型）。整合の条件は H Definition 4.1.6 に従い、Lean では Mathlib の `MonoidalLeftAction V M` と、作用の関手 H についての二つの二変数の随伴（H ⊣₂ 余テンソル、H.flip ⊣₂ 写像対象）で表す。作る側はこれを出し、使う側（H Definition 4.2.18 の C モデル圏）はこれを受け取る。
- **豊穣圏の側の定義**（R Definition 3.7.2・3.7.3、K §3.7。V の中の同型）は、本体の `EnrichedRepresentability` として残し、その値は閉じた V 加群から一般論の定義として一度だけ構成する（R Proposition 10.1.4。同型そのものを返す定義。存在の主張にしない）。
- 本体の `TensorCotensor`（二つの二変数の随伴だけ）は、文献のどちらの定義よりも弱い。これ単独を受け取っている使う側は、閉じた V 加群を受け取る形に直す。`TensorCotensor` を「閉じた V 加群の、随伴の部分」として残すか、閉じた V 加群の構造に吸収するかは、段 2 の改訂で、使う側の書き換えの量を見て決める。
- もとから圏である M の豊穣化は `EnrichedOrdinaryCategory`、写像対象が定義である豊穣圏は `EnrichedCategory`、二つの行き来は Mathlib のものだけ（決定 2 のまま）。

### 決定 3′：一般論として持つもの

決定 3 に、次の二点を加える。ほかは決定 3 のまま。

- **B2 は文献の一般の形で書く**（R Theorem 3.7.11）：閉対称モノイダル圏の間の随伴 F : V ⇄ U : G で F が強モノイダルのとき、**閉じた U 加群である任意の M** が閉じた V 加群になる（v ⋆ m := Fv ⊗ m、{v, m} := m^{Fv}、M_V(m, n) := G M_U(m, n)）。U 自身の場合（R Example 3.7.5 と合わせる）は、その特別な場合として出す。
- **B6 を足す**：関手と随伴が豊穣化と両立すること。
  - 閉じた V 加群の間の関手が V 関手であることと、テンソルとの整合的な比較 v ⊗ Fm → F(v ⊗ m) を持つことの対応（R Proposition 10.1.5、H Definition 4.1.7）。
  - 随伴が V 随伴であることの判定（R Proposition 3.7.10）。
  - 強モノイダルな随伴 F ⊣ G 自身が V 随伴であること（R Corollary 3.7.12）。
  対称スペクトルの「写像対象と豊穣化」のうち、写像対象の自然性、懸垂とループの随伴との両立、Fₙ ⊣ Evₙ との両立は、これの適用にする。

### 決定 7′：文献の使い分け

- 定理の主張は R（第 3 章、§10.1）。
- 加群（作用）の定義と整合は H §4.1（R Definition 10.1.3 は整合を省いているので、定義としては使わない）。モデル構造との両立は H §4.2。
- 豊穣圏どうしの構成は K。
- 対称スペクトルは HS。

## 4. 一般論の一覧（直した後）

| 番号 | 内容 | 文献 | Lean | ファイル |
| --- | --- | --- | --- | --- |
| A1 | 自己豊穣化。閉対称モノイダル圏は自分自身の上の閉じた加群 | R Lemma 3.4.9、Example 3.7.5、K §1.6 | M。閉じた加群としての形は書 | `TensorCotensor` |
| A2 | 基底の取り替え。通常の圏を保つ条件 | R Lemma 3.4.3 | M。本の補足を整理 | `BaseChange` |
| A3 | 閉じた V 加群から、通常の圏つきの豊穣圏を作る | R Proposition 10.1.4 の前半 | 書（本の `RepresentedMapping` を、入口を Mathlib の作用にして整理） | `OfAction` |
| B1 | 閉じた V 加群から、V の中の同型（`EnrichedRepresentability`）を構成する | R Proposition 10.1.4 の後半、Remark 3.7.4 | 書 | `TensorCotensor` |
| B2 | 強モノイダルな左随伴による、閉じた加群の基底の取り替え（任意の閉じた U 加群 M について） | R Theorem 3.7.11、H Definition 4.1.14、HS Theorem 7.11 の後の注意 | 書 | `MonoidalAdjunction` |
| B3 | A3 で作った豊穣圏が、もとの加群のテンソルと余テンソルを持つこと | R Proposition 10.1.4 | 書 | `OfAction` |
| B4 | B2 で作った豊穣圏（G を写像対象に当てたもの）と、取り替えた加群から A3 で作った豊穣圏の一致 | R Theorem 3.7.11 の証明の定義と、Proposition 10.1.4 の一意性 | 書 | `Comparison` |
| B5 | テンソルを持つ豊穣圏から作用を復元する | R Lemma 3.7.7 | 書かない | — |
| B6 | 関手と随伴が豊穣化と両立すること | R Proposition 3.7.10、10.1.5、Corollary 3.7.12、H Definition 4.1.7 | 書 | 段 2 の改訂で決める |
| C-軽 | 充満部分圏、対（テンソル）と挿入、関手の圏と評価、表現可能な Hom | K §1.2、§1.4、§2.2、§1.6・§1.10 | 書（M に一部） | `FullSubcategory`・`Product`・`FunctorCategory`・`Representable` |
| C-重、米田 | 双加群の合成、米田 | K §2.4 ほか | 保留 | — |

## 5. 証明の方針（文献から）

R の証明は、どれも同じ形をしている：二つの対象が同じ関手 V^op → Set を表現することを、随伴と結合の同型をつないだ自然な全単射の列で示し、Lemma 3.5.12（米田）で同型を得る。例（Theorem 3.7.11 の証明）：

    V(x, M_V(v ⋆ m, n)) = V(x, G M_U(Fv ⊗ m, n)) ≅ U(Fx, M_U(Fv ⊗ m, n)) ≅ M(Fx ⊗ (Fv ⊗ m), n)
      ≅ M((Fx × Fv) ⊗ m, n) ≅ U(Fx × Fv, M_U(m, n)) ≅ U(F(x × v), M_U(m, n))
      ≅ V(x × v, G M_U(m, n)) ≅ V(x, V(v, G M_U(m, n))) = V(x, V(v, M_V(m, n)))

Lean でも同じ形で書く：全単射の列を `Equiv` の合成として定義し、x についての自然性を示して、米田から同型を取り出す。こうすると、同型は具体的な定義になり（存在の主張にならない）、その性質（係数についての自然性、単位での一致）は、列の各段の自然性から従う。段ごとの全単射に名前を付け、docstring に R の式を書く。

注意する点：
- R は Proposition 10.1.4 と 3.7.10 の証明を演習にしている。本体で書く。
- R の全単射の列は、結合の同型を一回使う。豊穣圏の結合律（A3）を示すときには、作用の五角形が要るはず。R の定義は五角形を要求していないので、ここは H の定義（整合つき）で示す。⑧ の段 2 の型の案の `TensorAssociativity`（五角形なし）で B1 の欄が全部示せるかは、段 3b の最初に確かめる。示せない欄があれば、入力を `MonoidalLeftAction` に替える。
- 合成の順が文献と逆なので、列の途中で組紐が入る。どこで入るかを docstring に書く。

## 6. 未決（段 4 の設計で相談する）

1. **対称スペクトルの加群の向き**：本体は左加群（[HSS] の向き）。HS は右加群。原典どおりの方針に照らして、どちらに揃えるか。
2. **C と D を分けるか**：HS は、D が対称モノイダル圏、C が D の上の加群、という二つの圏で書く。本体は C＝D だけ。「文献に忠実に、一般性も」の方針に照らして、二つに分けた形にするか。B2 を一般の形（任意の閉じた U 加群 M）で書くので、分けた場合も一般論はそのまま当てはまる。
3. **関手の圏の大きさ**：K §2.2 は A が小さいことを仮定し、大きい場合は宇宙を広げる。本体の dg 関手の圏の書き方と照らす（段 5 の設計）。

## 7. 段の順番（直した後）

| 段 | 内容 | 状態 |
| --- | --- | --- |
| 1 | 全体の調査 | 済（cdaac1a39） |
| 2 | 設計（型の一覧） | 済（4bfe03a3f）。**下の 2b で改訂する** |
| 2b | **設計の改訂**：決定 2′・3′ に合わせて型の一覧を直す。この紙の対応表の「要確認」を Mathlib のソースで埋める。各宣言に文献の番号を付ける | 次 |
| 3a | A2、A3、B3。`CategoryTheory/Enriched/` を分け直す。略号の登録 | |
| 3b | B1。最初に、五角形なしで欄が示せるかを確かめる | |
| 3c | B2（一般の形）、B4 | |
| 3d | B6 | |
| 3e | 試験：基点付き単体集合（R Example 3.7.13） | |
| 4 | 対称スペクトル（HS）。先に未決 1・2 を相談 | |
| 5 | C-軽（K）。先に未決 3 を確かめる | |
| 6 | dg から単体的圏への移行 | |
| 7 | 残りの直接の構成 | |

段 3 と、⑧ の枝の main への取り込みは、⑦（監査）の区切りを待ってから行う。段 2b は Lean を変えないので、先に進めてよい。
