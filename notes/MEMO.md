# Serre の交点重複度の正値性（OpenAI math 193）：調査メモ

2026-10-07 作成。原本は Claude Doc（https://claude.ai/code/artifact/d6a6ee1c-2a1d-4a8f-87e5-45a3dcd889d4）。これはその写しで、図は文章に置き換えている。

## 論文と主張

- 論文：Positivity of Serre's Intersection Multiplicity（OpenAI、2026-09-23、31ページ）。[openai/math](https://github.com/openai/math) のファミリー 193。調査時点のコミットは `adc7f1241b42`（2026-10-06）。
- 主張（Theorem 1.1）：(R, m) を正則局所環、M, N を 0 でない有限生成 R 加群とする。length(M ⊗ N) < ∞ かつ dim M + dim N = dim R なら χ^R(M, N) = Σ(−1)ⁱ length Tor_i^R(M, N) > 0。標数・分岐の制限なし。どちらの加群にも不分岐正則局所環への持ち上げを要求しない。
- Lean 形式化：なし（CONTENTS.md にリンクがなく、`lean/formalization.yaml` にも載っていない）。

**既存の到達点**

| 結果 | 内容 |
| --- | --- |
| Serre | 等標数・不分岐（完備 DVR 上の冪級数環を含む）での正値性。対角への帰着 |
| Roberts、Gillet–Soulé | dim M + dim N < dim R での消滅（局所 Chern 指標、Adams 作用素） |
| Gabber | 一般の非負性（alteration と法束上の交点計算） |
| Skalit | 2次元正則局所環上 essentially smooth な場合の正値性 |
| KC–Soto Levins | Serre 持ち上げ条件をみたす加群での正値性 |
| Bhatt–Hochster–Ma | 両方の商整域に lim Cohen–Macaulay 列があれば正値性（条件付きの道筋） |

**優先権**：脚注1に、Editan が 2025-12-09 に Copilot・Gemini と連名で、同じ主張（素イデアル商の形）を公開ポストしていると記録されている。論文は「確立した定理としては扱わない」としている。

**位置づけ**：等標数は Lemma 5.1 で Serre を引用するだけで、別証明はしていない。新しいのは剰余標数 p > 0 の混標数の場合で、不分岐も分岐も一様に扱う。

## 証明の全体像

発想は「両側が Cohen–Macaulay なら高次 Tor が消えて χ = length Tor₀ > 0」という古典的な場面（Hochster の small CM 加群の路線）を、本物の CM 加群なしで実現することです。perfectoid 化（標数 p なら完全化）した巨大代数 C_D は正規化長さ λ の目で CM であり、χ を変えずに D と E をこの「CM もどき」に1つずつ置き換えていきます。

証明の連鎖：

1. χ(M, N)（一般の有限生成加群）
   → 帰着（Lemma 5.1）：Serre（等標数）、Roberts–Gillet–Soulé（消滅）
2. χ(D, E)（D = R/P, E = R/Q：完備局所整域、h + l = d）
   → 置き換え 1：D → C_D（Lemma 5.2）。降下 Thm 3.1 → Lemma 3.5
3. Σ_σ c_σ（C_D と E′ の Euler 特性）
   → 置き換え 2：E′ → C_E（式 5.18）。近似 §5.2–5.4、降下 Thm 3.1 → Thm 4.7
4. Σ_σ Σ_γ b_{σ,γ}（C_D の有限近似と C_E の Euler 特性）
   → 両側が CM もどき（Lemma 5.6）：高次の項が λ の目で消える
5. 各 b_{σ,γ} > 0（0 次の項だけが残り、生成元数で下から評価）

最終的に |G_D| a_D a_E χ(D, E) = (1/|G_E|) Σ_σ Σ_γ b_{σ,γ} > 0 です。既知の定理として使うのは帰着段階の Serre と Roberts–Gillet–Soulé、それに C_D, C_E を作る perfectoid の結果だけです。論文の新しさは、置き換えの各段階で χ が変わらないことを Galois 共役の和と有理 K 理論で保証したところにあります。

## 道具と2つの置き換え

### 帰着（Lemma 5.1）

完備化し、剰余体を代数閉体に拡大する（Lemma 2.1）。素フィルトレーションをとり、Roberts–Gillet–Soulé の消滅で次元の和が d 未満の対を落とす。これで D = R/P、E = R/Q（正次元の完備局所整域、h + l = d、P + Q は m-準素）の場合に帰着される。等標数は Serre を引用する。

### λ の目で CM な代数（§2、Theorem 2.5）

- 正則な正規化基底 A_D ⊂ D をとる。標数 p では k[[t₁,…,t_h]]（Cohen–Gabber）、混標数では W(k)[[t₂,…,t_h]]（Lemma 2.2）。
- p 冪根の塔 Λ = lim A_D[t^{1/pⁿ}] の上で、Faltings 型の正規化長さ λ_∞ を定義する（Lemma 2.3）。
- C_D を、標数 p では D_perf、混標数では (D ⊗ A_∞)_perfd（CLMST の perfectoid 化）とする。
- 性質：正次数のパラメータ Koszul ホモロジーの λ は 0。パラメータ商の λ は Hilbert–Samuel 重複度。標数 p の場合は Monsky（Hilbert–Kunz）と Roberts の Frobenius ホモロジー定理から、混標数の場合は CLMST の Prop. 4.0.4 / 4.0.10 / 4.0.14 から出る。
- 周りの R が混標数でも商 D が標数 p になりうるので、両方の場合が必要になる。

### 比較の原理と有理 K 理論の降下（§3）

- **原理（Lemma 3.4–3.5）**：正則な A 上の有限長加群 V では、λ(V ⊗ C) = r · length V（高次 Tor の λ は 0）と χ(V ⊗ T) = r · length V が成り立つ。よって2つの Euler 特性は A から引き戻した類の上で一致する。
- **Theorem 3.1**：有限全射 Spec T → Spec A で、有限群 G が幾何ファイバーに推移的に作用するとき、K^J(H)_ℚ ≃ (K^J(H ⊗ T)_ℚ)^{hG}（J ∋ p、H は任意の連結な結合的係数代数）。よって G 不変な有理類は A から来る。平坦性も順分岐性も不要。
- **道具**：Land–Tamme の truncating invariant の cdh 降下、有限忠実平坦被覆の Čech 降下、その組み合わせによる有限全射での降下（Lemma 3.2–3.3）。
- **結論（式 3.11）**：Galois 共役の和の上で、通常の Euler 特性と λ の Euler 特性が一致する。λ の G 不変性は不要。

### 置き換え1：D → C_D（§5.1、Lemma 5.2）

D′, E′ を Galois 閉包の整閉包、G_D をその Galois 群とする。R の作用を σ でひねって c_σ = Σ(−1)ⁱ λ_D Tor_i^R(C_D, E′) とおくと、Lemma 3.5 により |G_D| a_D a_E χ(D, E) = Σ_σ c_σ。

### 置き換え2：E′ → C_E（§4、§5.2–5.5）

- **パラメータ商（Lemma 5.3）**：Q の元で R-正則列かつ D のパラメータ系になる x をとり、B = R/(x)、U = C_D/xC_D とおく。i > l で λ Tor_i^B(U, L) = 0（λ の意味で B 上の射影次元が l 以下）。
- **有限近似（Lemma 5.4）**：共通に m_B^a で消される有限長 B 加群 Mₙ と sₙ = p^{jh} で、length Tor^B(Mₙ, L)/sₙ → λ Tor^B(U, L)。生成元数 β₀(Mₙ)/sₙ の極限も正。
- **切り詰め（Lemma 5.5）**：Mₙ の極小自由分解を l 次で切って E′ に持っていった列 F′ₙ は、ランク無視の圏の中で閉点に台をもち、通常の Euler 評価が c_σ になる。
- **ランク無視の圏（§4）**：ランク O(sₙ) の自由列の圏を、ランク o(sₙ) の列で割った Verdier 商の冪等完備化。長さは sₙ で割って超フィルター極限をとる。商をとった後にだけ台をもつ対象や、冪等元の像にも長さを定義する（Lemma 4.2、Prop. 4.3、4.5）。
- **K 理論への接続（Lemma 4.6）**：この圏は ∏ M_{sₙ}(A) から作った連結な dg 代数 H 上の Perf と同値。これで Theorem 3.1 を係数 H で適用でき、Theorem 4.7（漸近ノルム比較）が出る。
- **結論（式 5.18）**：|G_E| c_σ = Σ_γ b_{σ,γ}。

### 正値性（Lemma 5.6）

C_E 側も λ の目で CM なので、評価は 0 次の項 b₀ だけになる。0 次ホモロジーは (C_E/m C_E)^{β₀(Mₙ)} に全射し、b_{σ,γ} ≥ λ_D(U)/length(B/m_B^a) · r_E/t_E > 0。

| | 置き換え1 | 置き換え2 |
| --- | --- | --- |
| 置き換え | D → C_D | E′ → C_E |
| 対象 | 普通の有限自由複体 | 有限近似 Mₙ の切り詰めた分解の列 |
| 比較の命題 | Lemma 3.5 | Theorem 4.7 |
| 降下の入力 | Theorem 3.1（係数 A） | Theorem 3.1（係数 dg 代数 H） |
| 使う場所 | Lemma 5.2 | Lemma 5.5、式 (5.18) |

## 系

- **記号的冪（Kurano–Roberts 経由）**：分岐する混標数の正則局所環で、√(P + Q) = m かつ ht P + ht Q = dim R なら、r ≥ 1 で P ∩ Q^{(r)} ⊆ m^{r+1}。Kurano–Roberts の「正値性から記号的冪へ」の定理を適用しただけ。
- **Corollary 1.2（strict transform の交点）**：A/(P + Q) が有限長で次元が相補的、T = gr(A/P) ⊗ gr(A/Q) の次元が 1 以下なら χ_A(A/P, A/Q) ≥ e(A/P) e(A/Q)。等号は dim T = 0 のときに限る。Skalit の爆発公式に正値性を入れたもので、Dutta の下界の問題と関係する。

## 検証の重点

論文が新しく主張している一般定理（Theorem 3.1 と §4）が要です。§5 は短く初等的で、通読した範囲では問題は見つかっていません。

- [ ] Theorem 3.1、特に Lemma 3.2–3.3：台つき有理 K 理論の有限忠実平坦降下と、有限全射への拡張。Frobenius 型の非エタールな被覆まで通るか。J ∋ p で台をつけて有理化すると truncating になる、という点の確認。
- [ ] §4：商をとった後にだけ台をもつ対象や冪等元の像の上で、長さが well-defined か（Lemma 4.2、Prop. 4.3、4.5）。Lemma 4.6 の dg 商の扱い。
- [ ] Theorem 2.5 の混標数部分：CLMST の Prop. 4.0.4 / 4.0.10 / 4.0.14 の仮定との照合。
- [ ] 引用の照合：Land–Tamme の主張、Skalit の補題（Corollary 1.2）、Kurano–Roberts。
- [ ] Editan の公開ポスト（2025-12-09）の内容と、Bhatt–Hochster–Ma の路線との比較。

## 形式化の方針とプロジェクト構成

### 3層の切り分け

| 層 | 中身 | 扱い |
| --- | --- | --- |
| 1. 論文固有の議論 | §5 全体、Lemma 3.4/3.5 の形式的部分 | sorry なしで形式化する第一目標 |
| 2. 論文の新しい一般定理 | Theorem 3.1、Theorem 4.7（§4） | 当面は名前つき axiom。人手の検証を最優先 |
| 3. 文献からの入力 | Serre、Roberts–Gillet–Soulé、Cohen–Gabber、Monsky、Roberts、CLMST、Land–Tamme、Bhatt–Scholze | `class` と `axiom` インスタンスで置く |

第一マイルストーンは、主定理が層 2・3 の名前つき仮定だけから sorry なしで出る状態です。`#print axioms` に出るのが名前つき仮定だけになれば、論文の骨格の機械検証になります。そのあと、Lemma 3.4 系、標数 p の Theorem 2.5、§4 の圏論的部分の順に仮定を外していきます。

### Mathlib の現状（2026-10-07、mathlib `e6bbacd0`）

| 状況 | 項目 |
| --- | --- |
| ある | 正則局所環 `IsRegularLocalRing`（極大イデアルの生成元数 = Krull 次元）、`Module.supportDim`、`ringKrullDim`、`Module.length`（ℕ∞ 値）、Ext と射影次元、正則列、Noether 正規化、完備化、`Perfection`、perfectoid の初歩（untilt、Fontaine θ）、三角圏とその局所化、導来圏、スペクトル系列 |
| ある程度 | Tor：`CategoryTheory.Tor C n`（モノイド的アーベル圏の第2成分の左導来関手）。API はほぼなく、第1成分で導来した `Tor'` との同型も未証明。`HomologicalComplex.eulerChar` は finrank ベースで、長さではない |
| ない | Koszul 複体、パラメータ系、Hilbert–Samuel 重複度、Cohen–Macaulay 環、極小自由分解、Cohen の構造定理、優秀環、長さで測る Euler 特性、Serre の交点重複度、代数的 K 理論、perfectoid 化と almost 数学、正規化長さ |

主張は、`Tor (ModuleCat R) i` の対象を R 加群として見て `Module.length` をとり、χ を i ≤ dim R の有限和として自前で定義すれば書ける。証明では Koszul 複体と極小自由分解が §5 の随所で必要になり、そこが最初の大きな基盤整備になる。

### 置き場所

- **リポジトリ**：公開前提の独立リポジトリ [unaoya/SerrePositivity](https://github.com/unaoya/SerrePositivity)。既存の `arxiv_formalization` の仕組みは使わない（2026-10-07 決定）。
- **元論文**：openai/math はフォークせず、`paper/` に PDF と取得元（コミット `adc7f1241b42`）を記録する（`paper/SOURCE.md`）。
- **ノート**：`notes/INVESTIGATION.md`（要約、検証チェックリスト、Mathlib の現状）と、この調査メモの写し `notes/MEMO.md`。
- **作業**：以降の形式化は Claude Code で進める。
