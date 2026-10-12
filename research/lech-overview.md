# OpenAI「Lech's multiplicity conjecture」：主張と証明の見取り図

> 数学的な解説・調査記録。記載日の仮定・証明方針を保持し、現在のLean実装と未証明状態は [README](../README.md) と解説（`exposition/ja/exposition-ja.tex`）の付録 A を正本とする。

2026-10-10 作成。OpenAI, *Lech's multiplicity conjecture*（openai/math、`preprints/Lechs-multiplicity-conjecture-September-23-2026`、2026-09-23）を節ごとに読み、各主張を正確に書き出した記録。番号は論文のもの。Serre の正値性の論文（以下「Serre の論文」）と同じリポジトリで形式化することを視野に入れ、共有できる部分を最後に整理する。

## 全体の構成

| 節 | 内容 | 依存先 |
| --- | --- | --- |
| §2 | 一般の長さ λ に対する、短い自由複体の一様な評価（Theorem 2.1） | 爆発、射影空間上のベクトル束 |
| §3 | λ の入力となる長さ付き代数の構成（Theorem 3.1） | Faltings・CLMST の正規化長さ |
| §4 | 帰着（Lemma 4.2）と、Cohen 分解による補助環 T と複体 F（Prop 4.3） | Avramov–Foxby–Herzog |
| §5 | 剰余標数 p で源が標数 p の場合（Theorem 5.2）、Dutta 重複度の系（Cor 5.4） | §2、§3、§4、Ma の HK の等式 |
| §6 | 混標数（Theorem 6.3） | §2、§3、§4、Heitmann の Briançon–Skoda |
| §7 | 剰余標数 0（Theorem 7.4） | Theorem 5.2、Artin 近似 |
| §8 | 組み立て（Theorem 1.1） | |

## 主定理

**Theorem 1.1**：(R, 𝔪) → (S, 𝔫) を 0 でない Noetherian 局所環の平坦な局所準同型とする。このとき e(R) ≤ e(S)。次元・剰余体・標数に制限はない。

e は Hilbert–Samuel 重複度。難しさは、平坦性で比べられるのは 𝔪^N S による商なのに対し、e(S) は 𝔫 の冪で決まることにある。閉ファイバーが 0 次元で両方のフィルトレーションが有限余長でも、主要項を直接比べられない。

### 先行研究（序論による）

- Lech：源の次元 ≤ 2、閉ファイバーが完全交叉の重要な場合。
- Ma：等標数で源の次元 3。一般の次元で e(R) ≤ max{1, d!/2^d}·e(S)（Adv. Math. 2017）。標準次数付き代数（完全体上）の場合を弱い lim Ulrich 列で（Invent. Math. 2023）。
- Ulrich 加群の方法（Hanes）。Ulrich 加群・弱い lim Ulrich 列は一般には存在しない（Yhee）。小さな CM 加群も一般には存在しない（OpenAI, *A Complete Local Domain without a Small Cohen–Macaulay Module*）。
- Iyengar–Ma–Walker（ANT 2022）：短い複体と Koszul 複体のテンソルによる方針（Prop 8.3）。本論文の構成の前身。

## §2 一様な評価（論文の核心）

### 設定（§2.1）

- C は可換環。Noetherian 性は仮定しない。h ≥ 1、I = (z₁, …, z_h)C。
- 𝒯_I は I のある冪で消される C 加群のアーベル圏。
- λ: 𝒯_I → [0, ∞] は短完全列で加法的で λ(0) = 0。
- 共通の I の冪で消される長さ 0 の加群の直和と有向余極限は長さ 0。
- 式 (2.1)：0 < μ := λ(C/I) < ∞、λ(C/(z^a)C) = a^h μ、λ H_i(z^a; C) = 0（a ≥ 1、i > 0）。
- 長さ 0 の対象は Serre 部分圏をなすので、その商で核・像・余核・有限スペクトル系列を扱ってよい、と明記している。

解説の言葉では、(C, λ) が z について λ-CM で、パラメータ商の長さが a^h μ。

### Theorem 2.1

F を有限自由 C 加群の複体で、0〜h 次に集中し、Spec C ∖ V(I) 上で局所的に可縮なものとする。b_i = rank F_i とおく。

- (a) H_i(F) は I の冪で消され、λ H_i(F) = 0（i > 0）、λ H₀(F) < ∞。
- (b) さらに Σ(−1)^i b_i = 0 で、微分の成分が全て I^s に入る（s ≥ 1）なら、h だけによる定数 A_h があって

  λ H₀(F) ≥ μ s^h (b₀ − (A_h/s) Σ_i b_i)。

  誤差は O_h(1/s) で、C、I、λ、F によらず一様。

### 部品

- **Lemma 2.2**：(a) の証明。分裂 F ⊗ K_a ≃ ⊕_{T⊆{1..h}} F[|T|] と、Koszul を先にとる二重複体。H₀(F) は H_h(F ⊗ K_a) の、H_i(F) は H_{h+i}(F ⊗ K_a) の直和因子。解説の補題 4.7（付録の補題 B.6）と同じ議論。
- **§2.3、Lemma 2.3**：Y = Proj ⊕ Iⁿ（爆発）、L = IO_Y = O_Y(1)、E = V(L)。C が Noetherian でなくても L は可逆で E は Cartier 因子。
  - (C/I)[Z₁, …, Z_h] → gr_I C の核は各次数で長さ 0。
  - ℙ^{h−1}_{C/I} 上の V(t) のコホモロジーは E 上のものと長さ 0 を法として同型。
- **Lemma 2.4**：D = F_Y ⊗ V または G ⊗ V について、M が大きければ D(j+M) → D(j) は超ホモロジーで 0。超ホモロジーは I の冪で消され、有限長。
- **Lemma 2.5**：χ_λ(F_Y) = λ H₀(F)。交代階数が 0 なら、ℙ^{h−1} から引き戻した任意のベクトル束 V について χ_λ(F_Y ⊗ V) = rank V · χ_λ(F_Y)。
- **G の定義（式 2.6）**：G_i = L^{−is} ⊗ F_i。成分が I^s に入るので s 乗だけ割った複体が作れる。F_Y ⊆ G で、商の層は O_E(l)^{b_i}（l = −is, …, −1）。
- **Lemma 2.6**（Eisenbud–Schreyer 型）：r₁ > ⋯ > r_{h−1} に対し、ℙ^{h−1}_ℤ 上の階数 (h−1)! のベクトル束 V で、任意の環 A と整数 a について次を満たすものがある。
  - a = r_j なら V(a) は非輪状。
  - それ以外ではコホモロジーは単一の次数 #{j : r_j > a} にだけあり、自由で、Euler 標数は ∏(a − r_j)。
  - 構成は、2 元形式の積で定まる有限射 (ℙ¹)^{h−1} → ℙ^{h−1} による押し出し。

### Theorem 2.1 (b) の証明（§2.6）

1. H(x) = ∏_{i=1}^h (x+i) の導関数の根 ρ_j をとり、r_j ≈ sρ_j と丸める（Rolle で −(j+1) < ρ_j < −j）。
2. 根の位置により、G ⊗ V の超ホモロジーは長さ 0 を法として 0 次に集中し、χ_λ(G ⊗ V) ≥ 0。
3. F_Y ⊗ V ⊆ G ⊗ V の差を層ごとに足し、Lemma 2.5、2.6 から
   0 ≤ (h−1)! λH₀(F) + μ Σ_i (−1)^i b_i Σ_{l=−is}^{−1} ∏_j (l − r_j)。
4. 内側の和は Riemann 和で、どの i でも (h−1)! s^h + O(s^{h−1})。交代階数 0 で b₀ だけが残る。

## §3 長さ付き代数の構成

**Theorem 3.1**：(D, 𝔡, k) を次元 h > 0 の完備局所整域で、剰余体が標数 p の完全体とする。D 代数 C と、𝔡 の冪で消される C 加群の上の関数 λ で、次を満たすものがある。

1. 加法的で λ(0) = 0。共通の 𝔡 の冪で消される長さ 0 の加群の直和・和・有向余極限は長さ 0。
2. D の任意のパラメータ系 z と a ≥ 1 について λ(C/(z^a)C) = a^h e((z), D)、λ H_i(z^a; C) = 0（i > 0）。
3. 𝔡-準素イデアル H について、char D = p なら λ(C/HC) = e_HK(H, D)、char D = 0 なら λ(C/HC) ≤ e(H, D)。

構成：

- **標数 p（§3.2）**：C = D_perf。λ は Cohen–Gabber の基底 A = k[[t]] の perfection 上の λ_∞。
  - Lemma 3.2：有界な冪ねじれ加群について、長さ 0 の直和・和・有向余極限は長さ 0。増大列の合併は上限。λ(Mₙ) → 0 なら余極限の長さは 0（推移写像の単射性は不要）。Serre の論文の Lemma 2.4 に当たる。
  - Lemma 3.3：トレース双対による導手の評価。ある 0 ≠ g ∈ A で g^{1/q} C ⊆ B_q = A′D^{1/q}。
  - Lemma 3.4：有限長 D 加群 M について λ_∞(C ⊗ M) = lim q^{−h} ℓ(Φⁿ M)（極限が存在すれば）。
- **混標数（§3.3）**：C = (D ⊗_A A_∞)_perfd。CLMST Cor 4.0.4、Prop 4.0.10、4.0.14、Cor 4.0.18 を使う。

Serre の論文の定理 2.5（解説の定理 6.4）と同じ対象に、(3) の Hilbert–Kunz との関係を加えたもの。

## §4 帰着と補助環

**Lemma 4.1**：完備 Noetherian 局所環 (B, 𝔟, k) と k の代数閉包 k̄ に対し、平坦な局所写像 B → B′ で 𝔟B′ が極大イデアル、B′/𝔟B′ ≅ k̄、e(B′) = e(B) となるものがある。

**Lemma 4.2**：e(R) ≤ e(S) を示すには、R、S が完備、R が整域、dim R = dim S > 0、S の剰余体が代数閉の場合で足りる。両方が標数 p なら、帰着後も等標数 p。

- Nagata の局所化定理（excellent な B と dim B/q + dim B_q = dim B なら e(B_q) ≤ e(B)）で閉ファイバー 0 次元に帰着。
- R の素フィルトレーションと重複度の加法性で R を整域に。
- Lemma 4.1 で剰余体を代数閉に。

**Proposition 4.3**（剰余標数 p > 0、上の帰着後）：分解 R → (T, 𝔱) → S = T/J で、b = dim T/𝔪T、h = d + b として次を満たすものがある。

- (i) T は完備で剰余体は S と同じ。R → T は平坦で閉ファイバーは正則。dim T = h、e(T) = e(R)。
- (ii) T の全ての既約成分は次元 h。J は grade b の perfect イデアルで、S は T 上の長さ b の極小自由分解 P（P₀ = T）をもつ。
- (iii) 𝔫 の極小 reduction の持ち上げ x₁, …, x_d ∈ 𝔱 について、F = P ⊗_T K(x; T) は 0〜h 次の有限自由複体で、F₀ = T、閉点の外で局所的に可縮、微分の成分は 𝔱 に入り、階数の交代和は 0。
- (iv) R の 0 の上の素イデアル Q で T_Q は完全交叉（混標数なら正則）。J 上の極小素イデアルは R の 0 の上にある。混標数では T は generically reduced で、J 上の極小素イデアルはただ一つの T の極小素イデアルを含む。

構成：R の正則な基底 A ⊆ R をとり、A → S に Avramov–Foxby–Herzog の Cohen 分解 A → U ↠ S（U は正則）を当て、T = R ⊗_A U とする。

**Remark 4.4**：T は完備で等次元なので catenary で、dim T_Q + dim T/Q = h。

## §5 標数 p

**Lemma 5.1**（Ma の Hilbert–Kunz の等式）：T は標数 p の完備局所環（剰余体は完全）、J は perfect、S = T/J、x は S のパラメータ系とする。

- e_HK(J + (x), T) = Σ_{Q ⊇ J 極小, dim T/Q = d} e((x), T/Q) · e_HK(JT_Q, T_Q)。
- 各 T_Q が完全交叉なら、右辺は e((x), S)。

**Theorem 5.2**：標数 p の平坦な局所準同型について e(R) ≤ e(S)。

証明：

1. H = J + (x)T とおく。
2. T の各極小素イデアル P について D = T/P とし、Theorem 3.1 の C、λ をとる（I = (z)C、μ = e(D)、z は 𝔡 の極小 reduction）。
3. F の成分を Frobenius で q 乗した F(q) に Theorem 2.1 を s = q − c で当てる。H₀(F(q) ⊗ C) = C/H^{[q]}C なので
   q^h e_HK(HD, D) = λ(C/H^{[q]}C) ≥ e(D)(q − c)^h(1 − o(1))、よって e_HK(HD, D) ≥ e(D)。
4. Hilbert–Kunz と Hilbert–Samuel の結合公式で成分を足し、e_HK(H, T) ≥ e(T)（T の被約性は仮定しない）。
5. Lemma 5.1 より e(S) = e_HK(H, T) ≥ e(T) = e(R)。

### §5.1 Dutta 重複度

**Definition 5.3**：標数 p、次元 d の局所環上の短い複体とは、0 → F_d → ⋯ → F₀ → 0 の有限自由複体で、ホモロジーが有限長かつ H₀ ≠ 0 のもの。Dutta 重複度は χ_∞(G) = lim p^{−nd} χ(Φⁿ G)。

Roberts の Frobenius ホモロジー定理より、短い複体について χ_∞(F) = lim p^{−nd} ℓ H₀(Φⁿ F)（式 5.1）。

**Corollary 5.4**：(R, 𝔪) を標数 p の完備 Noetherian 局所整域、F を短い複体とすると χ_∞(F) ≥ e(R)。Iyengar–Ma–Walker の予想（Conjecture 8.1）の整域の場合。

証明の中で、C = R_perf と λ について λ H₀(C ⊗_R G) = χ_∞(G)（Lemma 3.4 と式 5.1）を示している。つまり「R_perf による評価は Dutta 重複度」が短い複体について明記されている。

## §6 混標数

- **Lemma 6.1**：(A, 𝔞) は正の次元 t、H は 𝔞-準素、f ∈ H、dim A/(f) = t − 1 なら e(H, A) ≤ e(H, A/(f))。
- **Lemma 6.2**：(B, 𝔟) を次元 h の完備局所整域、1 ≤ d ≤ h、L + (x₁, …, x_d) = 𝔟 とし、H_N = L + (x₁^N, …, x_d^N) とおく。
  1. dim B/L < d なら e(H_N, B) = O(N^{d−1})。
  2. L = 𝔮 が素で dim B/𝔮 = d、B_𝔮 が正則なら e(H_N, B) ≤ N^d e((x), B/𝔮) + O(N^{d−1})。
- **Theorem 6.3**：Prop 4.3 の状況で R が混標数なら e(S) ≥ e(T) = e(R)。

証明：

1. **有限拡大で深くする**：T の各成分 B で、パラメータの q 乗根 z_i = u_i^{1/q} を添加する。Heitmann の整拡大 Briançon–Skoda（Heitmann–Ma, Prop 2.8 の形）で 𝔟D ⊆ (z)^{q−h}D となる有限拡大 D をとる（階数 r、正規化してよい）。e(HD, D) = r e(H, B)、q^h e((z), D) = r e(B)。
2. **下界**：Theorem 2.1 より λ(C/(J, x)C)/r ≥ e(B)(1 − h/q)^h(1 − K/(q−h))。K は D によらない。
3. **冪の規則（式 6.8）**：λ(C/(J, x^N)C) = N^d λ(C/(J, x)C)。Lemma 2.2 と写像錐の三角形から。
4. **上界**：S の素フィルトレーションと Lemma 6.1、6.2 で、N → ∞ で D によらない上界。
5. q → ∞ とし、成分ごとに係数 1 で足す（Prop 4.3 (iv) の正則性で、各素イデアルはただ一つの成分に乗る）。

## §7 剰余標数 0

- **Lemma 7.1**：剰余標数 0 で等次元の平坦な局所写像 R → S は、R → R′ → S（e(R′) = e(R)、R′ → S は有限自由、R′ と S は同じ係数体と剰余体）に分解できる。
- **Lemma 7.2**：有限自由な局所写像 R₀ → S₀（次元 d > 0、共通の無限係数体 L と剰余体 L）と r = e(R₀) について、ℤ 上の有限個の多項式の連立方程式 F(t, Y) = 0 で、L[[t]] に解をもち、任意の体 K 上の K[[t]] の解から e(R) ≥ r、e(S) ≤ e(S₀) となる有限自由な局所写像 R → S が作れるものがある。表示行列の小行列式、源の reduction 関係、目標の随伴次数環のモニックな初項関係で上下の評価を記録する。
- **Lemma 7.3**：標数 0 の体 L 上の L[[t]] に解をもつ有限個の多項式の連立方程式は、正標数のある代数閉体 K 上の K[[t]] にも解をもつ。Artin 近似でヘンゼル化に下ろし、さらに有限型の環に下ろして特殊化する。
- **Theorem 7.4**：剰余標数 0 なら e(R) ≤ e(S)。反例があれば Lemma 7.2、7.3 で標数 p の反例ができ、Theorem 5.2 に矛盾する。

## §8 組み立て

Theorem 1.1：§4 の帰着の後、源が標数 p なら Theorem 5.2、混標数なら Theorem 6.3、剰余標数 0 なら Theorem 7.4。

## Serre の論文との関係

- 道具立ては共通：λ-CM な長さ付き代数（§3「Normalized length algebras」）、長さ 0 を法とした Koszul 非輪状性（Lemma 2.2）、CLMST の perfectoid 化。
- 有限加群の列の代わりに何を使うかが違う。Serre の論文は BHM の lim CM 列の代わりに K 理論の降下、Lech の論文は Ma の弱い lim Ulrich 列の代わりに爆発とベクトル束による一様な評価（Theorem 2.1）。

### Serre の論文の解説から移した比較（2026-10-11）

`exposition/ja/exposition-ja.tex` の付録「先行研究との関係」にあった Lech の論文の小節を、ここに移した。上の節と重なる部分は省いた。

**枠組みの対応**

- §2.1（長さの仮定）は、I = (z₁, …, z_h)C の冪で消される C 加群の上の加法的な長さ λ をとり、C のネーター性を課さない。長さ 0 の対象が Serre 部分圏をなすので、その商で核・像・余核・有限スペクトル系列を扱ってよい、と明記している。解説 §4 の評価先 𝒜_λ（長さ 0 の加群で割った Serre 商）を、名前をつけずに使っている形である。
- Lemma 2.2（Koszul 複体の分裂 F ⊗ K_a ≃ ⊕ F[|T|] と、Koszul を先にとる二重複体の議論）は、解説 §3 の反復錐による消滅、§5 の新交叉型の消滅と同じ議論である。
- Theorem 3.1 は Serre の論文の Theorem 2.5 に、標数 p で λ(C/HC) = e_HK(H, D)、混標数で λ(C/HC) ≤ e(H, D)（CLMST Cor. 4.0.18）を加えたもの。Lemma 3.2 は Serre の論文の Lemma 2.4 に当たる。

**小さな CM 加群の反例**

OpenAI, *A Complete Local Domain without a Small Cohen–Macaulay Module*（2026-09-23）の主定理（abstract による）は、剰余体 ℂ の 3 次元完備 Noetherian 正規局所整域で、0 でない有限生成の極大 CM 加群をもたないものが存在する、というもの。小さな CM 加群予想の整域版を否定する。構成は滑らかな射影曲面の切断環 R(X, H) で、小さな CM 加群をもてば K_X² − 2c₂(X) ≤ 6H² が成り立つ、という障害を使う。Lech の論文はこれを「有限加群を全ての環に要求する方法は普遍的でない」根拠として挙げ、ただしこの障害は弱い lim Ulrich 列の非存在までは意味しない、と注意している。

**有限加群の列による経路との対比**

| 予想 | 有限加群の列による条件付きの経路 | OpenAI の経路 |
| --- | --- | --- |
| Serre の正値性 | BHM の lim CM 列 | λ-CM 代数と K 理論の降下 |
| Lech の予想 | Ma の弱い lim Ulrich 列 | λ-CM 代数と短い複体の一様な評価 |

Ma（Invent. Math. 231 (2023)）の弱い lim Ulrich 列は、重複度と生成元数の比が 1 に近づき、高次の Koszul Euler 特性が生成元数に比べて無視できる有限加群の列である。Lech の論文は有限加群の列を使わず、単一の λ-CM 代数と一様な評価で置き換えている（序論では、Ulrich 加群や Ulrich 列を全ての源の環に要求しない方針だと述べている）。Serre の論文と BHM の関係と同じ構図である。どちらも有限加群の列の存在問題を迂回しており、lim CM 列や lim Ulrich 列そのものは構成していない。

**まとめ**

長さ付き代数とその Serre 商という枠組みは、OpenAI の Serre と Lech の二つの論文に共通する方法である。解説 §3–§4 の整理は、この二つに共通する構造を取り出したものと位置づけられる。どちらの論文も有限加群の列の存在を示さずに、それが与えるはずの結論を λ-CM 代数から直接出す。一般の完備局所整域が lim CM 列や lim Ulrich 列をもつかは開いている。小さな CM 加群は一般には存在しない。

## 形式化の見取り図

- **Serre の形式化とほぼ共有できる部分**
  - §2.1 の設定と Lemma 2.2：解説の補題 4.7、付録の補題 B.6。
  - §3 の Theorem 3.1 (1)(2) と Lemma 3.2：Serre の `Paper/Section2`（`theorem_2_5`、`Lemma2_4`、塔と λ_∞）。
- **新しく必要で重い部分**
  - §2.3〜2.6：非 Noetherian 環上の Proj、Čech による超ホモロジー、ℙ^{h−1} 上のベクトル束のコホモロジー（Lemma 2.6）。Theorem 2.1 (b) はここに依存する。
  - §3 (3) の Hilbert–Kunz との関係（Lemma 3.3、3.4、Monsky）。
  - §4 の Cohen 分解（Avramov–Foxby–Herzog）：引用で置くのが現実的。
  - §5 の Lemma 5.1（Ma）：引用。
  - §6 の Heitmann の Briançon–Skoda、§7 の Artin 近似：引用。
- **最初の目標の案**：Theorem 2.1 (b) を名前つきの引用として置き、§5（Theorem 5.2、Cor 5.4）を組み立てる。入力は Theorem 3.1（標数 p）、Lemma 5.1（引用）、Prop 4.3（Cohen 分解は引用）。標数 p の部分は Serre 側でも必要な D_perf と λ_∞ の扱いと重なる。

## 未確認の点

- 引用文献（Avramov–Foxby–Herzog、Heitmann–Ma Prop 2.8、Ma 2017 Lemma 4.2、Artin 1969 Thm 1.10、Iyengar–Ma–Walker Conj 8.1）の該当箇所は原典で照合していない。
- §2.4〜2.6 の証明の細部（Lemma 2.5 の「幾何的な塔」の比較、Lemma 2.6 の (ℙ¹)ⁿ → ℙⁿ の有限性と押し出しの計算）は読み流した程度。
- §6 の上界の部分（Lemma 6.2 の証明と、N → ∞ と q → ∞ の順序）は概略のみ。

## 現状の形式化との対応（2026-10-10 調査）

Serre の形式化（`SerrePositivity/`、285 ファイル、コミット `eb2ad9e` 時点）のうち、Lech の論文に使えるものを洗い出した。

### 前提：長さ付き代数の一般論は既にある

`LengthAlgebra/`（12 ファイル、sorry なし）に、解説の付録 B・C の一般論がほぼこの形で入っている。

- `SerreQuotient`：長さ 0 の加群による Serre 商と忠実な長さ（有限値版、拡大実数値版）。
- `Koszul`：`KoszulFinite`、`KoszulAcyclic`、`koszulEuler`（λ-重複度）、`homology_mem_finiteLengthTorsion`。
- `PerfectVanishing`：`lambdaHomology_projective_vanishing`（有限射影複体の新交叉型の消滅。長さの有限性・局所性・Noether 性・平坦性を仮定しない）。
- `PerfectMinimalLowerBound`：`perfectEuler_minimal_lower_bound`（極小性による 0 次の下界）。
- `KoszulFormula`：`lambdaEuler_baseChange_eq_koszulEuler_mul`（基底から来る類での e_λ 公式）。
- `Comparison`：`perfectEuler_conjSum_eq`（対称なノルム比較）。

長さ関数は `PerfectComplex/NormalizedLength`（`NormalizedLength C J`）、直和・和・有向余極限での長さ 0 の保存は `PerfectComplex/SupProperty`。

### 各部分の対応

| Lech の論文 | リポジトリの現状 | 評価 |
| --- | --- | --- |
| §2.1 の設定（λ、直和・余極限の安定性） | `NormalizedLength`、`SupProperty` | そのまま使える |
| 式 (2.1) | `KoszulFinite`、`KoszulAcyclic`、`Inputs/LengthAlgebra` | そのまま使える |
| Lemma 2.2 | `lambdaHomology_projective_vanishing`、`homology_mem_finiteLengthTorsion` | ほぼそのまま。「V(I) の外で局所的に可縮」から零ホモトピーを作る小さな補題が要る（`Support.isSupported_of_forall` などは既存） |
| Theorem 2.1 (b)、Lemma 2.3–2.6 | なし（代数幾何はゼロ） | 新規。設計は [lech-section2-algebraic.md](lech-section2-algebraic.md) |
| Theorem 3.1 (1)(2)、標数 p | `Paper/Section2`：`PerfectConductor`、`PerfectApproximation(Length)`、`PerfectTower`、`PerfectBaseChange`、`CommutativeAlgebra/TraceConductor` は sorry なし。`LengthAlgebraConstruction` に sorry 2 つ（等標数・混標数） | 大部分ある。等標数の残りは Lech §3.2 の式 (3.4)（核の O(1/q) 評価）と (3.6)–(3.7)（Koszul の極限）に当たる。Roberts は引用 |
| Lemma 3.2 | `Paper.Section2.Lemma2_4`、`SupProperty` | そのまま使える。(3) の「推移写像の単射性不要」の形があるかは要確認 |
| Theorem 3.1 (3)：λ(C/HC) = e_HK | `PerfectApproximationLength` に B_q の商の公式 (3.3)。Hilbert–Kunz 重複度の定義・Monsky はない | 一部ある。HK は新規（Monsky は引用） |
| Lemma 3.4 | `PerfectApproximationLength` に近い形 | 一部ある |
| §3.3 混標数 | `LengthAlgebraConstruction` の混標数の sorry（CLMST） | Serre と共有（引用） |
| Lemma 4.1 | `Paper.Section2.lemma_2_1`（主張のみ、sorry） | 同じ主張（Serre の版は長さ・次元・Tor を保つ形で、Lech の重複度の保存はその系）。証明すれば両方に効く |
| Lemma 4.2 | Nagata の局所化定理なし。重複度の加法性なし（交点重複度の加法性 `IntersectionMultiplicity.Additivity` はある） | 新規（Nagata は引用） |
| Prop 4.3 | 極小自由分解（`HomologicalAlgebra/MinimalFreeResolution` ほか）、Koszul、正則列（`CommutativeAlgebra/RegularSequence`）はある。Cohen 分解、極小 reduction、完全交叉はない | 部品は一部ある。Cohen 分解は引用、極小 reduction は新規 |
| Hilbert–Samuel 重複度 | `CommutativeAlgebra/HilbertSamuel`：定義あり、多項式性・次元定理・正値性は sorry。`MultiplicityFormulas`（パラメータ冪の公式、Koszul Euler 特性の公式、sorry 2） | 土台はある。結合公式、Lemma 6.1、6.2 など重複度の一般論を厚くする必要がある |
| Lemma 5.1（Ma） | なし | 引用 |
| Theorem 5.2、F(q) | Frobenius は `PerfectTower` に一部 | 新規だが軽い（Theorem 2.1 を引用で置けば組み立てられる） |
| Cor 5.4（Dutta） | 下界の一般論（`PerfectComplex/MinimalLowerBound` など）あり。Dutta 重複度の定義なし | 一部ある |
| §6 | 写像錐の長完全列（`HomologicalAlgebra/ConeLES`）あり。Heitmann なし | Heitmann は引用。Lemma 6.1、6.2 は新規 |
| §7 | なし | 符号化（Lemma 7.2）は新規、Artin 近似は引用 |

### まとめ

- 長さ付き代数の一般論と Koszul 非輪状性（§2.1、Lemma 2.2、§3 (1)(2)、Lemma 3.2）は、ほぼ全部使える。
- 標数 p の長さ付き代数の構成は 8〜9 割できている。残りは Lech §3.2 が詳しく書いている部分で、Lech に沿えば Serre 側の sorry（`LengthAlgebraConstruction` の等標数）も埋まる。
- 新しく作る必要があるのは、重い順に、(1) Theorem 2.1 (b) の Čech 複体による議論、(2) 重複度の一般論（Hilbert–Samuel の多項式性、結合公式、Hilbert–Kunz と Monsky、極小 reduction）、(3) 帰着の補題（Lemma 4.2、Prop 4.3、§7 の符号化）。

### 最初の段階の案

1. Theorem 2.1 (b) を名前つきの引用として置く。
2. Lech §3.2 に沿って `LengthAlgebraConstruction` の等標数の sorry を埋める（Serre と Lech の両方に効く）。
3. Hilbert–Kunz 重複度を定義し、Theorem 3.1 (3) の標数 p を示す（Monsky は引用）。
4. Prop 4.3（Cohen 分解は引用）と Lemma 5.1（引用）を置き、Theorem 5.2 を組み立てる。
