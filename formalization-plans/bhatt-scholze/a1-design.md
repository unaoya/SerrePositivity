# A1 の設計：Hodge–Tate 比較（原典 §4.2・§5・§6、2026-11-02）

概要：E3 を消す道筋の単位 A1。原典 BS 著者版 §4.2（Construction 4.9、Lemma 4.10、Thm 4.11、Cor 4.12）、§5（Thm 5.2、Lemma 5.4、Cor 5.5）、
§6（Construction 6.1、Prop 6.2、Thm 6.3）を、**定義は原典のまま、定理は E3 に要る特別な場合だけ**の方針で形式化するための項目表・
証明の筋・必要な一般論・差の記録・決定待ち。A0 の設計書（Not 4.16 の Δ、Rem 4.19 の模型、envelope の普遍性、Lemma 4.20・4.22）を前提にする。
方針：HT 比較は迂回せず原典の経路で示す（10-25 決定）。E3 に要るのは**多項式代数** R = (A/d)⟨X_1,…,X_r⟩ の HT 比較で、原典の帰着
（Thm 6.3 → Prop 6.2 → Construction 6.1 で結晶 prism へ → Cor 5.5 → Lemma 4.20 で Z_p へ → Thm 5.2 → Lemma 5.4 ＋ Cartier）をそのまま使う。
計算は A0 の Čech–Alexander 複体（非正規化の Tot）の上で行う。
規約：向き付き有界基底（ノート D5）。微分形式は p 完備な意味（p 完備多項式代数では dX_j 上の自由加群、D26）。環構造と Bockstein は
当面 Čech–Alexander 模型の上で与える（D27、A2・A4 の CAlg 値と後で結ぶ）。Lean の名前は仮。ビルドしない。
使われ方：A1 の骨組み（`drafts/A1/`）の正本。A2（Construction 7.6 の HT filtration）・A5（Lemma 8.6 の標数 p の de Rham 比較と Cartier）が
本書の Thm 6.3・Thm 5.2 の形を前提にする。

## 0. 範囲と前提

- 含む：Constr 4.9（HT 比較の写像 η^*）、Lemma 4.10、Thm 4.11＝Thm 6.3（多項式代数）、Cor 4.12（底変換、HT の後）、Thm 5.2（特別な場合、§5 と D25）、
  Lemma 5.4、Cor 5.5、Constr 6.1、Prop 6.2（一般の r）。§2 の前提：Lemma 2.36 の多変数版（生の pushout の p ねじれなし、T2-2 の変数の場合）、
  Lemma 2.24、Lemma 2.43・Cor 2.44 は変数の場合（A0-3c の存在定理で代替）。
- 含まない：Thm 6.4 の一般形（de Rham 比較。**多項式代数・mod p の特別な場合は A1-5、§9**）、Rem 4.13・4.14、Prop 4.15、Lemma 4.21（étale 局所化。多項式代数に限るので不要）、Thm 5.2 の一般の pd イデアル I の場合。
- 基底 prism の範囲（**D-A1-2、2026-11-02 決定：一般の有界向き付き prism**）：原典の Prop 6.2 は一般の (A,(d)) を、普遍向き付き prism
  (A_0,(d))（Ex 3.4）と E := A ⊗̂^L_{A_0} D_0（D_0 = A_0{φ(d)/p}^∧、a : A_0 → D_0 は Construction 6.1 の α）への底変換で扱う。E は一般に
  離散でない単体的可換環だが、**E を環として作る必要はない**：使うのは底変換関手 b̂^*（b : A → E）と ĉ^*（c : Z_p → E）だけで、
  テンソルの結合則により b̂^*K = (K ⊗^L_A E)^∧ = (K ⊗^L_{A_0} D_0)^∧ = â^*(Res_{A_0} K)、ĉ^*K = ((K ⊗^L_{Z_p} A) ⊗^L_{A_0} D_0)^∧ = â^*(Res_{A_0}(K ⊗^L_{Z_p} A))
  と、通常の環 A_0・A・D_0・Z_p の間の底変換と制限の合成で書ける（D30）。保存性・有限 Tor 振幅・Lemma 4.22 もこの合成について従う。
  Rem 4.19 の複体の項ごとの一致 b̂^*C^n_{R/A} ≃ ĉ^*C^n_{F_p[X]/Z_p} も、C^n_A = C^n_{A_0} ⊗̂_{A_0} A、C^n_{A_0} ⊗̂_{A_0} D_0 = C^n_{D_0} = C^n_{Z_p} ⊗̂_{Z_p} D_0
  （Rem 4.19 の prism の射に沿う底変換、A0 の `cechAlexanderAffine_baseChange`）と結合則から出る。
  したがって普遍向き付き prism（Ex 2.21・Ex 3.4、ノートの T2-4）が A1 の範囲に入る。
- R：p 完備化した多項式代数 (A/d)⟨X_1,…,X_r⟩、r 有限（Prop 6.2 は原典では r = 1、Thm 6.3 で一般の r。本書は最初から一般の r）。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Constr 4.9 | 定義そのまま（η^0、η^1、Bockstein、dg 代数の射 η^*） | `hodgeTateMap` | 環構造・Bockstein は模型の上（D27）。de Rham 複体の普遍性 | A1-1 |
| Lemma 4.10 | 定理（Prop 6.2 の系） | `bockstein_sq_zero` | — | A1-4 |
| Thm 4.11 ＝ Thm 6.3 | 定理。多項式代数、基底は §0 の範囲 | `hodgeTate_iso` | Prop 6.2 | A1-4 |
| Cor 4.12 | 定理。同じ範囲 | `prismaticCohomology_baseChange'` | Thm 6.3、導来 Nakayama | A1-4 |
| Not 5.1 | 定義そのまま（結晶 prism と pd イデアル I ∋ p、R^{(1)}） | `crystallinePrism`、`frobeniusTwist` | `OrientedPrism.crystalline` あり | A1-2 |
| Thm 5.2 | 定理。**特別な場合**：A = Z_p、I = (p)、R = F_p[X_1,…,X_r]。結晶コホモロジーの扱いは D25。**11-07：使う形は mod p の cohomology 同型だけ（§10）** | `crystallineBridgeModP_isCohomologyIso`（§10 の段 2） | pd 包の Čech 脈体、Lemma 5.4（mod p なので導来 Nakayama は不要） | A1-3 |
| Rem 5.3 | 不要 | — | — | — |
| Lemma 5.4 | 定理。有限変数、N は余単体的可換環（§10 の段 1）。無限変数は G-A1-15 | `frobeniusTwist_cech_quasiIso`、`frobeniusTwist_cech_quasiIso_infinite` | 余単体的ホモトピーの一般論（§4） | A1-3 |
| Cor 5.5 | 定理。多項式代数、結晶 prism。(Z_p,(p)) の場合は `hodgeTate_iso_polynomial_Zp` ＝ `hodgeTate_of_deRham_cartier`（§10） | `hodgeTate_iso_crystalline` | Thm 5.2、Cartier 同型、Lemma 4.20 | A1-3 |
| Constr 6.1 | 定義そのまま（B = A{φ(d)/p}^∧、α、性質 (1)(2)(3)） | `crystallineCover`、`crystallineCoverMap` | Cor 2.39 の r = 1（済）、Lemma 2.24（済）、導来 Nakayama、Tor 振幅 | A1-4 |
| Prop 6.2 | 定理。一般の r、基底は §0 の範囲 | `hodgeTate_iso_of_construction61`（drafts） | Constr 6.1、Cor 5.5、Lemma 4.20 | A1-4 |
| Thm 6.4 | 不要（多項式・mod p の場合は A1-5、§9） | — | — | — |
| 結晶 site・RΓ_crys（Thm 5.2 の証明、[Ber06 §III.4]） | **11-07 追加**：最小限で定義（§11） | `CrysOver`・`zariskiTopology`・`crystallineCohomology` | drafts/A1/CrystallineSite | A1-6 |
| Lemma 2.36 多変数 | 定理。変数の場合：Z_p{x_1,…,x_r, φ(x)/p} は離散・p ねじれなしで pd 包 D_{(x)}(Z_p{x}) | `pdEnvelope_eq_frobeniusDivision` | 像の形は済（`pDivisionFactorialSubring_eq_raw_range`）。p ねじれなしは r = 1 のみ（T2-2） | A1-2 |
| Lemma 2.38・Cor 2.39 | 変数の場合は Lemma 2.36 多変数と自由 δ 環の平坦底変換で済む | — | — | A1-2 |
| Ex 2.21・Ex 3.4 | 定義そのまま（普遍 distinguished δ 環 Z_(p){d, δ(d)^{-1}} と、その (p,d) 完備化 A_0。有界 prism、(p,d) 正則、A_0/p の Frobenius が d 完全平坦、向き付き prism への普遍性） | `universalOrientedPrism` | 未（T2-4）。自由 δ 環・δ 環の局所化（`DeltaLocalization`）・完備化の δ 構造は済。Frobenius の mod p 自由性は `FreeDeltaFrobeniusFlat` | A1-4 |
| de Rham 複体 | 定義（p 完備多項式代数について、dX 上の自由加群と d。D26） | `deRhamComplex` | Mathlib に de Rham 複体はない（Kähler 微分・外冪はある） | A1-1 |
| Cartier 同型 | 定理。F_p 上の多項式代数（乗法的、§10 の段 5） | `finitePolynomialCartier`（`PolynomialCartier`） | なし。直接計算 | A1-3 |
| pd 包の Čech 脈体と de Rham 複体の比較 | 定理。D68 改訂後の経路では F_p[X] の mod p だけ（§10 の段 4）。Z_p⟨X⟩ の整係数版は A1-5（G-A1-17） | `pdDeRhamCohomologyIso`、`pdDeRhamCohomologyIso_cup` | なし。古典（Berthelot、Bhatt–de Jong） | A1-3 |

## 2. 定義の形

### 2.1 de Rham 複体（D26）

R = (A/d)⟨X_1,…,X_r⟩（p 完備化した多項式代数、以下 k := A/d）について、Ω^i_{R/k} := R 上の自由加群（基底 dX_{j_1} ∧ ⋯ ∧ dX_{j_i}、j_1 < ⋯ < j_i）、
d : Ω^i → Ω^{i+1} を通常の式で定める（p 完備な Kähler 微分。R は p 完備なので Mathlib の `KaehlerDifferential` の p 完備化と一致するが、
A1 では自由加群として直接定義する）。可換 dg 代数の構造（外積）と、普遍性「dg 代数の射 Ω^*_{R/k} → H^* は、環の射 R → H^0 と、
R 加群の射 Ω^1 → H^1 で H^0 → H^1 の微分（ここでは Bockstein）と両立し H^1 の像の平方が零なもの、から一意に決まる」を定理にする
（原典 Constr 4.9 の「universal property of the de Rham complex」）。
標数 p の F_p[X]（完備化不要）も同じ定義。Frobenius 捻り R^{(1)} := R ⊗_{k, φ} k（Not 5.1。k = F_p なら R^{(1)} ≅ R）。

### 2.2 模型の上の環構造と Bockstein（D27）

A0 の Čech–Alexander 複体 C^•（余単体的 δ-A 環）とその mod d の C^•/dC^•（余単体的 R 代数。各 C^n/dC^n は R 代数で、構造射は R 代数の射）。
- Tot(C^•/d)（非正規化）は Alexander–Whitney の cup 積で dg 環、コホモロジー H^*(Tot(C^•/d)) は次数付き可換環（余単体的可換環の
  cup 積の次数付き可換性）。R 代数。これを Ō_{R/A} の模型と呼ぶ。
- Bockstein β : H^i(Tot(C^•/d)) → H^{i+1}(Tot(C^•/d))：各 C^n で d は正則なので 0 → C^•/d →d→ C^•/d^2 → C^•/d → 0 が余単体的加群の短完全列、
  その連結準同型。向き付きなので捻り {i} は落とす（原典 Constr 4.9 の最後の文）。β は H^* の微分（β² = 0、Leibniz）で、H^*(Tot(C^•/d)) は
  dg 環になる。
- η^0 : R → H^0（R → C^0/dC^0 の合成）、η^1 : Ω^1_{R/k} → H^1、dX_j ↦ β(η^0(X_j))（R 線形に延ばす）。Lemma 4.10（β(f)² = 0）のもとで
  §2.1 の普遍性により η^* : Ω^*_{R/k} → H^*(Tot(C^•/d)) が dg 代数の射として一意に延びる。これが Constr 4.9 の η^*_R。
- D27：原典の H^*(Ō_{X/A}) は「位相における可換環対象のコホモロジー」の次数付き可換環。本書では模型の上で与え、抽象的な Δ（CAlg 値の RΓ、
  A2・A4）の環構造との一致は、Čech–Alexander 複体が CAlg 値で Δ を計算すること（余単体的可換環 → E∞、Barratt–Eccles／Alexander–Whitney）
  の定理として A2・A4 に置く。A1 の定理はすべて模型について述べる。

### 2.3 結晶側（Not 5.1、Thm 5.2 の対象）

A = Z_p、I = (p)、R = F_p[X_1,…,X_r]、B_0 = Z_p⟨X⟩ = Z_p[X]^∧_p、B = Free_δ(B_0)^∧ = Z_p{X}^∧（A0 の `completedFreeDelta`）、J_0 = (p)。
- 原典の C^• は B^•{J_0^•B^•/p}^∧。J_0^n = (p, X^{(i)} − X^{(0)})、よって C^0 = B、C^n = B^n{z/p}^∧（z_i := X^{(i)} − X^{(0)}）＝ A0 の Rem 4.19 の模型
  （d = p）。A0 の存在定理により C^n = Z_p{X^{(0)}, Y_1,…,Y_n}^∧（z_i = pY_i）で離散・p ねじれなし。
- D^• := J_0^•B^• の pd 包の p 完備化 = B^•{φ(z)/p}^∧（Cor 2.39）。変数 z は B^n = Z_p{X^{(0)}, z}^∧ の自由 δ 変数なので、
  D^n = (D_{(x)}(Z_p{x_1,…,x_n}) ⊗_{Z_p{x}} B^n)^∧（自由 δ 環の平坦底変換）で、Lemma 2.36 の多変数版（変数の場合）だけが要る（Lemma 2.38・Cor 2.39 の
  一般形は不要）。D^n は離散・p ねじれなしの δ 環で (D^n, (p)) は結晶 prism。
- η : φ_A^*C^• = C^• → D^•（A = Z_p なので φ_A = id）：C^n = B^n{z/p}^∧ → D^n = B^n{φ(z)/p}^∧ を b ↦ φ_{B^n}(b)（z/p ↦ φ(z)/p）で。
  envelope の普遍性（A0 の `IsPrismaticEnvelope.lift`、D^n は prism over (Z_p,(p))）で定義し、余単体的射。
- D^n ≅ C^n ⊗_{B^n, φ} B^n（相対 Frobenius に沿う引き戻し。C^n = Z_p{X^{(0)}, Y}^∧ with z = pY の φ に沿う底変換は z ↦ φ(z) で D^n）。

### 2.4 Construction 6.1 の対象

(A,(d)) 向き付き prism で A/p の Frobenius が平坦、A/d が p ねじれなし。
（Lean の仮定は D77（design-status）：原典の「Frobenius が平坦」を本体で使う形に言い換えたもの。11-12 追記）
- B := A{φ(d)/p}^∧（r = 1 の Cor 2.39、既存 `Andre/Envelope/PDivision` の形）。Lemma 2.24 で φ(d) = pu（u 単元）、B は (p, φ(d)) 完備ゆえ (p,d) 完備、
  (d) の pd 包の p 完備化で離散・p ねじれなし。(B,(p)) は結晶 prism。
- α := (A → B) ∘ φ_A : (A,(d)) → (B,(p)) は prism の射（α(d) = φ(d) ∈ pB）。
- α̂^* : D_comp(A) → D_comp(B)（導来 (p,d) 完備底変換）の性質：(1) 保存的、(2) 有限 (p,d) 完全 Tor 振幅（c の明示）、(3) α̂^*Δ_{R/A} ≃ Δ_{R_B/B}
  （Lemma 4.20）。証明は mod p の分解 (6)：A/p → A/(p,d) → A/(p,d^p) → B/p ≅ D_{(d)}(A/p) で、最初は有限 Tor 振幅（d 正則 mod p：A/d が
  p ねじれなしなので d は A/p で正則）、二つ目は Frobenius の平坦性、最後は pd 包の自由性。

### 2.5 Tor 振幅の実例（A0 §2.9 の定義で）

- 平坦な射（Z_p → 結晶 prism A、A は p ねじれなし）：c = 0。
- Constr 6.1 の α：**c = 3**（A0 §2.9 の Koszul 版の述語——任意の K ∈ D^{≥n}(A₀) について (K ⊗^L B) ⊗ Kos(B; p, α(d)) ∈ D^{≥ n−c}——で。D4-04、11-03、二度目の訂正）。
  評価：B/p の A₀ 上の Tor 次元 ≤ 2（A₀ → A₀/p で 1 段、α mod p で 1 段）に、標的の Kos(B; p, α(d)) = Kos(B; p, pu) ≃ Kos(B; p) ⊗ Kos(B; 0) の余分な 1 段を加えて 3。
  下界：A₀ で (p,d) は正則列なので K = A₀/(p,d) = Kos(A₀; p, d) を取ると K ⊗^L B = Kos(B; p, pu) ≃ Kos(B; p, 0)、さらに Kos(B; p, pu) を掛けて Kos(B; p, 0, 0, 0) 型となり
  H^{−3} = B/p ≠ 0。以前の「c = 1」は α mod p（A₀/p → B/p、(6) の最初の射）の**通常の Tor 振幅 ≤ 1** の値で、Koszul 版の (p,d) 完全 Tor 振幅とは別の量。
  **Lemma 4.22 に要るのは有限性だけ**なので二つを分けて記録する：(i) `torAmplitude_modP_le_one`（α mod p の通常の Tor 振幅 ≤ 1、保存性と (6) の分解に使う）、
  (ii) `HasFiniteCompleteTorAmplitude α (p,d) 3`（Lemma 4.20・4.22 用。数値は公開しない方針でもよい）。
- Prop 6.2 の b（D-A1-2 で (i) を採る場合のみ）。

## 3. 証明の筋（原典の帰着の順）

1. **Thm 6.3（多項式代数）⇐ Prop 6.2（一般の r）**：Thm 6.3 の証明は「Lemma 4.21 で多項式代数に帰着し、Prop 6.2 と同じ議論」。多項式代数に限るので
   Prop 6.2 を一般の r で示せばよい。
2. **Prop 6.2**：η : ⊕_i Ω^i_{R/k}[−i] → Tot(C^•/d) を D(R) で選ぶ（Ω^i は自由 R 加群なので、H^i の像の基底の代表元を選ぶ）。η が擬同型であることを示す。
   **順序（W9-I-25）**：まず r = 1 で η⁰・η¹ だけから加群の比較を行い（H² = 0 を得る）、Lemma 4.10（平方零）を導き、それから一般の r の
   dg 比較（外積写像、基底の順序つき cup 積）を作る。一般 r の加群写像を先に cup 積で作る場合は、その定義と底変換との両立を明記する。
   (a) 結晶 prism (A,(p))：Cor 5.5。(b) 普遍向き付き prism (A_0,(d))：α̂^* が保存的（Constr 6.1 (1)）で α̂^*Δ_{R/A_0} ≃ Δ_{R_{D_0}/D_0}（(3)、Lemma 4.20 と
   Rem 4.19 の底変換）なので、(D_0,(p)) の場合（a）に帰着。η の α̂^* による像が (D_0,(p)) の HT 写像に一致することを確かめる（生成元で）。
   同じ議論は Construction 6.1 の仮定を満たす任意の (A,(d)) に通る。
   (c) 一般の有界向き付き prism (A,(d))：d の選択で A_0 → A。b̂^* := â^* ∘ Res_{A_0}（§0 の読み方）は (p,d) 完備な A 複体の上で保存的
   （Res は完備性と零を保ち、â^* は保存的）。b̂^*Δ_{R/A} ≃ ĉ^*Δ_{F_p[X]/Z_p}：Rem 4.19 の複体で項ごとに（§0）、Tot と交換するのは Lemma 4.22
   （a : A_0 → D_0 は有限 (p,d) 完全 Tor 振幅、Z_p → A は Tor 振幅 ≤ 1、Res は完全）。この同一視が b̂^*η を (Z_p,(p)) の HT 写像（Cor 5.5 で同型）に
   写すことを生成元で確かめる。よって b̂^*η が同型、保存性で η が同型。
3. **Cor 5.5**：結晶 prism (A,(p))、S = A/p[X]。Lemma 4.20 で (Z_p,(p)) に帰着（Z_p → A は平坦、S = F_p[X] ⊗ A/p）。R := F_p[X]、S = R^{(1)} = R。
   Thm 5.2（特別な場合）で Tot(C^•) ≃ Tot(D^•)、D25 の形で Tot(D^•) ≃ Ω^•_{Z_p⟨X⟩/Z_p}、mod p で H^i(Tot(C^•/p)) ≅ H^i(Ω^•_{F_p[X]/F_p})、
   Cartier 同型で ≅ Ω^i_{F_p[X]^{(1)}}。η^* との一致を生成元で確かめる（η^1(dX) = β(X) ↦ C^{-1}(dX) = [X^{p−1}dX]。紙の検証 §8 の 3）。
4. **Thm 5.2（特別な場合、§2.3 の記号）**：η : C^• → D^• は余単体的 δ 環の射。D^• = C^• ⊗_{B^{•,(1)}} B^•（相対 Frobenius の引き戻し、平坦）。
   Lemma 5.4 を N = C^•/p、B^• の mod p に適用すると η mod p は非正規化複体の擬同型。両辺 p ねじれなし・p 完備なので導来 Nakayama で η は擬同型。
   Frobenius との両立：η は δ 環の射なので φ と可換（D25 の β 形では結晶側の Frobenius は D^• の δ 構造のもの。原典の「結晶コホモロジーの
   Frobenius との一致」の議論は RΓ_crys を定義する α 形でだけ要る）。
5. **Lemma 5.4（有限変数、無限変数は G-A1-15 の filtered 余極限で）**：原典どおり。k 標数 p、B = k[N^r] = k[M]、B^• = k[EM]（EM は 0 → M の Čech 脈体、[n] ↦ M^{⊕[n]}）、B^{•,(1)} = k[E(pM)]。
   S = {0,…,p−1}^r の剰余類代表で k[EM] ≅ k[E(pM)] ⊗_k k[ES]（半余単体的加群として自由）、k[ES] は k → C^0 := k[M^{gp}/pM^{gp}] の Čech 脈体の
   半余単体的加群に同じ、C^0 → k の切断があるので Čech 脈体 k → C^• は余単体的加群のホモトピー同値、テンソルで保たれ、
   非正規化複体は半余単体的構造だけで決まる。
6. **D25 の β 形：Tot(D^•) ≃ Ω^•_{Z_p⟨X⟩/Z_p}**（mod p でよい：Tot(D^•/p) ≃ Ω^•_{F_p[X]/F_p}）。二段：(i) 多項式環 B_0 = Z_p⟨X⟩ の pd Čech 脈体
   D_0^•（δ 変数なし）について Tot(D_0^•) ≃ Ω^•_{B_0}：双複体 K^{n,j} = Ω^j_{D_0^n}（**pd 微分**：dγ_m(z) = γ_{m−1}(z)dz、G-A1-7）を二通りに Tot する。
   列（n 固定）は pd-Poincaré 補題（Ω^•_{D_0^n/Z_p} ≃ Ω^•_{B_0/Z_p}、D_0^n = B_0⟨z_1,…,z_n⟩_{pd}）で、各列は Ω^•_{B_0} に擬同型、よって
   Tot K ≃ Tot_n(定数) ≃ Ω^•_{B_0}。行（j 固定）は、**j ≥ 1 では** 余単体的加群 Ω^j_{D_0^•} が収縮可能（Bhatt–de Jong 2011 Lemma 2.15–2.17：
   Ω^1_{D_0^•} に基底ごとのホモトピーを作り、外冪・テンソル・完備化へ延ばす。G-A1-14）、**j = 0 の行 D_0^• は収縮可能ではない**（Tot D_0^• は
   結晶コホモロジーそのもの。Codex W9-I-13 の計算：一変数 mod p で H¹(D_0^•/p) ≠ 0）。よって Tot K ≃ Tot(D_0^•)。
   **訂正（2026-11-02、W9-I-13）**：以前の「D_0^• が切断つきの Čech 脈体で行が非輪状」は誤り。行の非輪状性は j ≥ 1 の Ω^j の収縮から出る。
   (ii) D^•（δ 変数つき、B = Z_p{X}^∧）と D_0^• の比較（**W9-I-18 で再訂正**：(i) の列の議論を D^• に直接当てることはできない。pd を加える核は
   J_0^n B^n = (p, x^{(i)}_{·,0} − x^{(0)}_{·,0}) で、高い δ 座標の差 t = x^{(1)}_{·,1} − x^{(0)}_{·,1} は通常の多項式変数のまま残り、mod p で t^p が列の
   H⁰ に余分に現れる）。**正しい比較**：Q := Z_p[U_k | k ≥ 1]（追加の δ 座標）とすると全次数で D^n ≅ (D_0^n ⊗_{Z_p} Q^{⊗(n+1)})^∧_p、余面・余退化は
   copy の挿入・同一視と両立。E^• := Q^{⊗(•+1)} は Z_p → Q の通常の Čech 余脈体で、retraction U_k ↦ 0 の extra degeneracy により Z_p → E^• は
   余単体的加群のホモトピー同値（G-A1-3）。D_0^• とテンソルして（G-A1-3 のテンソルでの保存）、自然な包含 D_0^• → D^• は非正規化複体の擬同型
   （mod p^a で同じ収縮、Rlim_a で完備版）。D_0^• 自体の split 性は主張しない（W9-I-13 と整合）。G-A1-16。
7. **Cor 4.12**：導来 Nakayama で mod d に帰着し、Thm 6.3 と微分形式の底変換から。Lemma 4.20 の Tor 振幅の仮定が外れる。
8. **Lemma 4.10**：Prop 6.2 の H^2 = 0（r = 1 の affine 直線で β(X)² ∈ H^2 = 0）と関手性（任意の f は X ↦ f で affine 直線から来る）。

## 4. 必要な一般論（A1-G）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A1-1 | 余単体的可換環の非正規化複体の cup 積（Alexander–Whitney）、dg 環、H^* の次数付き可換性 | EInfinity/AlexanderWhitney に余鎖の余モノイドの部品。cup 積としての形は要確認 | §2.2 |
| G-A1-2 | 余単体的加群の短完全列の連結準同型（Bockstein）と Leibniz 則 | Mathlib の短完全列の長完全列 | §2.2 |
| G-A1-3 | 余単体的加群のホモトピー同値 ⇒ 非正規化複体の鎖ホモトピー同値；切断をもつ射の Čech 脈体はホモトピー同値（extra degeneracy）；ホモトピー同値はテンソル積で保たれる；非正規化複体は半余単体的構造で決まる | Mathlib `SimplicialObject/Homotopy`・`ChainHomotopy`（単体的。余単体的は双対）。Čech 脈体の extra degeneracy は要作成 | Lemma 5.4、§3 の 6 |
| G-A1-4 | 導来 Nakayama：導来 (p,d) 完備な K で K ⊗^L A/(p,d) = 0 ⇒ K = 0；p 完備・p ねじれなしの複体の射で mod p が擬同型なら擬同型 | HA/DerivedCompletion に相当する補題がある見込み（要確認） | Thm 5.2、Constr 6.1(1)、Cor 4.12 |
| G-A1-5 | 完全忠実平坦な射に沿う底変換の保存性、有限 Tor 振幅の合成 | CommutativeAlgebra/CompletelyFlat | Constr 6.1 |
| G-A1-6 | pd 包：(x_1,…,x_r) に沿う pd 包 D_{(x)}（Mathlib の `DividedPowers` で分冪構造、一変数の分冪多項式代数 Γ⟨x⟩ は Delta/DividedPower/RankOneDP）、多変数はテンソル積、平坦底変換 | 一変数は済、多変数は要作成（T2-1 の変数の場合） | §2.3、§3 の 6 |
| G-A1-7 | **pd 微分加群と pd de Rham 複体**（分冪と両立する微分 dγ_m(z) = γ_{m−1}(z)dz。通常の Kähler 微分ではない：標数 p の分冪多項式環では余分な微分形式が出る、W9-I-14）と pd-Poincaré 補題：Ω^•_{B⟨z⟩_{pd}/B} ≃ B（標数 p でも、p 完備でも）。通常の多項式代数の de Rham 複体との関係を明示 | なし | §3 の 6 |
| G-A1-8 | Cartier 同型（F_p[X_1,…,X_r]）：C^{-1} : Ω^i_{F_p[X]^{(1)}} → H^i(Ω^•_{F_p[X]/F_p}) | なし。Künneth（一変数の直接計算のテンソル） | Cor 5.5 |
| G-A1-9 | de Rham 複体の普遍性（§2.1） | なし | Constr 4.9 |
| G-A1-10 | D(R) で自由加群からの射を H^i の元から持ち上げる | 初等 | Prop 6.2 の η |
| G-A1-11 | **値が CAlg の RΓ と模型の環構造の一致（D27 の一般論）**：Sheaves 層を E = CAlg_R（E∞-A 代数の ∞ 圏、EInfinity の `CAlg_R`）で使い、環の前層 O_Δ を CAlg 値前層として RΓ を取る（CAlg_R の presentable 性 G12 が要る）。余単体的可換環 C^• の Tot は Barratt–Eccles／Alexander–Whitney で E∞ 代数になり、S3 の補題の CAlg 版で RΓ_CAlg(O_Δ) ≃ Tot C^• が E∞ 代数の同値。その H^* の環構造が §2.2 の cup 積に一致する | EInfinity に Barratt–Eccles・Alexander–Whitney（余鎖の余モノイド）、忘却の極限保存。CAlg_R の presentable 性・余単体的環の Tot の E∞ 構造は未 | D27。A2（Construction 7.6 の可換代数対象）でも要る |
| G-A1-12 | 普遍向き付き prism（Ex 2.21・3.4）：自由 δ 環の δ(d) での局所化と (p,d) 完備化、有界性、(p,d) 正則、Frobenius の mod p 平坦性、向き付き prism への普遍性 | 自由 δ 環・`DeltaLocalization`・完備化の δ 構造・Frobenius の mod p 自由性は済 | Prop 6.2 (c) | **済**（11-12 確認：Ex 3.4 は本体で証明済み、`Delta/Distinguished/Universal`・`Prism/Basic/Construction61Frobenius`）
| G-A1-13 | 底変換関手の合成の性質：Res_{A_0} が (p,d) 完備性と零を保つこと、Tor 振幅の合成、Lemma 4.22 の合成への適用 | HA/DerivedCompletion（2b の後に読む） | Prop 6.2 (c) |
| G-A1-14 | **行の収縮**（Bhatt–de Jong 2011 Lemma 2.15–2.17）：pd Čech 脈体 D_0^• の余単体的加群 Ω^j_{D_0^•}（j ≥ 1）の収縮可能性。Ω^1 に基底ごとのホモトピーを作り、外冪・テンソル・完備化へ延ばす | なし | §3 の 6（W9-I-13 の訂正） |
| G-A1-15 | Lemma 5.4 の無限変数版：任意の多項式代数（自由 δ 環 B/p は δ^k(X) で無限個の変数）へ filtered 余極限で延ばす（原典 p.48 の議論、W9-I-16） | なし | §3 の 4・5 |
| G-A1-16 | **追加座標の Čech 因子の分離**（W9-I-18）：D^n ≅ (D_0^n ⊗_{Z_p} Q^{⊗(n+1)})^∧_p、E^• = Q^{⊗(•+1)} は retraction つき Čech 余脈体で収縮可能、D_0^• → D^• は擬同型 | G-A1-3 | §3 の 6 (ii) |
| G-A1-17 | **pd イデアル J つきの多項式の比較**（W9-I-19）：結晶 prism (B,(p)) と pd イデアル J ⊂ B、S = (B/J)[X] の持ち上げについて、J つき pd Čech 模型（B⟨X⟩ に差の pd 変数）の Tot ≃ 持ち上げの de Rham 複体、持ち上げの取り替えと多項式射についての自然性。Lemma 4.20 だけでは出ない（Δ の基底の底変換で、結晶側の J の変更ではない） | なし（A1-3 の補題として） | §9.1 の 2・3 |

## 5. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D25 | Thm 5.2 は Δ_{R^{(1)}/A} ≃ RΓ_crys(R/A)（大きい結晶 site のコホモロジー） | **β（2026-11-02 決定）**：E3 で使う形 Δ_{R^{(1)}/Z_p} ≃ Tot D^• ≃ Ω^•_{Z_p⟨X⟩}（RΓ_crys を既知の値で置き換えた特別な場合）で述べる。結晶 site は定義しない。α（結晶 site と RΓ_crys、pro 版の脚注 10）は β の上に後から足せる | E3 の経路で RΓ_crys を使うのは Thm 5.2 だけ。定理の特別な場合であり、定義は増やさない。**改訂（11-07、ユーザー）：結晶 site を必要最小限で原典どおり定義する（§11）。β の「結晶 site は定義しない」は撤回** |
| D26 | 微分形式は p 進形式スキームの（連続）Kähler 微分 | p 完備多項式代数について dX 上の自由加群として直接定義 | 原典の用法と同じ。Mathlib の `KaehlerDifferential` の p 完備化との一致は注記 |
| D27 | H^*(Ō_{X/A}) は位相の可換環対象のコホモロジーの環 | Čech–Alexander 模型の cup 積と Bockstein で与え、CAlg 値の Δ との一致は A2・A4 | A1 の定理は模型について述べる |
| D28 | 捻り {i}（I^i/I^{i+1}） | 向き付きなので落とす（原典 Constr 4.9 の最後の文） | 同じ |
| D29 | Prop 6.2 は r = 1、Thm 6.3 で Lemma 4.21 により一般へ | 最初から一般の r の多項式代数。Lemma 4.21 は使わない | 定理の範囲を多項式代数に絞る |
| D30 | Prop 6.2 の一般の有界 prism は普遍向き付き prism と、単体的可換環 E = A ⊗̂^L_{A_0} D_0 への底変換 | **一般の有界向き付き prism で行う（2026-11-02 決定）**。E は環として作らず、底変換関手 b̂^*・ĉ^* を通常の環の底変換と制限の合成として定義する（§0）。原典の議論と同じ関手で、導来環は出てこない | 数学は同じ。原典の E は記法上の装置で、使われるのは b̂^*・ĉ^* の性質だけ |

## 6. 単位と順序

| 単位 | 内容 | 前提 |
| --- | --- | --- |
| A1-1 | de Rham 複体（§2.1）と普遍性、模型の cup 積・Bockstein（§2.2）、η^*（Constr 4.9） | A0-2、G-A1-1・2・9 |
| A1-2 | 結晶側の対象（§2.3）：Lemma 2.36 の多変数（変数の場合）、pd 包 D^•、η : C^• → D^•、D^• = C^• ⊗_φ B^• | A0-3c、G-A1-6、T2-2（変数） |
| A1-3 | Lemma 5.4、Thm 5.2（特別な場合）、D25 の形の de Rham 比較、Cartier、Cor 5.5 | A1-2、G-A1-3・4・7・8、Lemma 4.20 |
| A1-4 | Construction 6.1、Prop 6.2（一般の r）、Thm 6.3、Cor 4.12、Lemma 4.10 | A1-3、A0-4（Lemma 4.20・4.22）、G-A1-4・5 |
| A1-6（11-07） | 結晶 site（最小限）：site・O_crys・RΓ_crys、(a) Čech–Alexander（pro）、(b) Poincaré 補題、(c) Thm 5.2 の多項式の場合、(d) 関手性（§11） | A1-3 の pd 模型（CrystallineInput）、S2・S3（pro 版を新設）、A2 の Δ_0 |

骨組みの順（2026-11-02 決定）：A1-1 → **A1-4** → A1-2 → A1-3。結晶側の話は最小限にする：A1-4 は結晶側の入力を一つの定理
`hodgeTate_iso_polynomial_Zp`（(Z_p,(p))・R = F_p[X_1,…,X_r] の Cor 5.5）に閉じ込め、A1-2・A1-3 はその証明だけを供給する。
結晶 site・crystal・RΓ_crys は定義せず（D25 β。**11-07 改訂：site と RΓ_crys は §11 で最小限に定義、crystal は定義しない**）、Thm 5.2 の一般の pd イデアル・結晶側の Frobenius の議論・Thm 6.4 の一般形は扱わない（多項式・mod p の特別な場合は A1-5、§9）。
A1-3 の de Rham 比較（§3 の 6）と Cartier は BS と独立な古典なので、別のファイルに分けて共有層へ出せる形にする（置き場所は調整役と相談）。

**結晶側に残るもの（最小限）**：(1) Lemma 5.4（余単体的代数、無限変数版 G-A1-15）、(2) pd 包の Čech 脈体 D^•/p の Tot ≃ Ω^•_{F_p[X]/F_p}（δ 座標なしの D_0^• で pd 微分の
pd-Poincaré 補題と j ≥ 1 の行の収縮 G-A1-14、D_0^• → D^• は追加座標の Čech 因子の収縮 G-A1-16）、(3) Cartier 同型（F_p[X]）、(4) 橋 η : C^• → D^• と D^• ≅ C^• ⊗_φ B^•（Lemma 2.36 の変数の場合）。
A5 の Lemma 8.6 が使う標数 p の de Rham 比較は (2) の W(k) への平坦底変換。

- **A1-5（2026-11-02、A5 の決定 3 で追加）**：de Rham 比較 Thm 6.4 の T = R⟨X_1,…,X_n⟩・mod p の特別な場合
  （φ_A^*Δ_{T/A} ⊗^L_A A/(p,d) ≃ Ω^•_{(T/p)/(R/p)}、E∞ 代数として、T → T_∞ と両立）。Lemma 8.6（A5-3）の入力。A1-4 の装置
  （Construction 6.1・普遍 prism）で原典 Thm 6.4 の証明を特別な場合に追う。結晶側の入力は増やさない。設計は A5-3 の骨組みの前に a1-design に追記。

## 7. 決定（2026-11-02、ユーザー）

1. **D-A1-1（D25）**（**11-07 改訂：§11 で結晶 site と RΓ_crys を最小限で定義**）：β。Thm 5.2 は E3 で使う形（Δ_{R^{(1)}/Z_p} ≃ Tot D^• ≃ Ω^•_{Z_p⟨X⟩}）の特別な場合として述べ、結晶 site は定義しない。
   「pd 包の Čech 脈体 ≃ de Rham 複体」（§3 の 6）を証明する。α は後から足せる。
2. **D-A1-2（D30）**：一般の有界向き付き prism で行う。導来テンソル E は環として作らず、b̂^*・ĉ^* を通常の環の底変換と制限の合成として
   定義する（§0・§3 の (c)）。普遍向き付き prism（G-A1-12）が範囲に入る。
3. **D-A1-3（D27）**：A1 の定理は模型（Tot(C^•/d) の cup 積・Bockstein）について述べてよい。**ただし必要な一般論を準備する**：
   余単体的可換環の cup 積と次数付き可換性（G-A1-1）、Bockstein（G-A1-2）、de Rham 複体の普遍性（G-A1-9）に加えて、
   CAlg 値の RΓ と模型の環構造の一致（G-A1-11）を一般論として用意し、A2 を待たずに模型と抽象的な Δ の環構造を結べるようにする。

## 8. 紙で確かめる項目

1. §2.3：D^n = (D_{(x)}(Z_p{x}) ⊗_{Z_p{x}} B^n)^∧ で、B^n が Z_p{x} 上平坦（自由）であること。Lemma 2.36 の多変数版で要るのは
   「Z_p{x, φ(x)/p} の生の pushout が p ねじれなし」（Lemma 2.11 の Frobenius の忠実平坦性、`FreeDeltaFrobeniusFlat`）。
2. §2.3：η : C^n → D^n が余単体的射で、D^n ≅ C^n ⊗_{B^n, φ} B^n（自由 δ 環の模型 C^n = Z_p{X^{(0)}, Y}^∧、z = pY の φ 底変換）。
3. §3 の 3：η^* と Cartier の一致（η^1(dX_j) = β(η^0(X_j)) が、Thm 5.2 と de Rham 比較を通して [X_j^{p−1}dX_j] に写ること）。Bockstein の
   符号と cup 積の規約を固定する。**未（11-07）**：§10 の段 6 `crystallineChain_generators` の TODO。Bockstein の両立そのものは比較写像が整係数の厳密な
   写像なので自動（`bockstein_natural`、段 4 は整係数の zigzag の mod p）。残るのは β_{D_0}[X^p] の段 4 での像が [X^{p−1}dX] であることの符号つきの計算。
4. §3 の 6：pd Čech 脈体と de Rham 複体の比較の、行の非輪状性（Tot_n Ω^j_{D_0^•} = 0、j ≥ 1）の証明の形（Bhatt–de Jong 2011 Lemma 2.15–2.17 の
   Ω^1 の収縮を有限変数・mod p で、外冪へ延ばす）。j = 0 の行は収縮しない（W9-I-13）。
8. §3 の 6 (ii)：D^n ≅ (D_0^n ⊗ Q^{⊗(n+1)})^∧_p の表示と余面・余退化の両立、E^• の extra degeneracy、G-A1-3 のテンソルでの保存（W9-I-18 の代案）。
5. §2.4：Construction 6.1 の (1)(2) の mod p 分解 (6) の各射の性質（A/d が p ねじれなし ⇒ d は A/p で正則；A/p の Frobenius 平坦；pd 包の自由性）
   と、perfect prism (A_inf(R), d) で R が p ねじれなしのとき仮定が満たされること。
6. §0・§3 の (c)：b̂^* = â^* ∘ Res_{A_0}、ĉ^* = â^* ∘ Res_{A_0} ∘ (⊗^L_{Z_p} A) の読み方が原典の E の議論と一致すること（テンソルの結合則、
   完備化との交換、Rem 4.19 の三つの底変換 A_0 → A、A_0 → D_0、Z_p → D_0 の両立）。
7. G-A1-12：A_0 の Frobenius の mod p 平坦性（F_p{d, δ(d)^{-1}} の Frobenius は多項式環の p 乗で自由、局所化と d 完備化で d 完全平坦）と、
   Construction 6.1 の (6) で要るのが「A/(p,d) → A/(p,d^p) が忠実平坦」であること（平坦かつ Spec の同相）。

## 9. A1-5：de Rham 比較の多項式・mod p の場合（原典 Thm 6.4、2026-11-02 追記）

概要：A5 の決定 3 で追加した単位。Lemma 8.6（A5-3）の入力：完全 prism (A,(d))（R = A/d perfectoid）と T = R⟨X_1,…,X_n⟩ について、
φ_A^*Δ_{T/A} ⊗̂^L_A A/(p,d) ≃ Ω^*_{(T/p)/(R/p)}（p 完備 de Rham 複体の mod p）を D(R/p) の可換代数の自然な同型として。
T_∞ = R⟨X_i^{1/p^∞}⟩ については T_∞ = (colim_m T_m)^∧（T_m = R⟨X_i^{1/p^m}⟩ は多項式）と Δ の filtered 余極限の可換性で、
φ^*Δ_{T_∞} ⊗ A/(p,d) ≃ colim_m Ω^*_{(T_m/p)/(R/p)} = T_∞/p（遷移写像 d(X^{1/p^m}) = d((X^{1/p^{m+1}})^p) = 0 が Ω^{≥1} を殺す）。
Lemma 8.6 で使う形：Δ_T ⊗_A A/(p, φ^{-1}(d)) = φ_A^*Δ_T ⊗_A A/(p,d)（φ_A は自己同型、A/φ^{-1}(d) ≅_φ A/d）。
原典 Thm 6.4 の証明は ψ : A → W(A/I)（標準射と Frobenius の合成）で (A,I) → (W(A/I),(p)) を作り、底変換と Thm 5.2（pd イデアル J）で
RΓ_crys に移し、結晶コホモロジーが持ち上げの de Rham 複体を持ち上げることで示す。技術的仮定「W(A/I) が p ねじれなし」（Cor 15.4 で除去）。

### 9.1 帰着の筋（A1-4 の装置で、D69）

**訂正（2026-11-02、Codex W9-I-15）**：以前の案「A_0 → D_0 の保存性で結晶 prism に帰着」は、比較射を先に構成しないと使えない（保存的関手は
指定した射の同値性を反映するが、底変換後に同型があることから元の同型は出ない。Prop 6.2 は η を先に選んでいる）。そこで帰着を次の形に直す：
1. 完全 prism ← 普遍向き付き prism A_0（Ex 3.4）：d の選択で A_0 → A、Cor 4.12／(4) で Δ_{T/A} = Δ_{T_0/A_0} ⊗̂_{A_0} A（T_0 = (A_0/d_0)⟨X⟩）、
   Frobenius と両立（δ 射）、de Rham 複体は底変換と両立。**A_0 上で構成した比較同型を底変換する**（保存性は使わない）。
2. A_0 上では**原典 Thm 6.4 の証明そのもの**を使う：A_0/d_0 は p ねじれなし（Ex 3.4、Construction 6.1 の仮定）なので W(A_0/d_0) も p ねじれなしで、
   Thm 6.4 の技術的仮定を満たす。ψ := F ∘ can : A_0 → W(A_0/d_0) は (A_0,(d_0)) → (W(A_0/d_0),(p)) の prism の射、底変換 (4) で
   Δ_{T_0/A_0} ⊗̂_{A_0,ψ} W(A_0/d_0) ≅ Δ_{T′/W(A_0/d_0)}（T′ = T_0 ⊗̂_{A_0/d_0,ψ̄} W(A_0/d_0)/p = (W/p)[X]、係数は ψ̄ で捻る）、これが結晶比較（Thm 5.2、
   pd イデアル J = ker(W(A_0/d_0) → A_0/(p,d_0))）で RΓ_crys((T_0/p)/W(A_0/d_0)) に。**最後に W → C := A_0/d_0 に沿う底変換を取る**（W9-I-20）：
   C = A_0/d_0、W = W(C)、w_0 : W → C として
   (Δ_{T_0/A_0} ⊗̂^L_{A_0,ψ} W) ⊗̂^L_{W,w_0} C ≃ RΓ_crys((T_0/p)/W) ⊗̂^L_W C ≃ Ω^*_{T_0/C}、
   w_0 ∘ ψ は A_0 の Frobenius の後に C へ射影する射なので左辺は φ_0^*Δ_{T_0/A_0} ⊗̂^L_{A_0} C。**比較同型は原典の構成で与えられる**。
   RΓ_crys の記号は原典との照合のためで、D25 β では J つき pd Čech 模型とその de Rham 計算（G-A1-17）で埋める。**11-07 改訂：RΓ_crys は §11 の
   `crystallineCohomology` として定義し、模型はそれを計算する定理 (a) の担い手（§11.3）。**
3. 結晶 prism (W(A_0/d_0),(p)) と多項式：Thm 5.2 β の使う形（Δ ≃ Tot D^•、D^• の Tot ≃ 持ち上げの de Rham 複体＝§3 の 6）を、Lemma 4.20
   （(p)-prism の Δ は任意の p 完備底変換と可換、A0-4）で Z_p に帰着。
4. （**11-07 注：D68 改訂で以下の黒箱は削除。HT は §10 の六段で直接、A1-5 の Thm 5.2 β は `wittSmallBridge_isInvertible`（旧 `wittPdBridge`）の中で Lemma 5.4 と導来 Nakayama から**）
   Z_p と F_p[X]：~~結晶の黒箱~~（A1-3）を de Rham の形で：φ^*Δ_{F_p[X]/Z_p} ≃ Ω^*_{Z_p⟨X⟩/Z_p}（Thm 5.2 β の使う形、可換代数として、多項式代数の
   射について自然、乗法的、Bockstein と両立——W9 の仕様）。mod p で Ω^*_{F_p[X]/F_p}。HT 比較（Cor 5.5、A1-3 の `hodgeTate_iso_polynomial_Zp`）は
   同じ黒箱と Cartier 同型（一変数は G-A5-12、n 変数は Künneth）から。**結晶の黒箱は一つのまま**（D68）。
   注（W9-I-19 で確定）：2 の pd イデアル J つきの比較は Z_p の黒箱と Lemma 4.20 だけでは出ない（Lemma 4.20 は Δ の基底の底変換で、結晶側の J の
   変更ではない）。黒箱は Z_p のまま一つに保ち、**J つきの多項式の比較とその自然性を A1-3 の独立補題 G-A1-17 として置く**（Codex の推奨）。

### 9.2 単位と形

| 項目 | Lean の形 | 既存・不足 |
| --- | --- | --- |
| ~~黒箱（de Rham 形）~~ | **11-05 夜の D68 改訂で削除**（`crystalline_deRham_polynomial_Zp`・`CrystallineComparison`）。§10 | — |
| Cor 5.5（HT） | `hodgeTate_iso_polynomial_Zp` の証明：§10 の六段（mod p の直接証明） | G-A5-12 の n 変数版 |
| Lemma 4.20 | (p)-prism の Δ の底変換 | A0-4（D、2b 後） |
| ~~結晶 prism の多項式~~ | `deRham_iso_polynomial_crystalline`：**11-07 削除**（どこからも参照されていない、黒箱にだけ依存） | — |
| A_0 上の比較同型 | `deRham_iso_polynomial_universal`（原典 Thm 6.4 の証明：ψ : A_0 → W(A_0/d_0)、底変換 (4)、Thm 5.2 β、持ち上げの de Rham） | W(A_0/d_0) の p ねじれなし（Ex 3.4）、A1-3 |
| 完全 prism | `deRham_iso_polynomial_modP`（A1-5 の主張） | 1 |
| T_∞ | `deRham_iso_rootAlgebra_modP`：φ^*Δ_{T_∞} ⊗ A/(p,d) ≃ T_∞/p | A5-4 の filtered 余極限、Ω の遷移の消滅 |
| 可換代数構造 | 全段を CAlg の同型として | Shared/DeRhamPolynomial の cdga → CAlg、G-A1-11 |

### 9.3 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D68 | 結晶の入力は Thm 5.2（結晶 site）と Cor 5.5 | ~~黒箱を Thm 5.2 β の de Rham 形一つにし、HT（Cor 5.5）と de Rham mod p の両方をそこから出す~~ **改訂（11-05 夜、ユーザー）**：黒箱を外し、使う側が要る対象ごとの `HodgeTateIsoStatement` を mod p で直接証明（§10）。A1-5 の Thm 5.2 β は W 上で Lemma 5.4 と導来 Nakayama から | 恒久の引用なし（段階 II は sorry 0） |
| D25（改訂、11-07） | Thm 5.2・Thm 6.4 の RΓ_crys は big crystalline site のコホモロジー | **結晶 site を最小限で原典どおり定義**（affine な対象、Zariski 位相、p 冪零、cutoff κ）。(a) Čech–Alexander・(b) Poincaré 補題・(c) Thm 5.2 の多項式の場合・(d) 関手性を定理に（§11） | 定義は原典どおり。差は要相談（§11.6）として D 番号を付けない |
| D69 | Thm 6.4 の証明は ψ : A → W(A/I) と pd イデアル、仮定「W(A/I) p ねじれなし」 | 原典の証明を**普遍向き付き prism A_0 上だけ**で行い（A_0/d_0 は p ねじれなしなので仮定が成り立つ）、完全 prism へは底変換 (4) で移す（W9-I-15 で訂正：以前の「保存性で帰着」は比較射を欠いていた） | 原典の証明そのもの。perfectoid R について W(R) の p ねじれを確かめる必要はない |

### 9.4 決定事項（相談）

Codex W9 の判定（2026-11-02）：1（D68）は「自然性・乗法・Bockstein との両立・T → T_∞ の根の遷移との両立を仕様に含めた一つの黒箱」で妥当、
J つきの比較は黒箱に入れず A1-3 の独立補題 G-A1-17 に。2（D69、訂正後）は妥当（W9-I-20 の最後の底変換を補う）。
**決定（2026-11-02、ユーザー）：1 は (a)（仕様つきの de Rham 黒箱一つ `crystalline_deRham_polynomial_Zp`、HT は Cartier で、J つきは G-A1-17）、2 は (a)（原典 Thm 6.4 の経路を A_0 上で、完全 prism へ底変換）。**

1. 結晶の黒箱を de Rham 形 `crystalline_deRham_polynomial_Zp` 一つにして、HT（`hodgeTate_iso_polynomial_Zp`）をそこから Cartier で導く（推奨、D68。
   仕様：多項式代数の射についての自然性、乗法、Bockstein との両立、根の遷移との両立。J つきの比較は G-A1-17）／de Rham 形を第二の黒箱として別に置く。
2. 帰着（D69、W9-I-15 で訂正後）：原典 Thm 6.4 の ψ・W(A_0/d_0) の経路を**普遍向き付き prism A_0 上で**行い、完全 prism へ底変換で移す（推奨。
   比較同型は原典の構成で与えられ、p ねじれなしは A_0 で成り立つ）／A_0 上で多項式模型から自然な比較射を別に構成してから保存性を使う（Codex の代案 (a)）／
   結晶側の同型の降下データ（Codex の代案 (b)）。

### 9.5 紙で確かめる項目

1. 9.1 の 1：Frobenius 捻りと底変換の両立（φ_{A_0}^* と ⊗_{A_0} A の交換、δ 射）。W9 で確認（○）。
2. 9.1 の 2：ψ : A_0 → W(A_0/d_0) が prism の射であること（ψ(d_0) ∈ (p)）、底変換 (4) の適用、T′ の形。
5. 9.1 の 2・3：pd イデアル J つきの Thm 5.2 が Z_p の黒箱と Lemma 4.20 から出るか（出なければ黒箱の仕様に含める）。
3. T_∞ の段：colim_m Ω^*_{T_m/p} = T_∞/p（Ω^{≥1} の遷移が零）、Δ の完備化した filtered 余極限との整合。
4. Cartier の n 変数版（Künneth）で Cor 5.5 を黒箱から出せること。

## 10. D68 改訂後の経路：(Z_p,(p))・F_p[X_1,…,X_r] の HT 比較を mod p で直接（2026-11-07）

概要：11-05 夜のユーザー決定（段階 II は sorry 0、D68 改訂）に従い、結晶の黒箱 `crystalline_deRham_polynomial_Zp`（関手 ∞ 圏の同型
`FunctorIso zpDelta zpForms`、仕様 4 欄の構造体 `CrystallineComparison`）を drafts から外した。使う側が要るのは対象ごとの命題
`HodgeTateIsoStatement`（Čech–Alexander 模型 Tot(C^•/p) の H^i で η^i が全単射）だけなので、これを mod p で直接示す。∞ 圏の部品は使わない。
調査は citations-survey-2026-11-05.md §1。
方針：比較はすべて余単体的可換環の厳密な射（または整係数の厳密な写像の mod p）で与える。cup 積は `cohomologyMap_cup` で、Bockstein は
`bockstein_natural` で自動的に移る。mod p なので導来 Nakayama（G-A1-4）は使わない。
規約：骨組みは drafts/A1/CrystallineInput.lean の後半。「cohomology 同型」は Shared の `Cosimplicial.IsCohomologyIso`（全次数で `cohomologyMap` が全単射）。
使われ方：`hodgeTate_iso_polynomial_Zp`（A1/HodgeTateComparison）＝ `hodgeTate_of_deRham_cartier`。

### 10.1 六段と宣言の対応

記号：k = ℤ_p（`crystallineBase`）、F_p（`cartierBase`）、C^• = `zpCech`（= `htRings`、Rem 4.19 の小さい模型）、C^•/p = `reducedModel`、
D^• = `pdDeltaRings`（`pdDeltaModel`、B^•{φ(z)/p}^∧）、D_0^• = `pdRings`（`pdModel`、δ 座標なし）、B^•/p = F_p[δ^a(X_j^{(i)})]。

| 段 | 内容 | 宣言（drafts/A1/CrystallineInput） | 一般論・紙 |
| --- | --- | --- | --- |
| 0 | mod p と cohomology 同型の道具 | `modPrimeCosimplicial`、`modPrimeMap`；Shared の `IsCohomologyIso`・`IsCohomologyIso.addEquiv`・`isCohomologyIso_of_isIso` | — |
| 1 | Lemma 5.4：標数 p の k、B = k[X_σ] の Čech 脈体 B^•（`polynomialCech`）と相対 Frobenius（`relativeFrobeniusCech`、X ↦ X^p）、余単体的可換環 N^• と ι : B^{•,(1)} → N^• について N^• → N^• ⊔_{B^{•,(1)}} B^•（項ごとの押し出し＝テンソル）は cohomology 同型 | `frobeniusTwist_cech_quasiIso`（σ 有限）、`frobeniusTwist_cech_quasiIso_infinite`（G-A1-15、filtered 余極限） | G-A1-3 |
| 2 | 橋 η : C^• → D^•（b ↦ φ(b)、z/p ↦ φ(z)/p）の mod p が cohomology 同型。D^n/p ≅ C^n/p ⊗_{B^n/p, φ} B^n/p（D^n ≅ C^n ⊗̂_{B^n,φ} B^n、p ねじれなし、完備化は mod p で消える）と段 1（N = C^•/p、σ = Fin r × ℕ） | `crystallineBridge`、`crystallineBridge_generator`、`crystallineBridgeModP`、`deltaCoordinatesModP`、`pdDelta_modP_frobeniusPushout`、`crystallineBridgeModP_isCohomologyIso` | §8 の 1・2 |
| 3 | D_0^•/p → D^•/p が cohomology 同型（追加の δ 座標の Čech 因子 E^• の extra degeneracy、mod p なので Rlim 不要） | `pdInclusion`（= `insertPdFactor` ≫ `splitDeltaCoordinates`⁻¹）、`pdInclusionModP`、`pdInclusionModP_isCohomologyIso` | G-A1-16、§8 の 8 |
| 4 | H^*(D_0^•/p) ≅ H^*(Ω^•_{F_p[X]})：D_0^•(ℤ_p)/p ≅ D_0^•(F_p)、双複体 K^{n,j} = Ω^j_pd(D_0^n)、列は pd Poincaré、j ≥ 1 の行は収縮、cup 積と外積が両立 | `pdModel_modP`、`pdDeRhamDifferential`（G-A1-7）、`pdDeRhamDoubleComplex`、`pdColumnInclusion`、`pdPoincare_column`（G-A1-7）、`pdRow_contractible`（G-A1-14、基底 k を一般に）、`pdDeRhamCohomologyIso`、`pdDeRhamCohomologyIso_cup` | G-A1-7・14、§8 の 4、§10.3 |
| 5 | n 変数の Cartier 同型（次数 0 は f ↦ [f^p]、次数 1 は dX ↦ [X^{p−1}dX]、乗法的） | `PolynomialCartier`、`cartierZeroClass`、`cartierOneClass`、`finitePolynomialCartier`；Shared の `DeRham.formsZeroEquiv`・`DeRham.deRhamCohomologyWedge` | G-A1-8、G-A5-12 の n 変数版 |
| 6 | 生成元での照合 Ψ^0(η^0 X_j) = C^{-1}(X_j)、Ψ^1(η^1 dX_j) = C^{-1}(dX_j)（Ψ は段 2〜4 の合成）と組み立て | `cartierFormsIso`、`crystallineChain`、`crystallineChain_cup`、`crystallineChain_generators`、`hodgeTate_of_deRham_cartier` | §8 の 3（**TODO：未**） |

組み立て（`hodgeTate_of_deRham_cartier`）：Φ^i := C^{-1} ∘ `cartierFormsIso` と Ψ^i ∘ η^i は加法的で外積を cup／外積に送り、次数 0（環の射、X_j で一致）と
次数 1（dX_j で一致）で一致するので全次数で一致。Φ^i・Ψ^i は同型なので η^i は全単射。

### 10.2 削除・変更した宣言

- 削除（CrystallineInput）：`crystalline_deRham_polynomial_Zp`、`CrystallineComparison`、`zpDelta`、`zpForms`、`liftedDelta`、`hModP`、`reductionBeta`、
  `isPrimeCompleteCAlg`、`rootTransition`。削除（DeRhamComparisonPoly）：`deRham_iso_polynomial_crystalline`（参照なし、黒箱にだけ依存）。
- 変更：`finitePolynomialCartier` の型を部分型（次数 1 の条件だけ）から構造体 `PolynomialCartier`（次数 0・1 と乗法性）に。`pdRow_contractible` の基底を
  ℤ_p から一般の k に（段 4 は F_p で使う）。`hodgeTate_of_deRham_cartier` は名前を保ち、黒箱ではなく段 1〜6 から。
- 残したもの：`formsCAlg` 系・`pdPolynomialComparison`（G-A1-17）・`extraCech_comparison`（整係数）・`polyPoint`・`changePolyNerve` は A1-5（D69）用。
  A1-5 の `wittSmallBridge_isInvertible`（旧 `wittPdBridge`、W = W(A_0/d_0) 上の Thm 5.2 β）は整係数で要る（C = A_0/d_0 は p ねじれなし）ので、段 1 の無限変数版（k = W/p）と
  導来 Nakayama（G-A1-4）をそこで使う。

### 10.3 段 4 の積（厳密な Alexander–Whitney）

段 4 の zigzag 行 0 → Tot K ← Ω^• を cup 積と両立させるには、総複体 Tot K に積を入れる：(x ⊗ ω) · (y ⊗ η) := ±(x ∪ y) ⊗ (ω ∧ η)。余単体の方向は
厳密な Alexander–Whitney（Shared の `cup`：前面・後面の引き戻しの積、鎖のレベルで結合的）、形式の方向は外積、符号は Koszul。Leibniz 則は
`cochainDifferential_cup` と pd 微分の Leibniz から。行 0 の包含と Ω^•（定数の余単体的対象を copy 0 に）の包含はどちらもこの積を保つ（鎖のレベル）。
可換性は cohomology でだけ要る（`cohomologyCup_comm`）。Bockstein の両立のため、同じ積と zigzag を ℤ_p 上の厳密な写像として作り mod p を取る。
**訂正（11-07、§10.5 の設計で気づいた）**：行 0 の包含 D_0^• → Tot K と、列への包含 Ω^• → Tot K は**鎖写像ではない**（前者は縦の pd 微分、後者は
横の交代余面の微分が消えない）。鎖写像になるのは逆向きの射影：Tot K → 行 0（j = 0 成分。縦の微分は j を上げるので鎖写像）と
Tot K → 列 0 = Ω^•_pd(D_0^0) = Ω^•（n = 0 成分。横の微分は n を上げるので鎖写像）。前者は核が j ≥ 1 の行の有限 filtration で擬同型
（`pdRow_contractible`）、後者は列がホモトピー的に定数（`pdPoincare_column`、全ての余面が H で同じ同型）なので擬同型。どちらも AW × 外積の積を保つ。
段 4 の zigzag は span D_0^• ← Tot K → Ω^•（`pdDeRhamCohomologyIso`・`pdDeRhamCohomologyIso_cup` の docstring を直した）。

### 10.4 D69 の貼り合わせ（`deRham_iso_polynomial_universal`）の高次の整合性

調べた結果：**今回の D68 改訂ではこの貼り合わせは不要にならない**（D69 側は黒箱を使っていなかった）。現在の型
`{ e : FunctorIso universalTwist (formsCAlg p residueU) // ∀ n, e.app (polyPoint _ n) = wittComposite p n }` は Fun(N(Poly(C)), CAlg_C) の
ホモトピー圏の同型で、成分の同型（`wittComposite`）と G-A1-17 の自然性（`natural`・`changeLift`、ホモトピー圏の等式＝ 1 単体まで）からは作れない。
自然変換は N(Poly(C)) × Δ¹ → CAlg_C の写像で、2 単体以上の整合性が要る。しかも J つき pd 模型は持ち上げ W[X] → W[Y] の選択に依存し
（C → W(C) に環の切断はない）、Poly(C) 上の厳密な関手になっていない。
要る ∞ 側の部品（貼り合わせを残す場合）：
1. 選択なしで厳密に関手的な模型：Poly(C) の各対象 Q に、Q の台集合を変数とする W 上の多項式環の Čech 脈体の J つき pd 包（A0 の大きい模型
   Constr 4.18 と同じ考え方）。比較写像は Q について厳密に自然な zigzag（Tot D_big(Q)^• → Tot Ω^•_pd(D_big(Q)^•) → Ω^•_{(Q/p)/(C/p)} など）。
2. `Cosimplicial.totEInfinityFunctor`（Shared、sorry）と、CommMon(Complex) 値の関手の厳密な自然変換から関手単体集合の辺を作る部品
   （脈体 N(𝒞 × [1]) ≅ N𝒞 × Δ¹ と `algebraCAlgSource` の後合成）。未作成。
3. 成分ごとに可逆な辺は可逆：本体 `functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise`（InfinityCategories/Core/FunctorEdgePointwise）。既存。
代案（要相談、未実施）：使う側は `transferWittComparison` → `deRham_iso_polynomial_modP` → `deRham_iso_rootAlgebra_modP`（→ A5 `rootMap_modP_eq_deRham`）で、
どれも `.app (polyPoint _ n)` の成分と根の遷移 X ↦ X^p の可換な四角形しか使わない。型を「各 n の `VertexIso` ＋ X ↦ X^p についてのホモトピー圏の自然性」に
弱めれば 1〜2 は要らない（filtered 余極限 T_∞ = colim T_m の比較には N(ℕ) 上の自然変換が要るが、N(ℕ) の背骨の包含は内側 anodyne なので
成分と四角形から作れる）。A1-5 の主張 `deRham_iso_polynomial_modP` の型が変わる（原典 Thm 6.4 の「自然な同型」の特別な場合）。
drafts では型を変えず、`deRham_iso_polynomial_universal`・`pdPolynomialComparison` に TODO の docstring を付けた。
**11-07 決定（ユーザー）：代案は採らず、関手としての同型のまま。部品 (i)〜(iii) の設計は §10.5。**

### 10.5 D69 の部品 (i)：選択なしで厳密に関手的な模型と zigzag（2026-11-07）

概要：11-07 のユーザー決定（D69 は `FunctorIso` のまま）に従い、`deRham_iso_polynomial_universal` を Poly(C) 上の**厳密な関手と厳密な自然変換**の
zigzag から作る。C = A_0/d_0（`residueU`）、W = W(C)（`WU`）、J = ker(W → C/p)（`wittPdIdeal`、γ = `wittPdStructure`）、Q ∈ Poly(C)、
Q^∧ = C⟨X_1,…,X_n⟩（A2 の `polyCompletion`）。
方針：**対象は選択してよい、射は普遍性の lift で一意**なら厳密に関手的（map_comp は lift の一意性から等式で出る）。今の `pdPolynomialFunctor` が
W 上で関手にならないのは、射 f の持ち上げ f̃ : W[X] → W[Y]（係数の持ち上げ）を選ぶからで、対象の選択のせいではない。したがって
(1) W・A_0 の上では Q^∧ の元すべてを変数にする**大きい枠**（x_q ↦ x_{f(q)}、BS 著者版 Construction 4.18 の考え方）を使い、
(2) C の上では Poly(C) の射を C 係数のまま代入できるので、**小さい模型 `pdModel C n` が厳密に関手的**（`pdPolynomialFunctor C`）。
de Rham 比較は (2) の上で行い、大きい枠の pd 形式（無限変数）は使わない。
規約：骨組みは drafts/A1/DeRhamComparisonPoly の「D69 の厳密に関手的な模型と zigzag」、一般の pd 部品は drafts/A1/CrystallineInput の
「A1-5（D69）用」、∞ 側の部品は drafts/Shared/CosimplicialEInfinity の末尾 3 節。
使われ方：`deRham_iso_polynomial_universal` → `transferWittComparison` → `deRham_iso_polynomial_modP`。

#### 10.5.1 一般の部品

| 部品 | 主張 | 宣言 |
| --- | --- | --- |
| J つき pd 包 | 基底 (k, J, γ)、J B ⊆ K のとき p 完備な J つき pd 包の普遍性と存在（Berthelot I.2.3.1 の p 完備化） | `IsCompletedPDEnvelope`、`exists_completedPDEnvelope` |
| 枠の pd Čech 脈体 | 枠 s : S → R̄ について D_S^n = ker(k[S × [n]] → R̄) の pd 包。対象は選択、θ は lift | `pdFrame`、`pdFrameEval`、`pdCechNerve`、`pdCechAugmentation` |
| 枠の射 | φ : S → D_{S′}^0（増大で s に移る）から D_S^• → D_{S′}^• | `pdCechNerveMap` |
| **表示によらない** | 二つの枠がどちらも R̄ を覆えば、枠の射は交代余面複体の擬同型。積の枠 S ⊔ S′ を通し、S ⊆ S ⊔ S′ では D_{S⊔S′}^• ≅ D_S^• ⊗̂ Γ_k(t)^{⊗(•+1)}（t = y − ℓ）の pd 多項式の Čech 因子の extra degeneracy（mod p^a ごと、Rlim）、(φ, id) と 2-out-of-3 | `pdCechNerveMap_quasiIso` |
| 小さい模型 | `pdModel k r` は枠 Fin r → (k/J)[X] の pd Čech 脈体（k 上自由なので γ は JD に延びる） | `pdModel_iso_pdCechNerve` |
| 厳密な自然変換 → 辺（(ii)） | F : 𝒞 ⥤ 𝒟 を持ち上げた形状からの射に、α : F ⟶ G を単体的ホモトピー（N(𝒞 × [1]) ≅ N𝒞 × Δ¹、本体の `NerveHomotopy.homotopy`）に、∞ 関手 T を後合成し、成分が可逆なら本体の `functorIsoOfPointwiseInvertibleHomotopy`（(iii)、`functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise` の系） | Shared：`strictShapeNerve`、`strictShapeNerve_comp`、`strictNatTransHomotopy`、`homotopyPostcomp`、`strictNatTransFunctorIso` |
| Tot と可逆性 | 交代余面複体の擬同型 ⇒ Tot_{E∞} の可逆な辺 | Shared：`totEInfinity_map_isInvertible` |
| 余単体的 cdga の Tot | n ↦ cdga の Tot_{E∞}、次数 0 では余単体的可換環の Tot と一致、[0] への射影（極限錐の脚）とホモトピー的に定数なら可逆 | Shared：`CosimplicialCDGA`、`cdgaCAlg`、`discreteCDGA`、`totCDGAFunctor`、`totCDGA_discrete`、`totCDGA_evalZero`、`totCDGA_evalZero_isInvertible` |
| Tot と係数 | Tot は係数制限と可換、厳密な α : F ⟶ G ⋙ g_* の随伴の転置（G の Tot は p 完備）、頂点での辺、厳密な射についての自然性 | Shared：`restrictCosimplicial`、`totEInfinity_restrict`；A1：`completeChange_comp`、`baseChangeTotHomotopy`、`baseChangeTotEdge`、`baseChangeTotHomotopy_vertex`、`baseChangeTotEdge_natural` |

#### 10.5.2 zigzag の段（すべて Poly(C) 上で厳密に自然）

| 段 | 主張 | 厳密な関手性の理由 | 宣言 |
| --- | --- | --- | --- |
| 0 | universalTwist = Δ_0 ≫ completeChange(q ∘ φ) ≅ Δ_0 ≫ completeChange ψ ≫ completeChange w_0 | `wZero_psi`（w_0 ∘ ψ = q ∘ φ）と係数変換の合成 | `completeChange_comp` |
| 1 | Δ_0 ≅ Tot_{E∞} C_big(−)^•（大きい Čech–Alexander 模型） | C_big(Q)^n は A0 の `cechAlexander`（R = Q^∧）。f は x_{(q,i)} ↦ x_{(f̂q,i)} の envelope の lift | `bigCechAlexander`、`polyUnderlying_iso_bigCech` |
| 2 | 結晶の橋 β：C_big(Q)^• → ψ_* D_W(Q)^•（x ↦ φ(x) = x^p）、転置して completeChange ψ ∘ Tot C_big ⟹ Tot D_W | D_W(Q)^• は大きい枠 W[x_q] → Q^∧/p（係数は w_0）の J つき pd Čech 脈体。D_W(Q)^n は結晶 prism（p ねじれなし、δ は BS Lemma 2.38 の議論）、β は envelope の lift | `wittBigPdModel`、`wittBigCrystalline`、`wittBigBridge`、`baseChangeTotHomotopy` |
| 3 | D_W(Q)^• → (w_0)_* D_0(C, Q)^•（x_{(q,i)} ↦ copy i の q）、転置して completeChange w_0 ∘ Tot D_W ⟹ Tot D_0(C) | w_0 は pd 射 (J, γ) → (pC, 標準)、枠の射は Q^∧/p 上で両立、右辺 `pdPolynomialFunctor C` は C 係数のまま代入 | `residuePdStructure`、`wZero_isDPMorphism`、`wittToSmall` |
| 4 | Tot_{E∞} D_0(C, −)^• ≅ Ω̂^•_{(−)/C}（`formsCAlg`） | C 上の小さい模型と余単体的 cdga K(Q)^n = Ω^•_pd(D_0^n) は Poly(C) について厳密に関手的 | CrystallineInput：`pdDeRhamCDGA`、`pdDeRhamProjection`、`pdDeRhamZeroIso`、`formsCAlg_eq`、`pdDeRhamFunctorIso` |

組み立て：`bigZigzagIso` = 段 0 ≪≫ 段 1 ≪≫ 段 2 ≪≫ 段 3 ≪≫ 段 4（段 2・3 は `functorIsoOfPointwiseInvertibleHomotopy`、結合は `functorIsoOfEq`）。
段 4 の中身：Tot D_0 ≅ Tot(D_0 を次数 0 の cdga に)（`totCDGA_discrete`）← Tot K（行 0 への射影 `pdDeRhamProjection`、`strictNatTransFunctorIso`）→
K^0（`totCDGA_evalZero` の前合成）≅ Ω̂（`pdDeRhamZeroIso`）。

#### 10.5.3 Ω^*_{Q/C} へつなぐ写像（決定）

候補「pd 包 D(Q) → Q（C の (p) の標準 divided powers）と Ω^*_{D(Q)} → Ω^*_{Q/C}」は、段 3 の `wittToSmall` の第 0 項 D_W(Q)^0 → D_0(C,Q)^0 = C⟨X⟩ = Q^∧
としてそのまま入る（C は p ねじれなしなので γ_n(px) = p^n x^n/n! ∈ pC が pd、w_0 は pd 射）。ただし**形式は大きい枠の上では作らない**：
段 3 で C 上の小さい模型へ移ってから、有限変数の pd 形式で de Rham 比較（段 4）を行う。理由：(a) 大きい枠の Ω_pd は無限変数で、pd Poincaré・
行の収縮を無限変数でやり直す必要がある、(b) C 上では小さい模型が厳密に関手的なので大きい枠は要らない、(c) 既存の `pdRow_contractible`（一般の k）・
`pdPoincare_column`（一般の k へ）がそのまま使える。de Rham 側は W を経由しない（W 上の持ち上げ W⟨X⟩ の de Rham 複体は関手的でない）。
段 4 の span の向き：行 0・列 0 の**包含**は鎖写像でないので、総複体からの**射影**二つを使う（§10.3 の訂正）。列 0 への射影は Tot_{E∞} では
極限錐の [0] の脚で、K がホモトピー的に定数（pd Poincaré）なら可逆。

#### 10.5.4 `wittComposite` の扱い（決定：大きい模型を通る形に定義し直す）

`wittComposite n := (bigZigzagIso p).app (polyPoint _ n)`、`deRham_iso_polynomial_universal := ⟨bigZigzagIso p, fun _ => rfl⟩`。
理由：旧定義（小さい模型の四本の脚 `WittComparisonLegs`：regroup・crystalline・pd・liftChange）は psiBaseChange（Cor 4.12 の抽象的な同型）と
`wittPdBridge`（VertexIso の存在）を含み、zigzag の成分と一致することを示すには抽象的な同型の中身を開く必要がある。一方、成分の可逆性は
いずれにせよ小さい模型との四角形（10.5.5）で示すので、成分を zigzag で定義すれば一致の証明は要らない。型の条件は文書としての役割
（成分がどの構成かを固定する）だけになる。旧 `WittComparisonLegs`・`wittComparisonLegs`・`wittPdBridge` は削除（`psiBaseChange` は残し、
`wittSmallBridge_isInvertible` の証明に使う）。

#### 10.5.5 各対象での可逆性（小さい模型の結果を移す）

各 Q = ⟨n⟩ で選択なしに取れる枠の射（Q について自然ではない、各対象でだけ使う）：
- 段 2：`cechAlexanderFrame`（Rem 4.19 の小さい模型 `polyCosimplicialAlgebra` → C_big(Q)、X_j ↦ x_{X_j}、両方とも Δ の Čech 脈体なので Tot で可逆）、
  `wittSmallFrame`（pdModel W n → D_W(Q)、`pdCechNerveMap_quasiIso`）、小さい橋 `wittSmallBridge`（X ↦ X^p、基底 ψ）と四角形 `wittBridge_frame_comm`
  （envelope の一意性：両辺とも X^{(i)} ↦ x_{(X,i)}^p）。小さい橋の可逆性 `wittSmallBridge_isInvertible` が数学の中身（psiBaseChange、
  `cechAlexanderAffine_baseChange`、W 上の Thm 5.2 β：Lemma 5.4 の無限変数版 k = W/p、G-A1-16、導来 Nakayama G-A1-4）。→ `wittBigBridge_isInvertible`。
- 段 3：`wittToSmall_frame`（wittSmallFrame ≫ wittToSmall = `pdModelBaseChange`、X ↦ x_X ↦ X）、`pdModelBaseChange_isInvertible`
  （W 上と C 上の段 4 の span は係数変換と厳密に可換、Ω̂_{W⟨X⟩} ⊗̂ C = Ω̂_{C⟨X⟩} は各次数有限自由で有界）→ `wittToSmall_isInvertible`。
- 段 4：`pdDeRhamProjection_isInvertible`（j ≥ 1 の行の収縮）、`pdDeRham_homotopicallyConstant`（pd Poincaré）。
小さい橋の写し方（X ↦ X^p で、原典の b ↦ φ(b) = X^p + pδ(X) ではない）は問題ない：どちらも (T′/W)_Δ の余単体的対象の射なので、Tot の上では
site の RΓ からの制限として同じ類（S3 の制限の自然性）。

#### 10.5.6 要相談（原典との差・設計の未決、D 番号なし）

1. A2 の `PolyDeltaData` に「大きい Čech–Alexander 模型の Tot との FunctorIso」の欄を持たせるか。A2 の docstring は「∞ 関手としての整合性は
   大きい模型の厳密な関手性から」と書くが、今の欄（val・obj_eq・map_eval）からは段 1 の同型が出ない。構成は大きい模型の Tot の頂点を RΓ に
   差し替える（Joyal の isofibration Fun(K,X) → Fun(sk_0 K, X)、本体の名前は未確認）。
2. **（11-07、§11 で解消：模型は RΓ_crys を計算する定理 (a) の担い手）** 大きい枠 W[x_q | q ∈ Q^∧] の J つき pd Čech 模型は原典にない（原典 Thm 6.4 は結晶 site の RΓ_crys で、関手性は site から来る）。
   D25 β（結晶 site を pd Čech 模型で代える）の延長で、Construction 4.18 の考え方を結晶側に転用したもの。
3. 一般の J つき pd 包（`IsCompletedPDEnvelope`・存在）と「表示によらない」補題は Mathlib にない古典（Berthelot）。BS は当然として使う。
4. **削除した（11-07、ユーザー決定）**。旧 `pdPolynomialComparison`・`PDPolynomialComparison`・`pdTotMap`（1 単体までの自然性）は D69 の経路から使われなくなった。削除するか。
5. 宇宙と cutoff：`bigCechAlexander` は Q ごとの `polyCutoff` を使う（値は A_0 代数なので関手は作れる）。Q^∧ の濃度は n によらないので共通の
   cutoff にしてもよい。
6. 基盤待ち：`totEInfinityFunctor`・`totCDGAFunctor`（McClure–Smith／Berger–Fresse の E∞ 構造）、`cAlgBaseChange` とその随伴の関手 ∞ 圏への延長。

#### 10.5.7 紙で確かめる項目

1. D_W(Q)^n の p ねじれなしと δ 構造（Lemma 2.38 の議論、J = VW + pW は単項でない）。
2. β の存在：J_0（`cechKernel`）の像が pD に入る（z ∈ K̄ ⇒ φ(z) ∈ pD、δ 閉包も）。Q^∧ → D/p（q ↦ x_q^p）が環の射。
3. 表示によらない補題の無限変数・p 完備化（mod p^a ごとの収縮と Rlim）。D_{S⊔S′} ≅ D_S⟨t⟩ の変数変換が余単体的構造と両立すること。
4. w_0 が pd 射：γ_n(Vx) = (p^{n−1}/n!) V(x^n) ↦ 0、γ_n(p) ↦ p^n/n!（p = 2 も）。
5. 列 0 への射影の擬同型（ホモトピー的に定数な余単体的複体の Tot）、射影が AW × 外積の積を保つこと。
6. `pdModelBaseChange_isInvertible`：Tot と完備底変換の交換を de Rham の span で示せること（両辺の span が係数変換と厳密に可換）。

## 11. 結晶 site（最小限）（2026-11-07、ユーザーの方針変更）

概要：11-07 のユーザー決定「crystalline site も必要最小限で作りましょう。方針変更です。」により、D25（11-02、Thm 5.2 の β 形：RΓ_crys を定義しない）を改め、
Berthelot の結晶 site を**必要最小限で原典どおり**定義する。目的は、Thm 6.4 の比較同型（D69 の `deRham_iso_polynomial_universal`）の各段を、原典どおり
「RΓ_crys とその site の関手性」で読めるようにすること。§10.5 の厳密な模型は「RΓ_crys を計算する」という定理の担い手として残す。
方針：定義は原典どおり（BS 著者版 Thm 5.2 の証明の「big crystalline site (R/A)_CRYS as in [Ber06, §III.4]」、affine な対象）。定理は E3 に要る特別な場合だけ
（(a) Čech–Alexander 型の計算、(b) 多項式の Poincaré 補題、(c) Thm 5.2 の多項式の場合、(d) R̄ と基底についての関手性と模型の射との一致）。
計算用の模型（§10.5 の `wittBigPdModel`・`pdModel`）は「RΓ_crys を計算する」定理にする。
規約：骨組みは drafts/A1/CrystallineSite.lean（新設、単位 A1-6）。S3 の pro 版（`exists_limitCone_of_proCech`）も当面そのファイルの先頭に置き、中身の段階で
drafts/Sheaves/CechConerveLimit.lean へ移す。参照：Stacks Project の Crystalline Cohomology の章（Tag 07GI）の §5（07HL）・§18（07JI）・§21（07LE）。
使われ方：A1-5（§9・§10.5）の各対象での可逆性の証明の読み方（§11.3）。D68 の経路（§10）は使わない（§11.5）。

### 11.1 最小限の範囲：原典の項目との対応

| 原典の項目 | 扱い | 形（drafts/A1/CrystallineSite） | 原典との差 |
| --- | --- | --- | --- |
| site の対象（[Ber06 §III.4] の (U, T, δ)、BS の (D/p^n → R′ ← R)） | **そのまま定義（affine な対象）** | `CrysOver`：k 代数 B、J_B と δ、k → B は pd 射、p は B で冪零、R̄ → B/J_B（Stacks Tag 07HM の CRIS(C/A)） | T は affine に限る（§11.6 の 1） |
| U = Spec R 全体に限る小さい site（Stacks の Cris(C/A)、R̄ ≅ B/J_B） | **採らない** | — | BS の (D/p^n → R′ ← R) は R′ ≠ R で小さい site に入らず、f : R̄ → R̄′ の引き戻し関手もない。big site なら `crysPullback` が厳密な関手 |
| [Ber06 Prop III.4.1.4]（big と small の比較） | 不要 | — | RΓ_crys を big site で定義するので比較を使わない |
| 位相（Zariski） | **そのまま定義** | `zariskiTopology`（有限個の局所化 B → B_{f_i}、(f_i) = B の族が生成） | affine な対象の上の Zariski 被覆（§11.6 の 2） |
| RΓ が位相によらないこと | 定理 | `crystallineStructure_isSheaf`（Stacks Tag 07JJ の O の場合）、`crystallineCohomology_isLimit`（RΓ = lim O ＝ chaotic 位相の RΓ、Stacks Tag 07JK の C） | — |
| étale 位相 | 不要 | — | — |
| 基底 (W(A/I), J, 標準の divided powers) | 既存の定義を使う | `wittPdIdeal`・`wittPdStructure`（A1/DeRhamComparisonPoly）。一般には (k, J, γ)、p ∈ J | — |
| J と p の divided powers の両立 | 既存の sorry の中（`wittPdStructure`：VW と p の標準 divided powers は共通部分で一致）。W は p ねじれなしなので γ_n(p) = p^n/n! は一意 | Berthelot の「γ と両立」は J B ⊆ J_B のもとで k → B が pd 射であることと同じ（R̄ が k/J 代数なので自動） | — |
| (C, (p), 標準) と w₀ が pd 射 | 既存 | `residuePdStructure`・`wZero_isDPMorphism` | — |
| 大きさ | A0 と同じ cutoff | `IsCrystallineCutoff k R̄ κ`（κ ≥ `cutoff k R̄`）、枠の添字 #S ≤ κ。A1-5 では Poly(C) 全体で κ := cutoff W W | 宇宙は上げない。κ 不変性は使わない（κ を固定、§11.6 の 6） |
| 構造層 O_crys | そのまま定義 | `crystallineStructureRing`（B ↦ B）、`crystallineStructure`（CAlg_k 値） | — |
| RΓ_crys(R̄/k) := RΓ(site, O_crys) | そのまま定義 | `crystallineCohomology`（Sheaves の `derivedGlobalSectionsCAlg`、A2 の Δ と同じ入力） | 値は CAlg_k（D(k) 値は忘却） |
| (a) Čech–Alexander（pro 対象 {D/p^n} が弱終、余積、[Ber06] の計算） | 定理（全射な枠 S → R̄） | `pdCechTower`・`pdCechTower_proWeaklyTerminal`・`totEInfinity_isLimit_truncations`・`crystallineCechIso`；一般論 `exists_limitCone_of_proCech` | 対象は p 冪零なので弱終なのは pro 対象（BS p.45–46、Stacks Tag 07HP・07JL・07JN） |
| (b) 多項式の場合の Poincaré 補題（RΓ_crys は持ち上げの de Rham 複体） | 定理（R̄ = (k/J)[X]） | `crystallineCohomology_polynomial_deRham`（Stacks Tag 07LG の F = O） | — |
| (c) Thm 5.2（I ∋ p、多項式の場合） | 定理 | `pdDeltaCechNerve`（δ 変数つきの D^• = B^•{φ(J₀)/p}^∧）、`etaBridge`（原典の η、b ↦ φ(b)）、`pdDeltaRetraction`（δ 変数の収縮、`_quasiIso`）、`crystallineComparison_polynomial`；`crystallineBridge_eq_eta`（D68 の η はその (ℤ_p,(p)) の場合）；`frobeniusPdBridge`（= η ≫ ρ、X ↦ X^p）・`frobeniusPdBridge_tot` | 比較写像は原典の η（§11.6 の 3、11-07 決定）。Frobenius との両立は述べない |
| (d) R̄ についての関手性 | 辺の定義と定理 | `crysPullback`・`crysPullbackSite`・`crystallineCohomology_map`・`crystallineCohomology_map_comp`・`crystallineCohomology_map_frame` | ∞ 関手としての RΓ_crys は置かない（§11.4、§11.6 の 4） |
| (d′) 基底についての関手性（W(C) → C） | 辺の定義 | `crysBaseRestriction`・`crystallineCohomology_baseChangeEdge`；多項式での可逆性は既存の `pdModelBaseChange_isInvertible` | — |
| crystal、一般の O_{X/S} 加群、Frobenius の RΓ_crys への作用、Thm 5.2 の一般の smooth R・Frobenius との両立 | 不要 | — | E3 で使わない |

### 11.2 置いた宣言（drafts/A1/CrystallineSite.lean、48 宣言・sorry のある宣言 40。11-07 の η への書き直しで +8 宣言・+5）

- S3 の pro 版（名前空間 `InfinityCategories.Sheaves`）：`IsProWeaklyTerminal`、`ProCechNerveData`、`proCechIndexFunctor`（＋`_obj`）、`proCechShape`、`exists_limitCone_of_proCech`。
- site：`IsCrystallineCutoff`、`CrysOver`（＋`Hom`・圏・`IsZariskiFamily`・`essentiallySmall`）、`CrysOverSmall`、`CrystallineSite`、`zariskiTopology`、`crysAlgebras`、
  `crystallineStructureRing`、`crystallineStructure`、`crystallineStructure_isSheaf`、`crystallineCohomology`、`crystallineCohomology_isLimit`。
- 関手性：`crysPullback`、`crysPullbackSite`、`crystallineCohomology_map`、`crystallineCohomology_map_comp`、`crysBaseRestriction`、`crystallineCohomology_baseChangeEdge`。
- (a)：`crysResidueAlgebra`、`crysResidue_kernel`、`pdCechNerveIdeal`・`pdCechNerveDP`・`pdCechNerve_isDPMorphism`（`pdCechNerve` の選択の pd 構造を取り出す）、
  `pdCechTower`、`pdCechTower_proWeaklyTerminal`、`totEInfinity_isLimit_truncations`、`crystallineCechIso`、(d) の `crystallineCohomology_map_frame`。
- (b)：`crystallineCohomology_polynomial_deRham`。(c)：`crysPolynomial`、`polyPdCech`、`deltaCechVariable`、`pdDeltaCechNerve`、`etaBridge`、
  `pdDeltaRetraction`、`pdDeltaRetraction_quasiIso`、`frobeniusPdBridge`（合成で定義、sorry なし）、`frobeniusPdBridge_tot`、`crystallineComparison_polynomial`、
  `crystallineBridge_eq_eta`。
- 結論が `True` の仮置き・仮定の `True` はない。既存ファイルは編集していない（CrystallineInput も）。

### 11.3 D69（Thm 6.4）の筋の書き直し：原典の文と §10.5 の段

原典 Thm 6.4 の証明は「Δ_{R/A} ⊗̂_{A,ψ} W(A/I) ≃ RΓ_crys((R/p)/W(A/I))（底変換 Cor 4.12 ＋ Thm 5.2 を pd イデアル J で）」と「RΓ_crys((R/p)/W(A/I)) は
Ω_{R/(A/I)} を持ち上げる（結晶コホモロジーの一般論）」の二つ。A₀ 上（§9.1）で、Q ∈ Poly(C)、R̄_Q := Q^∧/p = (C/p)[X] = (W/J)[X] とすると
§10.5.2 の段はそれぞれ次の原典の文を厳密な模型で実現したものになる：

| 段 | 原典の文（RΓ_crys で） | 厳密な模型（§10.5、残る） | 各対象での可逆性の読み方（新） |
| --- | --- | --- | --- |
| 0 | q ∘ φ = w₀ ∘ ψ | `completeChange_comp`・`wZero_psi` | 変更なし |
| 1 | Δ_0 の関手性（prismatic site） | `polyUnderlying_iso_bigCech`（A2 の `PolyDeltaData` の欄） | 変更なし |
| 2 | Δ_{Q^∧/A₀} ⊗̂_ψ W ≃ RΓ_crys(R̄_Q/W) | `wittBigBridge`：C_big(Q)^• → ψ_* D_W(Q)^•、D_W(Q)^• = `wittBigPdModel`（大きい枠 Q^∧ → R̄_Q の pd Čech 脈体） | (a)：Tot D_W(Q)^• ≃ RΓ_crys(R̄_Q/W)（`crystallineCechIso`、枠 S = Q^∧）。`wittSmallFrame_isInvertible` は (d) で f = id（二つの枠がどちらも RΓ_crys を計算し、枠の射が site の射と一致）。`wittSmallBridge_isInvertible` は `psiBaseChange`（Cor 4.12）と (c) を (A, I) = (W, J) で（η の形の (c) を `frobeniusPdBridge_tot` で X ↦ X^p の `wittSmallBridge` に読む） |
| 3 | RΓ_crys(R̄_Q/W) ⊗̂_{W,w₀} C ≃ RΓ_crys(R̄_Q/C)（基底 (W,J) → (C,(p)) の pd 射に沿う底変換） | `wittToSmall`：D_W(Q)^• → (w₀)_* D_0(C,Q)^• | 辺は `crystallineCohomology_baseChangeEdge`（g = w₀）の転置。D_0(C,Q)^• = `pdModel C n` は小さい枠の pd Čech 脈体（`pdModel_iso_pdCechNerve`）なので (a) で RΓ_crys(R̄_Q/C) を計算。可逆性は `pdModelBaseChange_isInvertible`（模型の定理）と (d) |
| 4 | RΓ_crys(R̄_Q/C) ≃ Ω̂^•_{Q^∧/C}（Poincaré 補題） | `pdDeRhamFunctorIso`（k = C） | 各成分は (b)（`crystallineCohomology_polynomial_deRham`、k = C、J = (p)） |

**§10.5 のうち残るもの**（「RΓ_crys を計算する」定理の担い手、∞ 関手としての高次の整合性の出どころ）：`bigCechAlexander`、`wittBigPdModel`、`wittBigCrystalline`、
`wittBigBridge`、`wittToSmall`、`pdPolynomialFunctor`、`pdDeRhamCDGA` 以下の段 4、`baseChangeTotHomotopy` 系、Shared の厳密な自然変換の部品、`bigZigzagIso`、
`wittComposite`、`deRham_iso_polynomial_universal`（型は変えない）、各対象の `cechAlexanderFrame`・`wittSmallFrame`・`wittSmallBridge`・`pdModelBaseChange` と四角形。
**要らなくなるもの・軽くなるもの**：
1. `pdCechNerveMap_quasiIso`（表示によらない、積の枠と pd 多項式の Čech 因子の extra degeneracy・mod p^a ごとの収縮と Rlim）：(a)＋(d) の系になる（BS 著者版 Thm 5.2 の
   「this recipe is independent of the choice of (B₀ → R)」の原典どおりの理由）。主張は残し、証明の筋を site に差し替える（11-07 決定、§11.6 の 5）。変数変換
   D_{S⊔S′} ≅ D_S⟨t⟩^∧ は `wittBigCrystalline` の p ねじれなしに残る。
2. §10.5.6 の要相談 2（「大きい枠の J つき pd Čech 模型は原典にない」）：解消。模型は原典の定義 RΓ_crys を計算する定理 (a) の担い手になった。
3. §10.4 の代案・§10.5.4 の決定は変わらない（`wittComposite` は zigzag の成分のまま）。
4. `extraCech_comparison`（G-A1-16）：D_0^• と δ 変数つきの D^• がどちらも RΓ_crys を計算する（big site の対象 (D/p^e → R′ ← R)）ので site の系にもできるが、
   既存の extra degeneracy の証明は短いのでそのまま（どちらでもよい）。一般の基底の版が (c) の `pdDeltaRetraction_quasiIso`。

**(c) の形（11-07 決定、§11.6 の 3）**：比較写像は原典の η。一般の基底 (A, I, γ_I)（A は結晶 prism で生成元 p、有界）について
`etaBridge` : C^• = `polyCosimplicialAlgebra P hP r`（Rem 4.19）→ D_δ^• = `pdDeltaCechNerve`（B^• = A{X^{(0..•)}}^∧ の J₀ = I B + (X^{(i)} − X^{(0)}) の
γ_I と両立する p 完備な pd 包、Cor 2.39 の形 B^•{φ(J₀)/p}^∧）、b ↦ φ(b)。`crystallineComparison_polynomial` の結論は
Δ ≃ Tot C^• →(Tot η) Tot D_δ^• →(Tot ρ) Tot D^• ≃(a) RΓ_crys の合成が同型。D68 の `crystallineBridge` は (A, I) = (ℤ_p, (p)) の場合
（`crystallineBridge_eq_eta`：`pdDeltaModel` ≅ `pdDeltaCechNerve` のもとで一致。一般の η が本体で crystallineBridge はその特殊化だが、
CrystallineInput は CrystallineSite より前なので crystallineBridge は独立の定義のまま、関係を CrystallineSite の補題で述べる）。

**(a) とのつなぎ方**：D_δ^• は big site の対象 (D_δ^0/p^e, R̄ → R′ = B/J₀B ≠ R̄) の Čech 脈体だが、(a) は全射な枠 k[S] → R̄ の pd Čech 脈体についての定理。
二案：(i) δ 変数つきの {D_δ^0/p^e} を弱終な pro 対象として (a) をもう一つ置く（塔・各段の pd 構造・弱終性・同型の 4〜5 宣言）、
(ii) δ 変数なしの枠と比較する補題を置く。**(ii) を採った**：δ 変数の収縮 ρ = `pdDeltaRetraction` : D_δ^• → D^•（δ^a(X) ↦ 0、a ≥ 1）と
その擬同型 `pdDeltaRetraction_quasiIso`（G-A1-16 の一般の基底の版：D_δ^n ≅ D^n ⊗̂ E^n、E^• の extra degeneracy）の 2 宣言で済み、証明は
ℤ_p の `extraCech_comparison`・D68 の段 3 と同じ型で既にある。(a) は全射な枠の版だけでよい。

**X ↦ X^p の写像**：旧 `frobeniusPdBridge` は A1-5 の `wittSmallBridge`（δ 変数なしの `pdModel W n` へ、X ↦ X^p）と `wittBridge_frame_comm` が使うので、
η からの計算として残した：`frobeniusPdBridge := etaBridge ≫ pdDeltaRetraction`（ρ(φ(X)) = X^p）、`frobeniusPdBridge_tot`（Tot の類は Tot η ≫ Tot ρ）。
`wittSmallBridge` の型は変えない。

### 11.4 自然性：site の関手性が与えるもの・与えないもの

- 与えるもの：頂点（各 Q の RΓ_crys(R̄_Q/W)・RΓ_crys(R̄_Q/C)）と辺（`crystallineCohomology_map`：R̄ の射、`crystallineCohomology_baseChangeEdge`：基底の pd 射）、
  ホモトピー圏での関手則（`crystallineCohomology_map_comp`）、そして厳密な模型の射がその辺に一致すること（`crystallineCohomology_map_frame`）。
  big site なので R̄ → R̄′ の引き戻し `crysPullback` は厳密な関手（関手則は rfl）。
- 与えないもの：関手 ∞ 圏 Fun(N(Poly C), CAlg) の頂点としての Q ↦ RΓ_crys(R̄_Q)（2 単体以上の整合性）。site の族から ∞ 関手を作るには「厳密な site の族の上の
  極限の関手性」（Grothendieck 構成と右 Kan 延長）の基盤が要り、今の Sheaves にない。Δ_0（A2 の `PolyDeltaData`）と同じく、∞ 関手は厳密な模型から nerve で作り、
  site はその頂点と辺の意味を与える。D69 の `FunctorIso` の型と `bigZigzagIso` の組み立ては変えない（§11.6 の 4）。

### 11.5 D68（§10、HT の直接証明）への影響

なし。§10 の六段は (Z_p,(p))・F_p[X] の Čech–Alexander 模型の mod p の cohomology 同型で、RΓ_crys を通らない。A1/CrystallineInput の宣言（`pdModel`・`pdRow`・
`withExtraCoords`・`pdDeRhamFunctorIso` など）は変更せず、CrystallineSite はそれを import して使うだけ。共有するのは Lemma 5.4（`frobeniusTwist_cech_quasiIso_infinite`）で、
(c) の証明でも使う（重複しない）。段 2〜4 は (c)・(a)・(b) の (Z_p,(p)) の場合の mod p の読み替えにもなるが、§10 の証明は書き換えない。

### 11.6 要相談（原典との差・設計の未決、D 番号なし）→ 11-07 に 1〜6 とも決定（design-status §0.3.1 の末尾）

1. **affine な対象に限る**（Berthelot の (U, T, δ) は一般の T）。**決定（11-07）：限る**。理由：BS 自身が affine で議論し（「enough to solve the problem in the affine case」）、
   prismatic site（Def 4.1 の扱い）と同じ。全体の site との比較（Stacks Tag 07JK の special cocontinuous の議論）は E3 で使わないので証明しない。
2. **位相**：Zariski（原典どおり）／indiscrete（chaotic）。**決定（11-07）：Zariski**。Zariski で定義し、O_crys が層であること（`crystallineStructure_isSheaf`）を定理にする。理由：定義が原典どおりで、
   RΓ は層なので chaotic と同じ（`crystallineCohomology_isLimit`）。費用は有限個の局所化の族の Amitsur 複体（A0 の `structurePresheafDerived_isLimit_singleton` と同じ型）
   一件。この一件が重ければ chaotic に替える（その場合は Stacks Tag 07JK を根拠として定義の差を記録）。
3. **(c) の比較写像**：**決定（11-07、ユーザー）：Thm 5.2 は原典の η（b ↦ φ(b)、δ 変数つきの D^• = B^•{φ(J₀)/p}^∧、R′ = B/J₀B ≠ R の対象を通る）の写像が
   同型であるという形で述べる**（`etaBridge`・`crystallineComparison_polynomial`）。理由：X ↦ X^p で δ 変数なしの D^• に入れる形だと、D68 の `crystallineBridge`
   （(ℤ_p,(p)) の原典の η）と二つの比較写像が並び、Frobenius との両立やほかでの使い回しで困る。η の形なら crystallineBridge はその特殊化（`crystallineBridge_eq_eta`）。
   (a) とのつなぎは δ 変数の収縮 `pdDeltaRetraction`（Tot で可逆）で、X ↦ X^p の写像は `frobeniusPdBridge := etaBridge ≫ pdDeltaRetraction` として残る（§11.3）。
4. **∞ 関手としての RΓ_crys**：置かない／`PolyDeltaData` と同じ形の `PolyCrystallineData`（val・obj_eq・map_eq と模型との `FunctorIso` の欄）を W と C について置き、
   `bigZigzagIso` が文字どおり RΓ_crys を通るようにする。**決定（11-07）：置かない**。理由：§11.4 のとおり ∞ の整合性は模型から来るので、欄を足しても zigzag の中で打ち消し合うだけ。
5. **`pdCechNerveMap_quasiIso`**：主張を残して証明の筋を (a)＋(d) に差し替える／削除して `wittSmallFrame_isInvertible` などを (d) から直接。**決定（11-07）：主張を残し証明を site 経由に**。理由：使う側の
   docstring・sorry の理由を変えずに済み、sorry は増減しない。差し替えは CrystallineInput・DeRhamComparisonPoly の sorry の理由の行だけ（本体へ移す Codex の作業と合わせる）。
6. **対象は p 冪零**（Berthelot どおり）／p 進完備な対象（Stacks Remark 07KH の Cris^∧、D が弱終で pro 版の S3 が要らない）。**決定（11-07）：p 冪零**。理由：原典の定義のまま。
   費用は一般論 `exists_limitCone_of_proCech` 一件と `totEInfinity_isLimit_truncations`（Mittag-Leffler）。cutoff は κ := cutoff W W に固定し κ 不変性は置かない。

### 11.7 紙で確かめる項目

1. `pdCechTower`：p^e D ⊆ J̄ が divided powers で閉じる（γ_m(p^e x) = p^{em}/m!·x^m、v_p ≥ e、p = 2 も）こと、D_S^n/p^e が CRYS(R̄) で D_S^0/p^e の (n+1) 個の余積
   （Stacks Tag 07HN の余積の構成と pd 包の普遍性）、濃度 ≤ κ。
2. (c) を一般の I ∋ p で：D^• が (A,(p)) 上の結晶 prism の余単体的対象（Lemma 2.38 の議論）で、mod p の押し出し D^n/p ≅ C^n/p ⊗_φ B^n/p が I の pd を加えても成り立つこと
   （原典は I = (p) の場合に示してから一般へ帰着、本書は多項式で直接）。
3. (d)：m の mod p^{e+1} が pro 対象の間の site の射（pd 射・sec と両立）であること、O の極限の制限が pro Čech 図式の上で m に一致すること。
4. Zariski：divided powers が局所化に一意に延びること（平坦な底変換）、有限族の Amitsur 複体の完全性を ∞ の篩の条件へ移す議論。
5. 段 3：`crysBaseRestriction`（w₀）で C 上の対象が W 上の対象になる（W/J ≅ C/p、R̄_Q の二つの構造が両立）こと。
