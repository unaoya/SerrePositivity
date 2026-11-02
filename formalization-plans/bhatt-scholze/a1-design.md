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
- 含まない：Thm 6.4（de Rham 比較）、Rem 4.13・4.14、Prop 4.15、Lemma 4.21（étale 局所化。多項式代数に限るので不要）、Thm 5.2 の一般の pd イデアル I の場合。
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
| Thm 5.2 | 定理。**特別な場合**：A = Z_p、I = (p)、R = F_p[X_1,…,X_r]。結晶コホモロジーの扱いは D25（決定待ち） | `crystallineComparison_polynomial` | pd 包の Čech 脈体、Lemma 5.4、導来 Nakayama | A1-3 |
| Rem 5.3 | 不要 | — | — | — |
| Lemma 5.4 | 定理。有限変数 | `frobeniusTwist_cech_quasiIso` | 余単体的ホモトピーの一般論（§4） | A1-3 |
| Cor 5.5 | 定理。多項式代数、結晶 prism | `hodgeTate_iso_crystalline` | Thm 5.2、Cartier 同型、Lemma 4.20 | A1-3 |
| Constr 6.1 | 定義そのまま（B = A{φ(d)/p}^∧、α、性質 (1)(2)(3)） | `crystallineCover`、`crystallineCoverMap` | Cor 2.39 の r = 1（済）、Lemma 2.24（済）、導来 Nakayama、Tor 振幅 | A1-4 |
| Prop 6.2 | 定理。一般の r、基底は §0 の範囲 | `hodgeTate_iso_of_crystallineCover` | Constr 6.1、Cor 5.5、Lemma 4.20 | A1-4 |
| Thm 6.4 | 不要 | — | — | — |
| Lemma 2.36 多変数 | 定理。変数の場合：Z_p{x_1,…,x_r, φ(x)/p} は離散・p ねじれなしで pd 包 D_{(x)}(Z_p{x}) | `pdEnvelope_eq_frobeniusDivision` | 像の形は済（`pDivisionFactorialSubring_eq_raw_range`）。p ねじれなしは r = 1 のみ（T2-2） | A1-2 |
| Lemma 2.38・Cor 2.39 | 変数の場合は Lemma 2.36 多変数と自由 δ 環の平坦底変換で済む | — | — | A1-2 |
| Ex 2.21・Ex 3.4 | 定義そのまま（普遍 distinguished δ 環 Z_(p){d, δ(d)^{-1}} と、その (p,d) 完備化 A_0。有界 prism、(p,d) 正則、A_0/p の Frobenius が d 完全平坦、向き付き prism への普遍性） | `universalOrientedPrism` | 未（T2-4）。自由 δ 環・δ 環の局所化（`DeltaLocalization`）・完備化の δ 構造は済。Frobenius の mod p 自由性は `FreeDeltaFrobeniusFlat` | A1-4 |
| de Rham 複体 | 定義（p 完備多項式代数について、dX 上の自由加群と d。D26） | `deRhamComplex` | Mathlib に de Rham 複体はない（Kähler 微分・外冪はある） | A1-1 |
| Cartier 同型 | 定理。F_p 上の多項式代数 | `cartierIso` | なし。直接計算 | A1-3 |
| pd 包の Čech 脈体と de Rham 複体の比較 | 定理。Z_p⟨X⟩ について（D25 の β 形） | `pdCechNerve_deRham` | なし。古典（Berthelot、Bhatt–de Jong） | A1-3 |

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
- B := A{φ(d)/p}^∧（r = 1 の Cor 2.39、既存 `Andre/Envelope/PDivision` の形）。Lemma 2.24 で φ(d) = pu（u 単元）、B は (p, φ(d)) 完備ゆえ (p,d) 完備、
  (d) の pd 包の p 完備化で離散・p ねじれなし。(B,(p)) は結晶 prism。
- α := (A → B) ∘ φ_A : (A,(d)) → (B,(p)) は prism の射（α(d) = φ(d) ∈ pB）。
- α̂^* : D_comp(A) → D_comp(B)（導来 (p,d) 完備底変換）の性質：(1) 保存的、(2) 有限 (p,d) 完全 Tor 振幅（c の明示）、(3) α̂^*Δ_{R/A} ≃ Δ_{R_B/B}
  （Lemma 4.20）。証明は mod p の分解 (6)：A/p → A/(p,d) → A/(p,d^p) → B/p ≅ D_{(d)}(A/p) で、最初は有限 Tor 振幅（d 正則 mod p：A/d が
  p ねじれなしなので d は A/p で正則）、二つ目は Frobenius の平坦性、最後は pd 包の自由性。

### 2.5 Tor 振幅の実例（A0 §2.9 の定義で）

- 平坦な射（Z_p → 結晶 prism A、A は p ねじれなし）：c = 0。
- Constr 6.1 の α：c = 1（(6) の最初の射）。
- Prop 6.2 の b（D-A1-2 で (i) を採る場合のみ）。

## 3. 証明の筋（原典の帰着の順）

1. **Thm 6.3（多項式代数）⇐ Prop 6.2（一般の r）**：Thm 6.3 の証明は「Lemma 4.21 で多項式代数に帰着し、Prop 6.2 と同じ議論」。多項式代数に限るので
   Prop 6.2 を一般の r で示せばよい。
2. **Prop 6.2**：η : ⊕_i Ω^i_{R/k}[−i] → Tot(C^•/d) を D(R) で選ぶ（Ω^i は自由 R 加群なので、H^i の像の基底の代表元を選ぶ）。η が擬同型であることを示す。
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
5. **Lemma 5.4（有限変数）**：原典どおり。k 標数 p、B = k[N^r] = k[M]、B^• = k[EM]（EM は 0 → M の Čech 脈体、[n] ↦ M^{⊕[n]}）、B^{•,(1)} = k[E(pM)]。
   S = {0,…,p−1}^r の剰余類代表で k[EM] ≅ k[E(pM)] ⊗_k k[ES]（半余単体的加群として自由）、k[ES] は k → C^0 := k[M^{gp}/pM^{gp}] の Čech 脈体の
   半余単体的加群に同じ、C^0 → k の切断があるので Čech 脈体 k → C^• は余単体的加群のホモトピー同値、テンソルで保たれ、
   非正規化複体は半余単体的構造だけで決まる。
6. **D25 の β 形：Tot(D^•) ≃ Ω^•_{Z_p⟨X⟩/Z_p}**（mod p でよい：Tot(D^•/p) ≃ Ω^•_{F_p[X]/F_p}）。二段：(i) 多項式環 B_0 = Z_p⟨X⟩ の pd Čech 脈体
   D_0^•（δ 変数なし）について Tot(D_0^•) ≃ Ω^•_{B_0}：双複体 Ω^•_{D_0^•} を二通りに Tot する。列（n 固定）は pd-Poincaré 補題
   （Ω^•_{D_0^n/Z_p} ≃ Ω^•_{B_0/Z_p}、D_0^n = B_0⟨z_1,…,z_n⟩_{pd}）、行（j 固定、j ≥ 1）は Tot_n Ω^j_{D_0^•} の非輪状性（Ω^j_{D_0^•} が
   Ω^j_{D_0^0} ⊗ D_0^• 型の余単体的加群に分解し、D_0^• が切断つきの Čech 脈体であること）。古典（Berthelot、Bhatt–de Jong 2011 Thm 2.12）。
   (ii) D^•（δ 変数つき、B = Z_p{X}^∧）と D_0^• の比較：B_0 = Z_p⟨X⟩ は δ 環（δ(X) = 0）なので B → B_0 ← B_0 の retraction があり、
   双余単体的な pd 包の脈体の行・列が切断つき Čech 脈体のホモトピー同値になる。または (i) の議論を D^• に直接行う（δ 変数は多項式変数として
   Ω に dδ^k(X) を足すだけ）。実装でどちらか。
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
| G-A1-7 | pd-Poincaré 補題：Ω^•_{B⟨z⟩_{pd}/B} ≃ B（標数 p でも、p 完備でも） | なし | §3 の 6 |
| G-A1-8 | Cartier 同型（F_p[X_1,…,X_r]）：C^{-1} : Ω^i_{F_p[X]^{(1)}} → H^i(Ω^•_{F_p[X]/F_p}) | なし。Künneth（一変数の直接計算のテンソル） | Cor 5.5 |
| G-A1-9 | de Rham 複体の普遍性（§2.1） | なし | Constr 4.9 |
| G-A1-10 | D(R) で自由加群からの射を H^i の元から持ち上げる | 初等 | Prop 6.2 の η |
| G-A1-11 | **値が CAlg の RΓ と模型の環構造の一致（D27 の一般論）**：Sheaves 層を E = CAlg_R（E∞-A 代数の ∞ 圏、EInfinity の `CAlg_R`）で使い、環の前層 O_Δ を CAlg 値前層として RΓ を取る（CAlg_R の presentable 性 G12 が要る）。余単体的可換環 C^• の Tot は Barratt–Eccles／Alexander–Whitney で E∞ 代数になり、S3 の補題の CAlg 版で RΓ_CAlg(O_Δ) ≃ Tot C^• が E∞ 代数の同値。その H^* の環構造が §2.2 の cup 積に一致する | EInfinity に Barratt–Eccles・Alexander–Whitney（余鎖の余モノイド）、忘却の極限保存。CAlg_R の presentable 性・余単体的環の Tot の E∞ 構造は未 | D27。A2（Construction 7.6 の可換代数対象）でも要る |
| G-A1-12 | 普遍向き付き prism（Ex 2.21・3.4）：自由 δ 環の δ(d) での局所化と (p,d) 完備化、有界性、(p,d) 正則、Frobenius の mod p 平坦性、向き付き prism への普遍性 | 自由 δ 環・`DeltaLocalization`・完備化の δ 構造・Frobenius の mod p 自由性は済 | Prop 6.2 (c) |
| G-A1-13 | 底変換関手の合成の性質：Res_{A_0} が (p,d) 完備性と零を保つこと、Tor 振幅の合成、Lemma 4.22 の合成への適用 | HA/DerivedCompletion（2b の後に読む） | Prop 6.2 (c) |

## 5. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D25 | Thm 5.2 は Δ_{R^{(1)}/A} ≃ RΓ_crys(R/A)（大きい結晶 site のコホモロジー） | **β（2026-11-02 決定）**：E3 で使う形 Δ_{R^{(1)}/Z_p} ≃ Tot D^• ≃ Ω^•_{Z_p⟨X⟩}（RΓ_crys を既知の値で置き換えた特別な場合）で述べる。結晶 site は定義しない。α（結晶 site と RΓ_crys、pro 版の脚注 10）は β の上に後から足せる | E3 の経路で RΓ_crys を使うのは Thm 5.2 だけ。定理の特別な場合であり、定義は増やさない |
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

骨組みの順（2026-11-02 決定）：A1-1 → **A1-4** → A1-2 → A1-3。結晶側の話は最小限にする：A1-4 は結晶側の入力を一つの定理
`hodgeTate_iso_polynomial_Zp`（(Z_p,(p))・R = F_p[X_1,…,X_r] の Cor 5.5）に閉じ込め、A1-2・A1-3 はその証明だけを供給する。
結晶 site・crystal・RΓ_crys は定義せず（D25 β）、Thm 5.2 の一般の pd イデアル・結晶側の Frobenius の議論・Thm 6.4 は扱わない。
A1-3 の de Rham 比較（§3 の 6）と Cartier は BS と独立な古典なので、別のファイルに分けて共有層へ出せる形にする（置き場所は調整役と相談）。

**結晶側に残るもの（最小限）**：(1) Lemma 5.4（余単体的代数）、(2) pd 包の Čech 脈体 D^•/p の Tot ≃ Ω^•_{F_p[X]/F_p}（pd-Poincaré 補題と
Čech 方向の非輪状性）、(3) Cartier 同型（F_p[X]）、(4) 橋 η : C^• → D^• と D^• ≅ C^• ⊗_φ B^•（Lemma 2.36 の変数の場合）。
A5 の Lemma 8.6 が使う標数 p の de Rham 比較は (2) の W(k) への平坦底変換。

- **A1-5（2026-11-02、A5 の決定 3 で追加）**：de Rham 比較 Thm 6.4 の T = R⟨X_1,…,X_n⟩・mod p の特別な場合
  （φ_A^*Δ_{T/A} ⊗^L_A A/(p,d) ≃ Ω^•_{(T/p)/(R/p)}、E∞ 代数として、T → T_∞ と両立）。Lemma 8.6（A5-3）の入力。A1-4 の装置
  （Construction 6.1・普遍 prism）で原典 Thm 6.4 の証明を特別な場合に追う。結晶側の入力は増やさない。設計は A5-3 の骨組みの前に a1-design に追記。

## 7. 決定（2026-11-02、ユーザー）

1. **D-A1-1（D25）**：β。Thm 5.2 は E3 で使う形（Δ_{R^{(1)}/Z_p} ≃ Tot D^• ≃ Ω^•_{Z_p⟨X⟩}）の特別な場合として述べ、結晶 site は定義しない。
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
   符号と cup 積の規約を固定する。
4. §3 の 6：pd Čech 脈体と de Rham 複体の比較の、行の非輪状性（Tot_n Ω^j_{D_0^•} = 0、j ≥ 1）の証明の形（Bhatt–de Jong 2011 §2 の議論を
   有限変数・mod p で）。
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

Thm 6.4 の証明の ψ・W(A/I) の経路ではなく、Prop 6.2（A1-4）と同じ帰着を使う：
1. 完全 prism → 普遍向き付き prism A_0（Ex 3.4）：d の選択で A_0 → A、Cor 4.12／(4) で Δ_{T/A} = Δ_{T_0/A_0} ⊗̂_{A_0} A（T_0 = (A_0/d_0)⟨X⟩）、
   Frobenius と両立（δ 射）、de Rham 複体は底変換と両立。よって A_0 上で示せばよい。
2. A_0 → D_0（Construction 6.1 の α、結晶 prism (D_0,(p))）：α̂^* は保存的（(1)）、(3) で α̂^*Δ_{T_0/A_0} = Δ_{T_{D_0}/D_0}、α は δ 射なので φ と両立。
   よって結晶 prism (D_0,(p)) 上で示せばよい。
3. 結晶 prism (B,(p)) と多項式 (B/p)[X]：Lemma 4.20（(p)-prism の Δ は任意の p 完備底変換と可換、A0-4）で Z_p に帰着。
4. Z_p と F_p[X]：**結晶の黒箱**（A1-3）を de Rham の形で：φ^*Δ_{F_p[X]/Z_p} ≃ Ω^*_{Z_p⟨X⟩/Z_p}（Thm 5.2 β の使う形、可換代数として）。mod p で
   Ω^*_{F_p[X]/F_p}。HT 比較（Cor 5.5、A1-3 の `hodgeTate_iso_polynomial_Zp`）は同じ黒箱と Cartier 同型（一変数は G-A5-12、n 変数は Künneth）から。
   **結晶の黒箱は一つのまま**（D68）。

### 9.2 単位と形

| 項目 | Lean の形 | 既存・不足 |
| --- | --- | --- |
| 黒箱（de Rham 形） | `crystalline_deRham_polynomial_Zp : φ^*Δ_{F_p[X_1..X_n]/Z_p} ≃ Ω^*（CAlg(D(Z_p))）` | A1-3（A1-2 の対象の上） |
| Cor 5.5（HT）を黒箱から | `hodgeTate_iso_polynomial_Zp` の証明：黒箱 mod p と Cartier | G-A5-12 の n 変数版 |
| Lemma 4.20 | (p)-prism の Δ の底変換 | A0-4（D、2b 後） |
| 結晶 prism の多項式 | `deRham_iso_polynomial_crystalline` | 3 |
| A_0 への持ち上げ | `deRham_iso_polynomial_universal`（α̂^* 保存的、(3)、φ 両立） | A1-4 `baseChangeB`・`crystallineCover*` |
| 完全 prism | `deRham_iso_polynomial_modP`（A1-5 の主張） | 1 |
| T_∞ | `deRham_iso_rootAlgebra_modP`：φ^*Δ_{T_∞} ⊗ A/(p,d) ≃ T_∞/p | A5-4 の filtered 余極限、Ω の遷移の消滅 |
| 可換代数構造 | 全段を CAlg の同型として | Shared/DeRhamPolynomial の cdga → CAlg、G-A1-11 |

### 9.3 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D68 | 結晶の入力は Thm 5.2（結晶 site）と Cor 5.5 | 黒箱を Thm 5.2 β の de Rham 形一つにし、HT（Cor 5.5）と de Rham mod p の両方をそこから出す | 黒箱は増えない（A5 の決定 3 の「結晶の範囲は増えない」を満たす） |
| D69 | Thm 6.4 の証明は ψ : A → W(A/I) と pd イデアル、仮定「W(A/I) p ねじれなし」 | Prop 6.2 と同じ帰着（A_0、Construction 6.1、Lemma 4.20、Z_p）で、仮定を使わない | 多項式・mod p の特別な場合なので可能。perfectoid R について W(R) の p ねじれを確かめる必要がなくなる |

### 9.4 決定事項（相談）

1. 結晶の黒箱を de Rham 形 `crystalline_deRham_polynomial_Zp` 一つにして、HT（`hodgeTate_iso_polynomial_Zp`）をそこから Cartier で導く（推奨、D68）／
   de Rham 形を第二の黒箱として別に置く。
2. 帰着は Prop 6.2 と同じ A_0・Construction 6.1・Lemma 4.20 の経路（推奨、D69）／原典 Thm 6.4 の ψ・W(A/I) の経路（W(R) の p ねじれなしを確かめる必要）。

### 9.5 紙で確かめる項目

1. 9.1 の 1：Frobenius 捻りと底変換の両立（φ_{A_0}^* と ⊗_{A_0} A の交換、δ 射）。
2. 9.1 の 2：α̂^* の保存性で CAlg の同型を反映できること（U で見て D(D_0) の保存性）。
3. T_∞ の段：colim_m Ω^*_{T_m/p} = T_∞/p（Ω^{≥1} の遷移が零）、Δ の完備化した filtered 余極限との整合。
4. Cartier の n 変数版（Künneth）で Cor 5.5 を黒箱から出せること。
