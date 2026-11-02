# A0 の設計：prismatic site と Čech–Alexander 複体（原典 §4.1・§4.3 と §3 の前提、2026-11-02）

概要：E3 を消す道筋（stage2 の A 案）の最初の単位 A0 の設計。原典 BS 著者版 §4.1（Def 4.1、Rem 4.6、Lemma 4.8）、§4.3
（Not 4.16、Construction 4.17・4.18、Rem 4.19、Lemma 4.20・4.22）と、それらが使う §3 の定理（Lemma 3.7(2)(3)、Cor 3.12、
Prop 3.13、Def 2.42）を、**定義は原典のまま、定理は E3 に要る特別な場合だけ**の方針で形式化するための項目表・型の案・単位・差の記録。
方針：Δ_{R/A} は Not 4.16 どおり site の RΓ（[∞ 層の設計書](infinity-sheaves-design.md) の `derivedGlobalSections`）で定義し、
Čech–Alexander 複体がそれを計算することは定理にする。envelope は Prop 3.13 の普遍性で定義し、存在は Ex 3.14 の場合（多項式代数からの
全射の核）に証明する。計算用の模型（完備化した自由 δ 環）は証明の中だけで使う。
規約：決定済みの差は U1（Type u・濃度 ≤ κ、ノート D16）、U3（向き付き有界基底、ノート D5）、U4（完備化は導来完備化の H⁰）、
β（RΓ は層化と Γ）、D-S1（Čech 層、ノート D17）、D18（まず D(A) 値）。本書では D19 以降を追加する。Lean の名前は仮。
ビルドしない（設計と骨組みのみ、`drafts/`）。原典の番号は著者版。
使われ方：A0 の骨組み（`drafts/A0/…`）を書くときの正本。A1 の設計書は本書の Not 4.16・Rem 4.19・Lemma 4.20 を前提にする。
勉強ノート第 4 章（`exposition/ja/bs/04-site.html`）の項目表と対応させる。

## 0. 範囲と前提

- 含む：§4.1（Def 4.1、Rem 4.6、Lemma 4.8 は済）、§4.3（Not 4.16、Constr 4.17・4.18 と脚注 10、Rem 4.19、Lemma 4.20・4.22）、
  §3 の前提（Def 2.42、Lemma 3.7(2)(3)、Cor 3.12、Prop 3.13、Ex 3.14）、O_Δ と Δ の Frobenius（§4 には明示されないが Construction 7.6 が使う）。
- 含まない：§4.2（Constr 4.9、Lemma 4.10、Thm 4.11、Cor 4.12）は A1。Rem 4.2〜4.5・4.7、Lemma 4.21 は不要（ノート第 4 章の判定）。
- 前提にする一般論：∞ 層の設計書の S1（層条件）、S2（Γ・RΓ の型）、S3（弱終対象の Čech 脈体の補題）、S6（κ の切り落とし）。
  S4（層化の存在）は Not 4.16 の定義の存在部分に要るが、A0 の骨組みは S2 の型（反射が与えられたとして）で書ける。
- 基底：向き付き有界 prism (A, (d))。既存の `OrientedPrism p A` と、有界性は既存の形（A/d の p 冪ねじれが一様な冪で消える）。
- R：原典は p 完全 smooth な A/I 代数。**定義**（site、O_Δ、Δ_{R/A}）は任意の p 完備な A/d 代数 R について入れる（原典 Def 4.1 も
  任意の p 進形式スキームについて述べている）。**定理**（Constr 4.17 の弱始性、Prop 3.13 の適用、Čech–Alexander が Δ を計算すること）は
  集合上の多項式代数 R = (A/d)⟨X_T⟩（p 完備化）に限る。A2 の左 Kan 延長の添字圏がこれで足りる。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存 | 単位 |
| --- | --- | --- | --- | --- |
| Def 2.42 | 定義そのまま（A に相対的な (p,d) 完全正則列） | `IsCompletelyRegularRel` | なし。Koszul 複体の平坦性は HA/Koszul* | A0-3a |
| Lemma 3.7(2) | 定理。一般の形 | `isDiscrete_of_completelyFlat_boundedPrism` ほか | HA/DerivedCompletion の CompletedFlat*（docstring なし、要読解） | A0-3b |
| Lemma 3.7(3) | 定理。一般の形 | 平坦な prism の射 ⇔ 完全平坦 δ 代数 | `OrientedPrism.Hom`、`IsCompletelyFlat` | A0-3b |
| Cor 3.12 | 定理。一般の形（site の公理、O_Δ が層、導来降下） | §2.6 | 押し出し＝完備テンソル（BS/Perfectoidization/CompletedTensor）。Amitsur の完全性はなし | A0-3d |
| Prop 3.13 | **定義**：普遍性。**定理**：Ex 3.14 の場合の存在と (1)(2)(3) | `IsPrismaticEnvelope`、`prismaticEnvelope_exists_of_variables` | `DeltaAdjoinDivision` と `existsUnique_deltaAdjoinDivisionHom_of_regular`、`RelativeFreeDeltaRing`、`deltaPDCompletionStructure` | A0-3c |
| Def 4.1 | 定義そのまま | `PrismOver`、`PrismaticSite`、`flatTopology`、`structurePresheaf` | `OrientedPrism`、`IsCompletelyFaithfullyFlat`、Mathlib `GrothendieckTopology`・`Sieve.generate` | A0-1 |
| Rem 4.6 | 定義そのまま（完全 prism の充満部分圏）。perfectoid 代数の圏との同値は定理 | `PerfectPrismaticSite` | Thm 3.10（`Prism/Perfectoid/*`）、E3 の `PerfUnder_u` | A0-1（同値は A5） |
| Lemma 4.8 | 済（有界な標的） | `existsUnique_perfectPrismHomLift_to_bounded` | 済 | — |
| Not 4.16 | 定義そのまま | `prismaticCohomology`、`hodgeTateCohomology` | S2 | A0-1 |
| Frobenius | 定義（O_Δ の自然変換）と Δ への誘導 | `structurePresheafFrobenius`、`prismaticCohomologyFrobenius` | δ 構造の φ、S2 の関手性 | A0-1 |
| Constr 4.17 | 定義そのまま（B_0 = R の台集合上の多項式環の完備化）。弱始性は定理（多項式代数） | `cechAlexanderZero`、`cechAlexanderZero_weaklyInitial` | `RelativeFreeDeltaRing`、`PDCompletionH0` | A0-2 |
| Constr 4.18 | 定義そのまま（Čech 脈体）。Δ を計算することは定理 | `cechAlexander`、`cechAlexander_isLimitCone`、`prismaticCohomology_iso_cechAlexanderTot` | Mathlib `Arrow.cechConerve`、`alternatingCofaceMapComplex`、S3 | A0-2 |
| 脚注 10 | 一般論（S3） | — | — | S3 |
| Rem 4.19 | 定理（affine 空間の小さい模型と底変換） | `cechAlexanderAffine`、`cechAlexanderAffine_baseChange` | Prop 3.13(2) | A0-2 |
| Lemma 4.22 | 定理。一般の形 | `completedBaseChange_tot_comm` | HA/DerivedCompletion（CompletedBaseChange*、Truncation） | A0-4 |
| Lemma 4.20 | 定理。一般の形 | `prismaticCohomology_baseChange` | Lemma 4.22、Prop 3.13(2) | A0-4 |
| Rem 4.2〜4.5・4.7、Lemma 4.21 | 不要 | — | — | — |

## 2. 定義の形

名前・名前空間は仮（`SerrePositivity.BhattScholze.Prismatic`）。

### 2.1 基底と対象（Def 4.1 の材料）

- 基底：`(A : Type u) [CommRing A] (P : OrientedPrism p A) (hP : 有界)`。以下 d := P.generator。
- R：`(R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]`、p 完備（`IsModuleComplete R p`）。
- 対象（環の側）：構造 `PrismOver P R`
  - `B : Type u`、`[CommRing B]`、`Q : OrientedPrism p B`、有界、
  - `toHom : OrientedPrism.Hom P Q`（prism の射。剛性 `map_ideal_eq` により `Q.ideal = (d)B`）、
  - `section : R →ₐ[A ⧸ P.ideal] B ⧸ Q.ideal`、
  - 濃度：`#B ≤ κ`（κ は §2.7）。
- 射：`B → B'` の prism の射で、`section` と両立するもの。圏 `PrismOver P R`（対象は Type (u+1) にあるが、濃度の条件で本質的に小さい）。
- site：`PrismaticSite P R := (PrismOver P R)ᵒᵖ`（原典 Def 4.1・Cor 3.12 の「prism の圏の opposite」）。

### 2.2 位相と構造層（Def 4.1）

- 忠実平坦な prism の射：`f : B → C` が (p, d) 完全忠実平坦（`IsCompletelyFaithfullyFlat (Ideal.span {p, d}) C`、C を B 加群として）。
  原典の「(p, IB) 完全忠実平坦」。Lemma 3.7(3) によりこれが「忠実平坦な prism の射」の定義（原典の定義は Lemma 3.5 を経由するので、
  Lemma 3.7(3) を定理として記録する）。
- 位相：`flatTopology P R : GrothendieckTopology (PrismaticSite P R)` := 忠実平坦な射 f について篩 `Sieve.generate (Presieve.singleton f.op)` を
  被覆篩に含む**最小の**位相（`GrothendieckTopology` は完備束）。これで site の公理を定義の段階で証明しなくてよい。
  Cor 3.12 前半（忠実平坦な射の押し出しが存在し忠実平坦）は、「この位相の被覆篩は忠実平坦な射の篩で refine できる」という定理として入れる。
- 構造層：`structurePresheaf P R : PrismOver P R ⥤ CommRingCat`（B ↦ B）、`reducedStructurePresheaf`（B ↦ B ⧸ (d)B）。
  site の前層としては `(PrismaticSite P R)ᵒᵖ ⥤ CommRingCat` で、これは `PrismOver P R ⥤ CommRingCat` と同じ。
- D(A) 値：`J A ∘ structurePresheaf`（E3 の `J R = discreteEmbedding R` と同じ埋め込み）。A 加群としては `toHom` で A 代数。

### 2.3 完全 prismatic site（Rem 4.6）

- `PerfectPrismaticSite P R`：`PrismOver P R` のうち B が完全（φ_B 全単射）な対象の充満部分圏の opposite。
- 定理（A5 で使う）：Thm 3.10 により、完全 prism B ↦ B/dB は perfectoid 環で、`PerfectPrismaticSite P R` は R 上の perfectoid 代数
  （E3 の `PerfUnder_u`）の圏と同値。原典 Rem 4.6 の「prism を使わない記述」。

### 2.4 prismatic コホモロジー（Not 4.16）と Frobenius

- `prismaticCohomology P R : (derivedInfinityCategory A) _⦋0⦌` := `derivedGlobalSections (flatTopology P R) (J A ∘ structurePresheaf P R)`。
  S2 の規約どおり、頂点の等号ではなく `IsLimitCone` の普遍性で扱う（錐のデータは `prismaticCohomologyCone`）。
- `hodgeTateCohomology P R` := `prismaticCohomology P R ⊗^L_A A/d`（D(A) のテンソル。基盤の完備テンソル／Koszul の形で）。
  定理：Ō_Δ の RΓ とも一致する（Cor 3.12 の最後の文：A/d は完全複体なので RΓ と ⊗ が交換）。
- Frobenius：各 B の δ 構造の φ_B は環の射 B → B で、δ 射と可換するので、`structurePresheaf` の自然変換
  `structurePresheafFrobenius : structurePresheaf ⟶ structurePresheaf`（環の前層として。A 線形ではなく φ_A 半線形）。
  S2 の関手性（前層の射 F → G から F^♯ → G^♯ と Γ の射）で `prismaticCohomologyFrobenius : Δ → φ_{A*}Δ`（D(A) で、スカラー制限 φ_{A*}）。
  A4（Def 8.2 の Frobenius 余極限）の入力。

### 2.5 prismatic envelope（Def 2.42、Prop 3.13、Ex 3.14）

- `IsCompletelyRegularRel P B x`（Def 2.42）：B は導来 (p,d) 完備な A 代数、x : Fin r → B。Kos(A; p, d) → Kos(B; p, d, x) が
  単体的可換環の平坦射。Lean では「Kos(B; p, d, x) の H⁰ = B/(p,d,x) が A/(p,d) 上平坦で、高次ホモロジーが消える」の形
  （原典の定義の離散な言い換え。差 D20）。
- `IsPrismaticEnvelope P (B : δ-A 代数) (J : Ideal B) (hJ : (d) ≤ J) (C : PrismOver 型の prism) (η : B → C)`：
  η は δ 射で J ↦ dC、かつ任意の prism (D, dD) over P と δ 射 g : B → D で J·D ≤ dD となるものに対し、g = h ∘ η となる δ 射 h : C → D が一意。
  原典 Prop 3.13 の「普遍射 (B, J) → (C, IC)」そのもの。普遍性の中の D は有界性を要求しない（原典どおり「prism (C, IC) over (A, I)」）。
- 定理 `prismaticEnvelope_exists_of_variables`（Prop 3.13 の存在、Ex 3.14 の場合）：B_0 を集合 T 上の多項式 A 代数の (p,d) 完備化、
  B := Free_{δ,A}(B_0)^∧（相対自由 δ 環 `RelativeFreeDeltaRing` の完備化 `PDCompletionH0`、δ 構造は `deltaPDCompletionStructure`）、
  J := (d) + (変数の部分集合 Z ⊆ 変数系) B。このとき envelope が存在し、(1) (p,d) 完全平坦、(2) 底変換と可換、(3) 平坦局所化と可換。
  **証明**（計算用の模型、定義には使わない）：Z = d·Y とおいた自由 δ 環 A{(T∖Z), Y}^∧ が普遍性を満たす。普遍性の両向きは
  `existsUnique_deltaAdjoinDivisionHom_of_regular`（標的で d が正則）と `existsUnique_deltaPDCompletionHom`。平坦性・離散性・d の正則性は
  Lemma 3.7(2)（多項式環は自由）。一般の Prop 3.13（Zariski 局所的な正則列）は E3 に不要で、主張を Ex 3.14 の場合に絞る。
- Construction 4.17 が実際に使う J は ker(B → (B/J_0 B)^∧)（J_0 = ker(B_0 → R)）。R = (A/d)⟨X_S⟩ のとき、A/d → A の集合論的切断で
  係数を持ち上げた変数変換により J_0 B_0 は「変数の部分集合 ＋ (d)」の形になる（紙の検証 §5 の 2）。これで上の定理が適用できる。

### 2.6 Cor 3.12 と Lemma 3.7(2)(3)

- Lemma 3.7(2)：有界 prism 上の (p,d) 完全平坦な複体 M は離散で古典的 (p,d) 完備、M[d^n] = 0、M/d^n M の p 冪ねじれは有界。
  一般の形で証明する（Cor 3.12 の押し出しと Prop 3.13(1) の両方で使う）。HA/DerivedCompletion の CompletedFlat* に部品がある見込み（要読解）。
- Lemma 3.7(3)：prism の射 (A,(d)) → (B, J) が（忠実）平坦 ⇔ B が (p,d) 完全（忠実）平坦な δ-A 代数で J = dB。
- Cor 3.12：
  (a) 忠実平坦な prism の射 B → C と任意の射 B → B′ について、押し出し (B′ ⊗̂^L_B C)^∧ が有界 prism で B′ 上忠実平坦。既存の完備テンソル
  （BS/Perfectoidization/CompletedTensor、HA/DerivedCompletion/CompletedBaseChange*）と Lemma 3.7(2)。
  (b) O_Δ（環の前層）は flatTopology の 1 圏の層：忠実平坦な B → C について B → C ⇉ C ⊗̂_B C が等化子。
  (c) 導来降下：忠実平坦な B → C の完備 Čech 余脈体 C^• について、錐 B → Tot C^• が D(A)（または D(B)）の極限錐。
  原典の証明は mod (p^n, d^n) で単体的可換環の忠実平坦降下に帰着し逆極限を取る。Mathlib には Amitsur 複体の完全性がないので、
  有限段（B/(p^n,d^n) → C/(p^n,d^n) の Amitsur 複体の完全性、忠実平坦なら底変換後の収縮ホモトピーで）を証明し、逆極限（Milnor 列）で
  完備版にする。HA/CompleteFaithfullyFlatDescent はスカラー同種写像の降下だけなので再利用できない。
  (d) (b)(c) から、D(A) 値前層 J ∘ O_Δ は `IsInfinitySheaf (flatTopology)`（S1。生成系の単射 f の篩に対する降下が f の Čech 脈体に沿う
  降下と同値であること、生成系での降下から全被覆篩での降下が出ること、の二つの S1 の補題を使う）。
  (e) O_Δ は離散な Čech 層なので hypersheaf（ノート D17 の記録、∞ 層の設計書 §2.1）。Γ は古典的 RΓ と一致する、という注記付きの定理。

### 2.7 濃度 κ（S6、ノート D16）

- λ := #A + #R + ℵ₀、κ := λ^{ℵ₀}。`PrismOver P R` の対象の条件 `#B ≤ κ`。
- 各構成が閉じること（紙の検証 §5 の 4）：Čech–Alexander の各項（台集合 R 上の多項式環の完備化、濃度 ≤ (λ·ℵ₀)^{ℵ₀} = κ）、押し出し（完備テンソル、
  ≤ κ^{ℵ₀} = κ）、完全化（Lemma 3.9、≤ κ^{ℵ₀}）、A5 の S̃ と André 拡大。
- κ 不変性：κ₀ ≤ κ ≤ κ′ で `prismaticCohomology` が一致（C^0 がどの κ でも弱始、C^• ⊂ 𝒞_{κ₀}、S3）。O_Δ についてだけ。

### 2.8 Čech–Alexander 複体（Constr 4.17・4.18、Rem 4.19）

- `cechAlexanderZero P R : PrismOver P R`（Constr 4.17 の C）：B_0 := (A[X_{|R|}])^∧（台集合 |R| 上の多項式環の (p,d) 完備化。
  原典 Constr 4.18 の「strictly functorial」な選び方）、B := Free_{δ,A}(B_0)^∧、J := ker(B → (B/J_0 B)^∧)、C := envelope（§2.5）。
  R → C/dC は B_0 → R の持ち上げから。濃度 ≤ κ。
- 定理 `cechAlexanderZero_weaklyInitial`：任意の D ∈ PrismOver P R に射 C → D がある（原典 Constr 4.17 の証明：B_0 → D の持ち上げは
  多項式環なので取れ、δ 構造で B → D に一意に延び、envelope の普遍性で C → D）。R が多項式代数のとき（§2.5 の存在定理の範囲）。
- `cechAlexander P R : CosimplicialObject (PrismOver P R)`（Constr 4.18）：A → B_0 の完備 Čech 余脈体 B_0^• に Constr 4.17 を項ごとに当てる。
  Mathlib `Arrow.cechConerve` は圏の押し出し（ここでは完備テンソル）を要るので、B_0^n = (A[X_{|R|} × Fin (n+1)])^∧ と直接書いて
  余単体的構造を変数の添字で与える方が短い見込み（どちらでも定義は原典どおり。実装の選択）。
- 定理：`cechAlexander` は `cechAlexanderZero` の `PrismOver P R` での Čech 脈体（n 項目が C^0 の (n+1) 個の余積。Constr 4.17 の最後の文
  「B_0 のテンソル積を余積に送る」）。余積の存在は envelope の普遍性から。
- 定理 `cechAlexander_isLimitCone`（Constr 4.18 ＋ 脚注 10）：錐 Tot O_Δ(C^•) → J ∘ O_Δ は `PrismaticSite P R` 上の極限錐（S3）。
  Cor 3.12(d) と合わせて `prismaticCohomology_iso_cechAlexanderTot : Δ_{R/A} ≃ Tot O_Δ(C^•)`、同様に Ō_Δ と C^•/dC^•。
  Tot は Mathlib `alternatingCofaceMapComplex`（各項が離散なので次数 n に C^n を置く余鎖複体）を D(A) へ送ったもの。D(A) の Δ 上の極限と
  一致することは S3 の G10。
- `cechAlexanderAffine P n`（Rem 4.19）：R = (A/d)⟨X_1,…,X_n⟩、B_0 = A⟨X_1,…,X_n⟩ の小さい模型。同じ定理で Δ を計算する
  （弱始対象は一意ではないので、両方が極限錐であることから同型）。定理 `cechAlexanderAffine_baseChange`：prism の射 (A,d) → (A′,d′) について
  項ごとの完備底変換が A′ 側の模型（Prop 3.13(2)）。A1 の Prop 6.2 とLemma 4.20 で使う。

### 2.9 底変換（Lemma 4.22・4.20）

- Tor 振幅：原典 Lemma 4.22 が使う形で定義する。`HasFiniteCompleteTorAmplitude (f : C → C′) (J = (x_1,…,x_r)) (c : ℕ)` :=
  任意の K ∈ D^{≥ n}(C) について (K ⊗^L_C C′) ⊗^L_{C′} Kos(C′; x) ∈ D^{≥ n−c}。平坦なら c = 0。Construction 6.1 の α と Prop 6.2 の b が
  有限振幅であることは A1 で示す。
- Lemma 4.22：J 完備底変換 (−) ⊗̂^L_C C′ は D^{≥0} の余単体的対象の Tot と可換。原典の証明（n 骨格で示し、fiber が D^{≥ n+1−c} に
  あることから各次数で一致）をそのまま。各項が離散な余単体的対象なら Tot は余鎖複体で、底変換後は各列が [−c, 0] に有界な双複体なので
  全複体は各次数で有限和（HA の BoundedAbove*・Truncation の部品）。
- Lemma 4.20：(A,d) → (A′,d′) が有限 (p,d) 完全 Tor 振幅なら Δ_{R/A} ⊗̂^L_A A′ ≃ Δ_{R′/A′}（R′ = R ⊗̂ A′）。
  `cechAlexanderAffine_baseChange`（項ごと）と Lemma 4.22。Ō も同様（mod d）。
  原典の注意どおり、HT 比較の後は Tor 振幅の仮定を外せる（Cor 4.12、A1）。

## 3. 単位と順序

| 単位 | 内容 | 前提 | 書く順 |
| --- | --- | --- | --- |
| A0-1 | Def 4.1（`PrismOver`・`PrismaticSite`・`flatTopology`・`structurePresheaf`）、Rem 4.6、Not 4.16（S2 の型で）、Frobenius、κ の条件 | S1・S2 の型、`OrientedPrism`、有界性、`IsCompletelyFaithfullyFlat` | 1 |
| A0-2 | Constr 4.17・4.18・Rem 4.19 の対象（余単体的対象として）と弱始性の主張、`cechAlexander_isLimitCone` の主張 | A0-1、A0-3c の `IsPrismaticEnvelope` | 2 |
| A0-3a | Def 2.42 | HA/Koszul | 3 |
| A0-3c | Prop 3.13 の普遍性による定義と、Ex 3.14（変数）の場合の存在 (1)(2)(3) | `DeltaAdjoinDivision`、`RelativeFreeDeltaRing`、`deltaPDCompletionStructure`、Lemma 3.7(2) | 3 |
| A0-3b | Lemma 3.7(2)(3) | HA/DerivedCompletion の CompletedFlat*、`CompletelyFlat/*` | 4 |
| A0-3d | Cor 3.12 (a)〜(e) | A0-3b、完備テンソル、有限段の Amitsur、S1 の二補題 | 5 |
| A0-4 | Tor 振幅、Lemma 4.22、Lemma 4.20 | HA/DerivedCompletion の CompletedBaseChange*・Truncation、A0-2 | 6 |

骨組み（主張の型と `sorry` の証明）は 1〜6 の順に `drafts/A0/` に書く。中身を書く段階に入るときは、S2・S3 の状態（∞ 側の窓）と、
A0-3b・A0-3d の HA の部品の読解の結果で、順序を見直す。

## 4. 原典との差（ノート第 4 章 D16〜D18 に加えるもの）

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D19 | Def 4.1 の site の対象は有界 prism (B, IB) 全体 | 向き付き（基底が向き付きなら剛性で自動）。既存規約 D5 の帰結 | 内容は同じ。Lemma 3.7(4) の局所向き付けは使わない |
| D20 | Def 2.42 は単体的可換環の平坦射 | Koszul 複体のホモロジーで述べる離散な言い換え（H⁰ の平坦性と高次の消滅） | 同値。単体的環を持ち込まない |
| D21 | Prop 3.13 は Zariski 局所的な正則列 | 存在は Ex 3.14（多項式代数からの全射の核、変数変換後は変数の部分集合）の場合だけ。定義（普遍性）は一般 | 定理を特別な場合に絞る。A3（Ex 7.9、f_1,…,f_r の正則列）では別の場合が要る |
| D22 | flatTopology は Cor 3.12 で site であることを示してから定義 | 生成される最小の位相として定義し、Cor 3.12 前半を「被覆篩は忠実平坦射で refine できる」という定理に | 同じ位相。定義の段階で公理の証明を要らなくする |
| D23 | Construction 4.18 の Čech 余脈体は完備テンソルの反復 | 変数の添字で直接書く（B_0^n = A[X_{S × [n]}]^∧、余単体的構造は添字集合の写像から）。決定 11-02 | 同じ対象。`PrismOver` に一般の余積がないので Mathlib の `cechConerve` は使えない |
| D24 | Lemma 4.21（étale 局所化）で smooth に延ばす | 多項式代数に限り、A2 の左 Kan 延長で済ませる | 定理の範囲を絞る |

## 5. 紙で確かめる項目（骨組みを書く前に）

1. §2.5 の存在定理：Z = dY とおいた自由 δ 環が「prism への普遍性」を満たすこと（d の正則性を使う箇所、δ 射であることの確認）。
2. §2.5 の最後：R = (A/d)⟨X_S⟩ と B_0 = A[X_{|R|}]^∧ について、J_0 B_0 が「変数の部分集合 ＋ (d)」になる変数変換（係数の持ち上げの切断、完備多項式環の
   三角型の自己同型が可逆であること）。
3. §2.8：`cechAlexander` が `PrismOver P R` の余積による Čech 脈体であること（envelope が B_0 のテンソルを余積に送る、Constr 4.17 の最後の文）。
4. §2.7：各構成の濃度評価。
5. §2.6(c)：有限段の Amitsur 複体の完全性（忠実平坦な底変換後の収縮ホモトピー）と、Milnor 列による完備版。(p^n, d^n) 冪の Koszul 塔で述べる形。
6. §2.6(d)：S1 の二補題（単射で生成される篩の降下 ⇔ Čech 脈体の降下、生成系で十分）の正確な仮定（押し出しの存在）。

## 6. 決定（2026-11-02、ユーザー）

1. Tot の表現：Mathlib の `alternatingCofaceMapComplex`（非正規化）を主にし、D(A) の Δ 上の極限との一致は G10 で結ぶ。正規化版
  （Dold–Kan）は計算で小さい複体が要るときだけ。∞ 圏の Tot（lim_Δ）と複体の Tot は別物で、G10 が橋。
2. §2.8 の Čech 余脈体は変数の添字で直接書く（(b)、D23）。理由：`PrismOver P R` には一般の有限余積がない（一般の Prop 3.13 が要る）ので
  Mathlib の `Arrow.cechConerve` の instance が入らない。S3 の補題は「U^n を U の (n+1) 個の余積として示す余錐のデータ」を仮定にとる形で
  述べる（∞ 層の設計書 §1 に反映）。
3. HA の部品（CompletedFlat*、CompletedBaseChange*）の読解は、論文の層の区切り 2b（DerivedCompletion 第二層）が main に入り
  改名表が届いてから。それまで A0-3b・A0-3d・A0-4 は設計書 §2.6・§2.9 の数学の形で止め、S1・S2・S6・A0-1・A0-2 の骨組みを先に書く。
