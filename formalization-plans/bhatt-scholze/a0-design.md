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
- 含まない：§4.2（Constr 4.9、Lemma 4.10、Thm 4.11、Cor 4.12）は A1。Rem 4.2〜4.4・4.7、Lemma 4.21 は不要（ノート第 4 章の判定）。Rem 4.5 は、原典の位相の比較（Zariski・Nisnevich・étale）そのものは不要だが、裏の一般論「位相を粗くしても層の RΓ は変わらない」（drafts/Sheaves/GlobalSections の `derivedGlobalSections_of_le`）を S2 で使う（A5 の Prop 8.5 が位相によらないことに使う。11-07 追記）。
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
| Lemma 3.7(2) | 定理。一般の形（向き付き基底、導来完備な M） | `isDiscrete_of_completelyFlat_boundedPrism`（drafts/A0/FlatDescent、11-07） | HA の CompletedFlat{BoundedTorsion,BoundedComparison,RegularModule}（加群の版のみ） | A0-3b |
| Lemma 3.7(3) | 定理。一般の形（対象の対応） | `exists_boundedPrism_of_completelyFlat`（FlatDescent） | `OrientedPrism.Hom`、`ofDistinguished`、`IsCompletelyFlat`、剛性 `map_ideal_eq` | A0-3b |
| Cor 3.12 | 定理。**固定基底 (A,(d)) 上の site (R/A)_Δ の場合**（site の公理、O_Δ・Ō_Δ が層、導来降下） | §2.6（FlatDescent ＋ PrismaticSite の `flatTopology_refine`） | 押し出し＝完備テンソル（BS/Perfectoidization/CompletedTensor）。Amitsur の完全性はなし | A0-3d |
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
| Lemma 4.22 | 定理。一般の形 | `Derived.completedBaseChange_tot_comm`（drafts/A0/BaseChange、11-07） | HA/DerivedCompletion（CompletedBaseChange*、Truncation） | A0-4 |
| Lemma 4.20 | 定理。**多項式代数 (A/d)⟨X_1,…,X_r⟩ の場合**（11-07 に一般形から絞った） | `prismaticCohomology_baseChange`・`hodgeTateCohomology_baseChange`（BaseChange） | Lemma 4.22、Rem 4.19 の `cechAlexanderAffine_baseChange` | A0-4 |
| Rem 4.2〜4.4・4.7、Lemma 4.21 | 不要 | — | — | — |
| Rem 4.5 | 一般論の部分だけ（S2） | `derivedGlobalSections_of_le`（drafts/Sheaves/GlobalSections） | — | 原典の位相の比較そのものは不要（11-07） |

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
  原典の「(p, IB) 完全忠実平坦」。これは原典 Def 3.2(3) の「(忠実) 平坦な prism の射」の定義そのもの（11-07 訂正：以前の「Lemma 3.7(3) により」は
  不要。Lemma 3.7(3) は逆向きの構成、FlatDescent の `exists_boundedPrism_of_completelyFlat`）。
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
  単体的可換環の平坦射。Lean では連結な（単体的）可換環の射の平坦性の定義（HA 7.2.2.10 の形）をホモロジーで書く：
  H₀(Kos(B; p,d,x)) = B/(p,d,x) が H₀(Kos(A; p,d)) = A/(p,d) 上平坦で、**すべての i について**自然な射
  H_i(Kos(A; p,d)) ⊗_{A/(p,d)} B/(p,d,x) → H_i(Kos(B; p,d,x)) が同型（差 D20）。
  **訂正（2026-11-02、Codex レビュー W9-I-01）**：以前の「高次ホモロジーが消える」は誤り。基底の Koszul 複体にも高次ホモロジーがある
  （d は正則なので Kos(A; p,d) ≃ Kos(A/d; p) で H₁ = (A/d)[p]；結晶 prism (Z_p,(p)) では H₁ = F_p、perfectoid R = A/d に p ねじれがあるときも非零）。
  正しい条件は基底のホモロジーの底変換同型。変数の場合（B = A{S}^∧ は A 上 (p,d) 完備平坦、X は B/(p,d) で正則）はこの条件を満たす。
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
- **置いた宣言（11-07、drafts/A0/FlatDescent.lean。2b 後に HA の名前を確かめて区分 D を解いた）**：
  - D(A) の対象の完全平坦性 `Derived.IsCompletelyFlatObject I M`：原典 §1.2 の定義そのまま（I 冪ねじれの任意の加群 N について
    M ⊗^L_A N が次数 0 に集中。∞ 関手 `tensorWith M` と drafts/DerivedGeneral の `discreteModuleEmbedding`・`IsConnectiveAt`・`IsCoconnectiveAt`）。
    本体の `IsCompletelyFlat` は加群（Tor の消滅）の版で、離散な M で一致する（比較の補題は中身の段階）。
  - Lemma 3.7(2) `isDiscrete_of_completelyFlat_boundedPrism`：**一般形**。M は導来 (p,d) 完備（`Derived.IsDerivedComplete`）を仮定
    （原典の証明が使い、直後の注意も「derived complete」の圏で述べる）。結論：H^i(M) = 0（i ≠ 0）、H⁰ が古典的 (p,d) 完備（`IsAdicComplete`）、
    dⁿ ねじれなし、H⁰/dⁿ の p 冪ねじれが有界。
  - Lemma 3.7(3) `exists_boundedPrism_of_completelyFlat`：導来 (p,d) 完備で (p,d) 完全平坦な δ-A 代数 B について、(B, f(d)) が有界な向き付き
    prism で f が prism の射。原典の「圏の同一視」のうち対象の対応（射は δ-A 射そのもの、逆向き J = dB は剛性 `map_ideal_eq`）。
    `PrismOver.IsFaithfullyFlat` は原典 Def 3.2(3) の定義そのもの（(p,I) 完全忠実平坦）で、Lemma 3.7(3) を経由しない（§2.2 の記述を訂正）。
  - Cor 3.12（**固定基底 (A,(d)) 上の site の場合**。原典は全有界 prism の圏）：(a) `PrismOver.isFaithfullyFlat_of_isIso`・`PrismOver.IsFaithfullyFlat.comp`・
    `PrismOver.exists_isPushout_isFaithfullyFlat`（`IsAdmissibleCutoff` の下、Mathlib の `IsPushout`）。PrismaticSite の `flatTopology_refine` はこれらから。
    (b) `structurePresheaf_isSheaf`・`reducedStructurePresheaf_isSheaf`（1 圏の層、`Presheaf.IsSheaf`）。(c) `structurePresheafDerived_isLimit_singleton`
    （忠実平坦な単一射の篩での `restrictionCone` が極限錐）。(d) `structurePresheafDerived_isSheaf`、Ō 版 `reducedStructurePresheafDerived_isSheaf`
    （Ō_Δ の D(A) 値は `reducedStructurePresheafDerived` := O_Δ ≫ `tensorWith (A/d)`、新しい sorry の定義は置かない）。(e) `prismaticCohomology_isLimit`
    （Δ_{R/A} は O_Δ 自身の極限錐の頂点。`derivedGlobalSections_of_isSheaf` で証明済みの形）。古典的 RΓ・hypersheaf との一致（旧 (e)）は述べない（D17）。
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
  **R の範囲（11-03、BS-D1 の質問への回答）**：比較定理の仮定は `h : HasEnvelopes P R`（Čech–Alexander 模型 C^• が存在し各項の濃度 ≤ cutoff、§2.8 の規約と同じ）、
  `IsAdmissibleCutoff κ`・`IsAdmissibleCutoff κ′`（cutoff ≤ κ、κ^{ℵ₀} = κ）、κ ≤ κ′。一般の p 完備 R で無条件には述べない（一般の Prop 3.13 は A0 の範囲外）。
  多項式代数 R では `hasEnvelopes_of_polynomial` が供給し、E3 に要るのはその場合だけ（A2 は多項式代数からの左 Kan 延長）。結論は包含 ι : 𝒞_κ → 𝒞_{κ′} に沿う
  O_Δ の制限について `derivedGlobalSections` を結ぶ D(A) の可逆な辺（頂点の等号は主張しない、W9-I-03）。証明は両辺を同じ Tot O_Δ(C^•) と結ぶ
  （`prismaticCohomology_eq_cechAlexanderTot` を κ と κ′ で）。**置き場所**（11-03）：包含関手 ι と O_Δ の制限は PrismaticSite.lean に残し、`HasEnvelopes` を使う
  比較定理本体は CechAlexander.lean の Tot 比較の直後に置く（同じ名前空間。CechAlexander が Site と Envelope を import するので逆向きは循環。W9-III-09 の「定義は先、後段の定理は後」と同じ）。

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
  有限振幅であることは A1 で示す。**注意（D4-04、11-03）**：この Koszul 版は、原典の「M ⊗^L A/(p,I) の Tor 振幅」（商の版）と、x が標的で正則列でないとき
  最大 r だけずれる（Kos(C′; x) と C′/(x) の差）。Lemma 4.22 の証明は有限性だけを使うので両者は同時に有限で、定理の主張はどちらでも同じ。c の値を記録する
  ときは Koszul 版で数える（Constr 6.1 の α は c = 3：B/p の Tor 次元 ≤ 2 ＋ 標的 Koszul の余分な 1 段。α mod p の通常の Tor 振幅は ≤ 1。a1-design §2.5）。
- Lemma 4.22：J 完備底変換 (−) ⊗̂^L_C C′ は D^{≥0} の余単体的対象の Tot と可換。原典の証明（n 骨格で示し、fiber が D^{≥ n+1−c} に
  あることから各次数で一致）をそのまま。各項が離散な余単体的対象なら Tot は余鎖複体で、底変換後は各列が [−c, 0] に有界な双複体なので
  全複体は各次数で有限和（HA の BoundedAbove*・Truncation の部品）。
- **置いた宣言（11-07、drafts/A0/BaseChange.lean）**：Tor 振幅 `Derived.HasFiniteCompleteTorAmplitude f x c`（一般の可換環 C → C′。A1 の
  HodgeTateComparison の同名の定義と同じ式を A0 の正本として置き直した。A1 の書き直しで A1 側を削除してこちらを参照する）、
  Lemma 4.22 `Derived.completedBaseChange_tot_comm`（**一般形**：D^{≥0}(C) 値の余単体的対象 Δ → D(C) の極限錐を drafts/DerivedGeneral の
  `completedBaseChange f (x の像)` で写すと極限錐）、Lemma 4.20 `prismaticCohomology_baseChange`・`hodgeTateCohomology_baseChange`
  （**R = (A/d)⟨X_1,…,X_r⟩ の場合**、R′ = (A′/d′)⟨X_1,…,X_r⟩ = `prismPolynomialCompletion P' (Fin r)`。結論は D(A′) の可逆な辺の存在）。
  **特別な場合に絞る理由**：E3 の経路で Lemma 4.20 を使うのは Construction 6.1(3)（α）、Prop 6.2（b・c、Rem 4.19 の模型）、Thm 6.4 の帰着
  （a1-design §9.1 の 3、結晶 prism から Z_p へ）で、どれも有限変数の多項式代数。Lemma 4.21 の étale 局所化は使わない（D24）。
  **残る点**：自然な射の指定（原典の「the natural map」）は主張に入れていない。Prop 6.2 (b) で η との両立に使うなら、Rem 4.19 の項ごとの射から
  誘導される辺を定義して主張に含める必要がある（A1 の `polynomialChangeEdge` は CAlg 値で同じことをしている。どちらに置くかは A1 の書き直しと調整）。
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
| D20 | Def 2.42 は単体的可換環の平坦射 | 連結な環の射の平坦性（HA 7.2.2.10）をホモロジーで書く：H₀ の平坦性と、全次数で H_i(基底) ⊗ H₀(標的) ≅ H_i(標的)。（訂正 11-02：「高次の消滅」は誤り、W9-I-01 の反例 (Z_p,(p))） | 同じ定義の書き方。単体的環を持ち込まない |
| D21 | Prop 3.13 は Zariski 局所的な正則列 | 存在は Ex 3.14（多項式代数からの全射の核、変数変換後は変数の部分集合）の場合だけ。定義（普遍性）は一般 | 定理を特別な場合に絞る。A3（Ex 7.9、f_1,…,f_r の正則列）では別の場合が要る |
| D22 | flatTopology は Cor 3.12 で site であることを示してから定義 | 生成される最小の位相として定義し、Cor 3.12 前半を「被覆篩は忠実平坦射で refine できる」という定理に | 同じ位相。定義の段階で公理の証明を要らなくする |
| D23 | Construction 4.18 の Čech 余脈体は完備テンソルの反復 | 変数の添字で直接書く（B_0^n = A[X_{S × [n]}]^∧、余単体的構造は添字集合の写像から）。決定 11-02 | 同じ対象。`PrismOver` に一般の余積がないので Mathlib の `cechConerve` は使えない |
| D24 | Lemma 4.21（étale 局所化）で smooth に延ばす | 多項式代数に限り、A2 の左 Kan 延長で済ませる | 定理の範囲を絞る |

### 2.8′ Čech 余脈体の余積の脚（11-03、BS-D1 の質問への回答）

`cechAlexander_isCoproduct` は「或る入射族が余積をなす」ではなく、**標準の脚**で述べる：[0] → [n] の n+1 個の頂点の包含（`SimplexCategory.const` の形）を
`cechAlexander.map` で送った射 C^0 → C^n を脚とする余錐が余積（`IsColimit (Cofan.mk (C^n) (fun i => cechAlexander.map (vertex i)))`）。これが S3 の `CechNerveData` の
`proj_map`（単体的構造の射は射影の添字を写す）にそのまま使える形で、§5.1 の計算（各項は自由 δ 環の完備化で、変数の添字の包含が余積の脚）と一致する。
∃ 版が要るならこの標準形から導く。

## 5. 紙で確かめる項目

1〜4 は 2026-11-02 に検証済み（§5.1）。5・6 は A0-3d の前に行う。

1. §2.5 の存在定理：Z = dY とおいた自由 δ 環が「prism への普遍性」を満たすこと。**済**。
2. §2.5 の最後：R = (A/d)⟨X_T⟩ と B_0 = A[X_{|R|}]^∧ について、J が「変数の部分集合 ＋ (d)」に変数変換できること。**済**。
3. §2.8：`cechAlexander` が `PrismOver P R` の余積による Čech 脈体であること。**済**。
4. §2.7：各構成の濃度評価。**済**（A0 の範囲。André と Prop 8.5 の S̃ は見込み）。
5. §2.6(c)：有限段の Amitsur 複体の完全性（忠実平坦な底変換後の収縮ホモトピー）と、Milnor 列による完備版。(p^n, d^n) 冪の Koszul 塔で述べる形。
6. §2.6(d)：S1 の二補題（単射で生成される篩の降下 ⇔ Čech 脈体の降下、生成系で十分）の正確な仮定（押し出しの存在）。

### 5.1 検証の結果（2026-11-02）

記号：(A,(d)) 有界向き付き prism。A{X_S} := 集合 S 上の自由 δ-A 代数（`RelativeFreeDeltaRing S` = A[X_{s,k}]、δ(X_{s,k}) = X_{s,k+1}）、
(−)^∧ := 導来 (p,d) 完備化の H⁰。

**1. 変数の envelope は完備化した自由 δ 環。** B := A{X_S}^∧、J := (d, X_z : z ∈ Z)、C := A{X_{S∖Z} ⊔ Y_Z}^∧、η : B → C を X_s ↦ X_s（s ∉ Z）、
X_z ↦ d·Y_z で定める（自由 δ 環の生成元の普遍性で A{X_S} → C を作り、`existsUnique_deltaPDCompletionHom` で B へ延ばす。C は (p,d) 導来完備）。
- (C, dC) は prism over (A,(d))：δ 構造・完備性は構成から（`deltaPDCompletionStructure`、`pdCompletionH0_self_complete_*`）、p ∈ (d, φ(d)) は A から。
  **d の正則性と C の離散性**は「有界 prism 上の自由加群 M の導来 (p,d) 完備化は離散で古典的完備、d は正則」で、これは直接示せる：
  Kos(A; p^n, d^n) は H⁰ = A/(p^n,d^n)、H⁻¹ = (A/d^n)[p^n]（d 正則）、H⁻² = 0。M 自由なので M ⊗ でも同じ。H⁰ の塔は全射で lim¹ = 0。
  H⁻¹ の塔 (M/d^n)[p^n] は、A/d^n の p 冪ねじれが p^{Nn} で消える（A/d の有界ねじれの d 進 filtration）ので、段 m ≥ (N+1)n から段 n への
  遷移（p^{m−n} 倍と mod d^n）が 0：pro 零で lim = lim¹ = 0。よって M^∧ = lim M/(p^n,d^n)M は離散。d の正則性：M^∧ = lim_n (M/d^nM)^∧_p
  と書き、0 → M/d^n →d→ M/d^{n+1} → M/d → 0 が有界 p ねじれの加群の列なので p 進完備化後も完全。dx = 0 なら各 x_{n+1} ∈ ker(d on (M/d^{n+1})^∧_p)
  = (d^nM/d^{n+1})^∧_p で、その M/d^n への像は 0、よって x = 0。**A0-3c で要る Lemma 3.7(2) はこの自由加群の場合だけ**（一般形は Cor 3.12(a) の押し出しで）。
- (p,d) 完全平坦性：M^∧ ⊗^L_A A/(p,d) ≃ M ⊗_A A/(p,d)（導来完備化は Kos との ⊗^L を変えない）で、M/(p,d)M は A/(p,d) 上自由。
- 普遍性：prism (D, dD) over (A,(d)) と δ-A 射 g : B → D で J·D ⊆ dD とする。g(X_z) = d·c_z で c_z は一意（d は D で正則）。h₀ : A{X_{S∖Z} ⊔ Y_Z} → D を
  X_s ↦ g(X_s)、Y_z ↦ c_z で（`existsUnique_relativeFreeDeltaHom`）、D が (p,d) 導来完備なので h : C → D へ延ばす。h ∘ η = g は、B = A{X_S}^∧ からの
  δ 射が生成元の値で決まることから、X_s と X_z（h(dY_z) = d c_z = g(X_z)）で確かめれば足りる。一意性：h′ ∘ η = g なら d·h′(Y_z) = g(X_z) = d c_z で
  h′(Y_z) = c_z（d 正則）、h′(X_s) = g(X_s)、生成元の値で決まるので h′ = h。標的 D に有界性は要らない。
- `IsPrismaticEnvelope` の他の欄：`base_hom`（d ↦ d·1）、`ideal_eq`（Q.ideal := (η(d)) と定義）、`map_le`（X_z ↦ dY_z）。

**2. 大きい模型の変数変換。** R := (A/d)⟨X_T⟩（p 完備化した多項式代数）、T′ := {X_t} ⊆ |R|、B_0 := A[X_f : f ∈ |R|]^∧、ev : B_0 → R（X_f ↦ f）は全射で
(p,d) 進連続。A[X_{T′}]^∧ → R は全射で核は (d)（A⟨X_T⟩/d = (A/d)⟨X_T⟩）。各 f ∈ |R| に持ち上げ f̃ ∈ A[X_{T′}]^∧ を選び（選択。f ∈ T′ では f̃ := X_f）、
σ : B_0 → B_0 を X_f ↦ f̃ とする連続 A 代数の自己準同型とすると、g − σ(g) ∈ (X_f − f̃)^−、σ(g) ∈ A[X_{T′}]^∧、g ∈ J_0 ⇒ ev(σ(g)) = 0 ⇒ σ(g) ∈ (d)。
よって J_0 = (d, X_f − f̃ : f ∉ T′)^−。B := A{X_{|R|}}^∧ で、τ : B → B を X_f ↦ X_f − f̃（f ∉ T′）、X_f ↦ X_f（f ∈ T′）とする δ-A 自己同型
（逆は X_f ↦ X_f + f̃。完備 δ 環への生成元の値で定義）。τ は変数のイデアル (d, X_f : f ∉ T′) を (d, X_f − f̃ : f ∉ T′) に写し、閉包も保つ。
したがって (B, J) ≅ (B, (d, Z)^−)（**閉包つき**。無限変数では代数的イデアル (d, Z) は閉じていない：例えば Σ p^n Z_n は閉包に入るが (d, Z) には入らない。
W9-I-09 で訂正）with Z = |R| ∖ T′。(d, Z) と (d, Z)^− の envelope は同じ（`IsPrismaticEnvelope.of_closure`）なので、変数の場合の存在定理を当ててよい。
退化した場合 A/d = 0（R = 0）は変数を R の部分集合として埋め込む記述を使わず別に扱う（envelope は零 prism）。**n 項目も同じ**：B_0^n = A[X_{|R| × [n]}]^∧、ev^n はすべての copy を評価し、
座標を copy 0 の T′ × {0} に取れば Z^n = |R| × [n] ∖ (T′ × {0})。
- **J の定義の注意**：J := ker(B → (B/J_0B)^∧_p) の完備化は**導来 p 完備化の H⁰**で取る（原典の「derived (p,I)-complete ideal generated by J_0」）。
  普遍性の標的 D は有界でないので D/dD は p 進分離とは限らないが、導来 p 完備ではある（D が導来完備で cofiber で閉じる）。よって
  B/J_0B → D/dD は (B/J_0B)^∧ を経由し、J は dD に入る。古典的閉包で定義すると有界でない D で破綻しうる。骨組みの `cechKernel` はこの形
  （一変数 Koszul 完備化の H⁰、E3 の `completionRing` と同じ道具。`PDCompletionH0 _ p 0` は使わない）。
- 閉包を取っても envelope は変わらない（`IsPrismaticEnvelope.of_closure`）：上と同じ理由。

**3. Čech 脈体は C^0 の余積。** D ∈ PrismOver P R について、Hom_{PrismOver}(C^n, D) ≅ {δ-A 射 g : B^n → D | J^n·D ⊆ dD、誘導される R → D/dD が sec_D}
≅ {(b_{f,i})_{f ∈ |R|, i ∈ [n]} ⊆ D | b_{f,i} ≡ sec_D(f) mod dD}（自由 δ 環の生成元の普遍性と、J^n の条件が「B_0^n → D/dD が R を経由して sec_D に等しい」
ことと同値であること。2 の注意により閉包も自動）≅ ∏_{i ∈ [n]} {(b_f)_f | b_f ≡ sec_D(f)} ≅ Hom(C^0, D)^{n+1}。全単射は自然で、i 番目の成分は
余面 [0] → [n]（0 ↦ i）が誘導する射 C^0 → C^n による前合成。よって C^n は C^0 の (n+1) 個の余積で、C^• はその Čech 脈体（余単体的構造は余積の
普遍性で決まる射と一致）。**弱始性**：D/dD → D は全射でないが D → D/dD は全射なので、各 f に b_f ∈ D を sec_D(f) の持ち上げとして選べば
Hom(C^0, D) ≠ ∅（選択）。R に smooth 性は不要。

**4. 濃度。** λ := #A + #R + ℵ₀、κ := λ^{ℵ₀}。κ^{ℵ₀} = κ、κ ≥ 2^{ℵ₀} ≥ ℵ₁。
- A0：A 上の ≤ λ 変数の多項式環は ≤ λ、その完備化（Cauchy 列の商）は ≤ λ^{ℵ₀} = κ。C^n・envelope も同じ。押し出し (B′ ⊗̂ C)^∧ は ≤ κ^{ℵ₀} = κ。
  完全化（Lemma 3.9、列の極限）は ≤ κ^{ℵ₀} = κ。
- A5・A6（見込み。実装時に確かめる）：Prop 8.5 の S̃（p 乗根の添加の反復）は ω 段で全元が根をもち ≤ κ。André 拡大（Thm 7.14）は各段 ≤ κ、
  ω₁ 段の反復で ≤ κ·ℵ₁ = κ。`Andre/Transfinite` の飽和の基数の取り方は A5 で確認する。
- 本質的小ささ：#B ≤ κ なら B は濃度 κ の固定した型 Ω の部分型と全単射で、環・δ・prism・射の構造を移せる。構造付きの Set Ω の全体は Type u の集合。
  δ 構造と OrientedPrism の環同型に沿う移送の補題が要る（`isIntegralPerfectoid_of_ringEquiv` と同型の補題）。

**帰結（骨組みへの反映）**：(a) A0-3c の存在定理の証明に要る Lemma 3.7(2) は自由加群の場合で、直接証明できる（一般形は A0-3d で）。
(b) `cechKernel` は導来 p 完備化 H⁰ への核で定義する（`PDCompletionH0 _ p 0` ではない）。(c) `cechAlexander_isCoproduct` と
`cechAlexanderObj_weaklyInitial` は Hom 集合の計算で、Prop 3.13 の普遍性と自由 δ 環の普遍性だけを使う。(d) κ の条件は `cardinal_envelope_le` の形で足りる。

## 6. 決定（2026-11-02、ユーザー）

1. Tot の表現：Mathlib の `alternatingCofaceMapComplex`（非正規化）を主にし、D(A) の Δ 上の極限との一致は G10 で結ぶ。正規化版
  （Dold–Kan）は計算で小さい複体が要るときだけ。∞ 圏の Tot（lim_Δ）と複体の Tot は別物で、G10 が橋。
2. §2.8 の Čech 余脈体は変数の添字で直接書く（(b)、D23）。理由：`PrismOver P R` には一般の有限余積がない（一般の Prop 3.13 が要る）ので
  Mathlib の `Arrow.cechConerve` の instance が入らない。S3 の補題は「U^n を U の (n+1) 個の余積として示す余錐のデータ」を仮定にとる形で
  述べる（∞ 層の設計書 §1 に反映）。
3. HA の部品（CompletedFlat*、CompletedBaseChange*）の読解は、論文の層の区切り 2b（DerivedCompletion 第二層）が main に入り
  改名表が届いてから。それまで A0-3b・A0-3d・A0-4 は設計書 §2.6・§2.9 の数学の形で止め、S1・S2・S6・A0-1・A0-2 の骨組みを先に書く。
  **11-07**：2b が main に入ったので A0-3b・A0-3d・A0-4 の主張の型を drafts/A0/FlatDescent.lean・BaseChange.lean に置いた（§2.6・§2.9 の「置いた宣言」）。
  HA の部品は加群の版（CompletedFlat*）で、D(A) の対象の版・Amitsur の完全性・完備底変換の ∞ 関手は未（入口は drafts/DerivedGeneral）。


> **11-12 夜の追記**：D22 は本体では採らなかった。本体の `flatTopology`（`Prismatic/FlatSiteSheaf`）は原典どおり Cor 3.12（`exists_isPushout_isFaithfullyFlat`）で被覆の引き戻しの公理を示して `flatCoverage … .toGrothendieck` で置いている。§1 の表と §2.6 で drafts の宣言として挙げた Lemma 3.7 (2)(3)・Cor 3.12 の正本は本体（design-status の記録の訂正）。
