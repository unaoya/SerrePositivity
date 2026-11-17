# A2 の設計：導来 prismatic コホモロジー（原典 Construction 7.6、2026-11-02）

概要：E3 を消す道筋の単位 A2。原典 BS 著者版 Construction 7.6（多項式代数の Δ_{R/A} を、すべての導来 p 完備な単体的可換 A/I 代数へ左 Kan 延長して
導来 prismatic コホモロジーを定め、HT 比較から HT filtration を得る）と、その帰結 (1)〜(5) のうち E3 に要るもの（(1) 多項式代数での一致、
(4) 底変換、(5) 余極限との両立・対称モノイダル性）を、**定義は原典のまま、定理は E3 に要る特別な場合だけ**の方針で形式化するための
項目表・定義の形・必要な一般論・差の記録・決定待ち。A0（Δ の定義と Čech–Alexander 模型）・A1（HT 比較、Cor 4.12）を前提にする。
方針：単体的可換環（animated 環）の ∞ 圏を、有限生成多項式 A/I 代数の圏の sifted 余極限による完備化 P_Σ(Poly_{A/I}) として入れる
（Lurie SAG 25.1.1.1、HTT 5.5.8）。基盤の F2/Presentable に P_Σ の一般論（Yoneda、HTT 5.5.8.10・5.5.8.15、左 Kan 延長、bar 実現）がある（11-13 追記：今の置き場所は `InfinityCategories/Kerodon/LargeInfinityCategories/`（PresentableInfinityCategories・TensorProductsOfInfinityCategories） の `Sigma*`。`InfinityCategories/F2/Presentable` はもうない）。
Δ は Poly 上の関手（A0 の Čech–Alexander ＝ RΓ）の P_Σ への sifted 余極限保存な延長（HTT 5.5.8.15）。値は (p,I) 完備な D(A) の可換代数対象で、
CAlg 値の Δ（G-A1-11）がここで本格的に要る。
規約：向き付き有界基底（D19）。R の始域は「導来 p 完備な単体的 A/I 代数」ではなく P_Σ(Poly_{A/I}) 全体にし、Δ が導来 p 完備化で不変であることを
定理にする（D32）。HT filtration は Postnikov 切り捨ての左 Kan 延長で定義し、その次数商が導来外冪つき余接複体の p 完備化の定義になる（D33）。
Lean の名前は仮。ビルドしない。
使われ方：A3（Lemma 7.7、Ex 7.9、Prop 7.10：離散な場合）、A4（Def 8.2 の Frobenius 余極限）、A5（Prop 8.5）、A7（Prop 8.13）、A8（Thm 10.11）。
E3 の `perfd` の始域（通常の離散 R 代数 `A_R R`）への制限は離散環の P_Σ への埋め込み（§2.3）で。

## 0. 範囲と前提

- 含む：Construction 7.6 の定義（Kan 延長、HT filtration、Frobenius）、(1)（多項式代数で元の Δ と一致）、(4)（底変換）、(5)（sifted 余極限・
  有限余積（テンソル）との両立 ＝ 対称モノイダル性）、離散環の埋め込み、導来 p 完備化での不変性。
- 含まない：(2) étale 層性、(3) quasisyntomic 層性（E3 の経路で使わない。Thm 7.14 の原典の証明が Prop 7.11 で使うが、André は証明済み）。
  形式スキーム X への大域化。
- 前提：A0 の `prismaticCohomology`（多項式代数の Δ、D(A) 値）と Čech–Alexander 模型、A1 の Thm 6.3（HT 比較）と Cor 4.12（底変換）、
  ∞ 層の S2（RΓ）、G-A1-11（CAlg 値の RΓ と模型の E∞ 構造）。

## 0′. D4-01（11-03、BS-D4 の質問への回答）：HT filtration の係数

gr^i = (∧^i L_{S/k})^∧[−i] の完備化は**導来** p 完備化（D(k)_{p-comp} 内、W9 で訂正）。多項式代数では ∧^i L = Ω^i（Shared の `forms`、通常の Kähler 形式）で、
A2 はこれを `discreteEmbedding` で D(k) に入れて DerivedGeneral の `completion`（LΛ_p）を施す。H⁰ の完備化 `completedForms`（Shared）に置き換えると、k の p 冪ねじれが
有界でないとき導来完備化の負次数を失う。有界 prism の k = A/d（有界 p 冪ねじれ）では両者が一致（`completedForms_eq_derivedCompletion_of_boundedTorsion`、Shared）し、
A1 はその同定で設計の Ω̂ を使う。Shared の `forms`・`completedForms` は k・T・p を明示引数にし、`completedForms` に `completedPoly k T p` 加群の構造を付けた。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| 単体的可換 A/I 代数の ∞ 圏 | 定義（P_Σ(Poly_{A/I})、SAG 25.1.1.1） | `AnimatedAlgebra k := SigmaPresheafInfinity (nerve (Poly k))` | F2/Presentable の `SigmaPresheafInfinity`、sigma Yoneda（11-13：今は `InfinityCategories/Kerodon/LargeInfinityCategories/`（PresentableInfinityCategories・TensorProductsOfInfinityCategories）） | A2-1 |
| 離散環の埋め込み | 定義（R ↦ (P ↦ Hom(P, R))、HTT 5.5.8.10） | `discreteToAnimated` | sigma Yoneda の有限余積保存の判定 | A2-1 |
| 導来 p 完備化 | 定義（Δ の不変性の定理に要る） | `derivedPCompletion` on P_Σ（要確認：定義の形。§2.3） | HomologicalAlgebra/DerivedCompletion（1 圏） | A2-4 |
| Constr 7.6 の Δ | 定義そのまま（左 Kan 延長） | `derivedPrismaticCohomology` | HTT 5.5.8.15（`SigmaLeftKan*`）、CAlg_A の sifted 余極限、(p,d) 完備化の ∞ 関手 | A2-2 |
| 同、Frobenius | 定義（Poly 上の φ の Kan 延長） | `derivedPrismaticFrobenius` | A0 の `prismaticCohomologyFrobenius`、φ_{A*} が余極限を保つ | A2-2 |
| HT filtration | 定義（τ^{≤i} Δ̄_P の Kan 延長）。gr^i = (∧^i L)^∧{−i}[−i] は定義（D33） | `hodgeTateFiltration`、`cotangentWedge` | D(A) の t 構造（要確認）、Thm 6.3 | A2-3 |
| (1) 多項式代数で一致 | 定理（充満忠実な包含に沿う左 Kan 延長の制限は元の関手） | `derivedPrismaticCohomology_poly` | HTT 4.3.2.17 系 | A2-2 |
| (2)(3) | 不要 | — | — | — |
| (4) 底変換 | 定理 | `derivedPrismaticCohomology_baseChange` | Cor 4.12（A1）、Kan 延長と底変換の交換 | A2-4 |
| (5) 余極限・対称モノイダル | 定理 | `derivedPrismaticCohomology_tensor`、`_siftedColimit` | 多項式代数の Künneth（HT filtration の gr で、または Čech–Alexander と Eilenberg–Zilber） | A2-4 |
| Rem 4.2（導来 prismatic site） | 不要 | — | — | — |

## 2. 定義の形

### 2.1 animated 代数（P_Σ）

k := A/d。`Poly k`：有限生成多項式 k 代数 k[X_1,…,X_n]（n : ℕ）と k 代数の射の圏（小さい。対象は n、射は k[X_n] → k[X_m]）。
（11-13 追記：本体に同じ定義の `Prismatic.Poly`（BhattScholze/Prismatic/PolynomialCategory:33、D69）がある。drafts/A2 の `Poly` を本体へ移すときはこれに寄せる。）
`AnimatedAlgebra k := SigmaPresheafInfinity (nerve (Poly k))`（F2 の P_Σ：有限積を保つ空間値前層の ∞ 圏）。
- sifted 余極限をもち、Yoneda j : Poly k → AnimatedAlgebra k は充満忠実で、像は compact projective な生成系（HTT 5.5.8.10・5.5.8.22）。
- `discreteToAnimated k : nerve (Under (CommRingCat.of k)) ⟶ AnimatedAlgebra k`：離散 k 代数 R に P ↦ Hom_k(P, R)（有限余積を保つ前層）。
  E3 の `algebraNerve` からの射。R が多項式なら j(R) に一致。
- 原典の「p 完備化した多項式代数」ではなく完備化しない多項式代数を生成系にする（D32。値は完備なので同じ）。

### 2.2 値の圏と Kan 延長

- （11-13 追記：D71〜D73 により、CAlg_A は構造 `EInfinityTheory` を通して使う（`E.CAlg A`）。drafts/A2/DerivedPrismaticCohomology は `E` を明示引数に取る。
  下の `CAlg_R` は 11-02 の書き方。）
- 値の圏 𝒱：(p,d) 完備な E∞-A 代数の ∞ 圏（EInfinity の `CAlg_R`（R := A）の、(p,d) 導来完備な対象の充満部分圏）。sifted 余極限は
  CAlg_A で取って (p,d) 完備化する（完備化は左随伴、G-A2-3）。忘却 U : CAlg_A → D(A) は sifted 余極限を保つ（HA 3.2.3.1。EInfinity/Operad の
  `AlgebraSiftedColimits` はモデルの側。∞ 側の形は要確認）。
- Poly 上の関手 Δ_0 : nerve (Poly k) ⟶ 𝒱：P ↦ Δ_{P^∧/A}（A0 の `prismaticCohomology` の CAlg 版、G-A1-11）。関手性は site の関手性
  （多項式代数の射 P → P′ から (P′/A)_Δ → (P/A)_Δ の制限と RΓ の関手性。S2 の `derivedGlobalSections_map` の CAlg 版）。
- `derivedPrismaticCohomology : AnimatedAlgebra k ⟶ 𝒱`：Δ_0 の sifted 余極限保存な延長（HTT 5.5.8.15：Fun^{Σ}(P_Σ(C), 𝒱) ≃ Fun(C, 𝒱)。
  F2 の `SigmaLeftKanAllColimitPreservation`・`SigmaYonedaColimitPreservationCriterion`）。
- Frobenius：Δ_0 の φ : Δ_0 → φ_{A*} ∘ Δ_0（A0 の `prismaticCohomologyFrobenius`、CAlg 版）を Kan 延長。φ_{A*} は D(A) では全余極限を保つが、
  **CAlg_A では sifted 余極限だけ**（初期対象 A は φ_{A*}A に写り、φ_A が同型でなければ初期対象でない。W9-I-27）。Kan 延長に要るのは sifted の保存で足りる。
  完備版では (p,d) と (p,φ(d)) が同じ位相（φ(d) ≡ d^p mod p）なのでスカラー制限は完備対象を保ち、完備化した sifted 余極限と両立する。
- 離散 R に対する Δ_R := `derivedPrismaticCohomology (discreteToAnimated R)`。E3 の `perfd` の材料（A4）。

### 2.3 HT filtration と導来外冪つき余接複体（D33）

- Poly 上：Δ̄_P := Δ_P ⊗^L_A A/d は D^{[0,n]}（Thm 6.3）。Postnikov 切り捨て τ^{≤i} Δ̄_P（D(A) の標準 t 構造。要確認 G-A2-2）は P について関手的で、
  gr^i := τ^{≤i}/τ^{≤i−1} = H^i(Δ̄_P)[−i] ≅ Ω^i_{P/k}[−i]（Thm 6.3、捻りなし）。
- **値の圏は導来 p 完備な D(k)_{p-comp}（k = A/d）**（W9-I-26 で訂正、2026-11-02）：通常の D(A) で Kan 延長すると完備性が失われる
  （R = k[X_1, X_2, …] では colim_n P_n^∧ = ⋃_n Z_p⟨X_1..X_n⟩ は p 完備でなく R^∧ と異なる。完備圏から D(A) への包含は sifted 余極限を保たない）。
  `hodgeTateFiltration i : AnimatedAlgebra k ⟶ D(k)_{p-comp}` := LΛ_p ∘ Lan（P ↦ τ^{≤i} Δ̄_P）、すなわち完備圏内の sifted 余極限保存延長
  （D(k) で延長してから導来 p 完備化 LΛ_p を取るのと同じ）。増大、exhaustive は**完備圏の余極限**で colim_i^{comp} Fil_i = Δ̄（Kan 延長は余極限と
  交換し、Poly 上では τ^{≤n} = Δ̄_P。D(k) の通常の余極限で述べるなら LΛ_p を付ける）。D(A) へは忘却で。
- `cotangentWedge i : AnimatedAlgebra k ⟶ D(k)_{p-comp}` := LΛ_p ∘ Lan（P ↦ Ω̂^i_{P/k}（Shared/DeRhamPolynomial の `completedForms`、
  p 完備化した多項式代数の微分形式）)。これが (∧^i L_{R/k})^∧ の定義（Illusie の単体的分解による定義の p 完備化と同じ。D33 は「延長後の完備化」込み）。
  i = 1 が p 完備化した余接複体 L^∧_{R/k}。
- 定理：gr^i hodgeTateFiltration ≅ cotangentWedge i [−i]（LΛ_p は完全で cofiber と交換、Kan 延長は余極限と交換、Poly 上で Thm 6.3）。
  原典の「HT 比較 for Δ̄_R」（完備化された gr、BS p.56）。
- **Fil_0 と単位は CAlg で**（W9-I-30）：Poly 上で τ^{≤0}Δ̄_P = H⁰(Δ̄_P) = P^∧ は coconnective な E∞ 代数の連結被覆で、H⁰ → Δ̄_P は E∞ 代数の射。
  これを CAlg_k で（完備化 LΛ_p は対称モノイダルな局所化で CAlg に持ち上がる、G-A2-9）Kan 延長すると、Fil_0 Δ̄_R = R^∧ → Δ̄_R が
  **CAlg の自然変換**になる。E3 の `unit`（`FunctorHom (algebraEmbedding R) perfd`）はこれから（A4-3）。H⁰ 上の環準同型だけでは足りない。
- 原典の捻り {−i} は向き付きなので落とす（D28）。

### 2.4 帰結

- (1) `derivedPrismaticCohomology_poly`：j(P) での値は Δ_0(P)（充満忠実な包含に沿う Kan 延長の制限）。
- 導来 p 完備化での不変性（D32）：animated な導来 p 完備化 R → LΛ_p R（A7-1 の `animatedCompletion`）で Δ_R ≃ Δ_{LΛ_p R}。HT filtration の gr で
  確かめる：(∧^i L_{R/k})^∧ は R の導来 p 完備化で不変（S = LΛ_p R で R/p^n → S/p^n が同値、L_{S/R} の導来 p 完備化が零、推移三角）、filtration は
  exhaustive（完備圏で）、導来 Nakayama。
  **E3 の非完備な離散 R との接続は別**（W9-I-29）：E3 の `completionRing R` は H⁰(LΛ_p R) で、LΛ_p R は一般に離散でない（例：R = Z_p ⊕ Q_p/Z_p で
  LΛ_p R ≃ Z_p ⊕ Z_p[1]）。したがって Δ_R ≃ Δ_{LΛ_p R} から Δ_R ≃ Δ_{completionRing R} は出ない。E3 の欄は定義（D41：perfd R := (completionRing R)_perfd）
  なので Δ の段の一致は不要だが、A8 の `integral`（Thm 10.11 は「整写像の p 完備化」＝animated LΛ_p R について）と A4-3 の `e3Perfd_eq_direct` には
  **perfd の段の比較** (LΛ_p R)_perfd ≃ (π_0 LΛ_p R)_perfd が要る。これは原典 Prop 8.5 の「Δ_{S,perf}・S_perfd は π_0 S のみによる」（系 4）そのもので、
  D45 で「述べない」としていた。→ a5-design §7 の決定項目 6（Prop 8.5 を導来 p 完備な animated S で述べ、系 4 を入れる）。
- (4) `derivedPrismaticCohomology_baseChange`：prism の射 (A,d) → (A′,d′) について Δ_{R_{A′}/A′} ≃ Δ_{R/A} ⊗̂^L_A A′。Poly 上は Cor 4.12（A1）、
  Kan 延長と底変換（余極限を保つ）の交換。
- (5) `derivedPrismaticCohomology_tensor`：Δ_{R ⊗^L_k R′} ≃ Δ_R ⊗̂ Δ_{R′}（CAlg の余積 ＝ 完備テンソル）。Poly 上の Künneth
  （P ⊗ P′ も多項式。HT filtration の gr で Ω^•_{P⊗P′} = Ω^•_P ⊗ Ω^•_{P′}、または Čech–Alexander 模型と Eilenberg–Zilber）、
  両辺が sifted 余極限を各変数で保つことから一般へ。sifted 余極限の保存は構成から。これが「対称モノイダル」の内容（E∞ 代数の余積）。

## 3. 必要な一般論（G-A2）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A2-1 | P_Σ(C) の定義、Yoneda の充満忠実性と compact projective 性、sifted 余極限、HTT 5.5.8.15（Fun^Σ(P_Σ(C), 𝒱) ≃ Fun(C, 𝒱)）、充満忠実な包含に沿う Kan 延長の制限 | F2/Presentable の Sigma*（11-13：今は `InfinityCategories/Kerodon/LargeInfinityCategories/`（PresentableInfinityCategories・TensorProductsOfInfinityCategories）。105 本。`SigmaPresheafInfinity`、`SigmaYoneda*`、`SigmaLeftKan*`、`SiftedColimitPreservation`）。5.5.8.15 の形は要確認 | §2.1・§2.2 |
| G-A2-2 | D(A) の標準 t 構造と Postnikov 切り捨て τ^{≤i}（∞ 関手として）、cofiber の gr、有界性 | **未**（InfinityCategories に t 構造の切り捨て関手は見当たらない。CategoryTheory のトップ階層に 1 圏の t 構造） | §2.3 |
| G-A2-3 | (p,d) 導来完備化の ∞ 関手 D(A) → D(A)_comp（左随伴、完備な対象の充満部分圏、余極限の完備化） | **未**（HomologicalAlgebra/DerivedCompletion は複体の 1 圏） | §2.2・(4)・(5) |
| G-A2-4 | CAlg_A の sifted 余極限と、U : CAlg_A → D(A) がそれを保つこと（HA 3.2.3.1）、CAlg_A の余積 ＝ テンソル（HA 3.2.4.7） | EInfinity/Operad/AlgebraSiftedColimits（モデルの側）。∞ 側（`CAlg_R`）の形は要確認。G12（presentable 性） | §2.2・(5) |
| G-A2-5 | スカラー制限 φ_{A*} : D(A) → D(A) が全余極限を保つこと；CAlg 版は **sifted 余極限**を保つこと（W9-I-27・38） | A0 の要確認 (A) | Frobenius |
| G-A2-6 | 多項式代数の Künneth（Ω^•_{P⊗P′} = Ω^•_P ⊗ Ω^•_{P′}、または余単体的加群の Eilenberg–Zilber） | Shared/DeRhamPolynomial（外冪のテンソル） | (5) |
| G-A2-7 | 離散環の P_Σ への埋め込みと、E3 の `algebraNerve` からの射 | sigma Yoneda の有限余積保存の判定（`SigmaYonedaEvaluation`） | §2.1 |
| G-A2-8 | 余接複体の p 完備化の導来 p 完備化不変性（gr の不変性） | なし | D32 |
| G-A2-10 | **perfectoid の基底拡大での Δ の不変性**（= A5 の G-A5-17 をここに前倒し、W9-I-35）：perfectoid の射 R → R′ と R′ 代数 T について、比較射 Δ_{T/A} → Δ_{T/A′}（(4) と乗法）は HT の gr（L̂_{R′/R} = 0）と Nakayama で同値 | なし | A3（Prop 7.10 の帰着）、A5（semiperfectoid の段） |
| G-A2-9 | 導来 p 完備化 LΛ_p は D(k) の対称モノイダルな局所化で CAlg_k に持ち上がる；完備圏 D(k)_{p-comp} 内の sifted 余極限＝LΛ_p ∘（D(k) の余極限）；LΛ_p は完全で cofiber と交換 | DerivedGeneral/CompletionFunctor の隣（W9-I-26・30） | §2.3 |

G-A2-2・G-A2-3 が主な不足で、どちらも ∞ 基盤の一般論（D(A) の t 構造、完備化の局所化）。調整役に予告する（M12 に続く項目）。

## 4. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D31 | 単体的可換 A/I 代数 | P_Σ(Poly_{A/I})（Lurie の animated 環の定義） | 同じ ∞ 圏（SAG 25.1.1.1） |
| D32 | 始域は導来 p 完備な単体的代数、生成系は p 完備化した多項式代数 | 始域は P_Σ(Poly) 全体、生成系は完備化しない多項式代数。Δ の animated な導来 p 完備化不変性を定理に。E3 の H⁰ 完備化 `completionRing` との接続は perfd の段で Prop 8.5 系 4（W9-I-29） | 値は (p,d) 完備なので同じ。完備化の ∞ 関手を始域で避ける |
| D33 | gr^i = (∧^i L_{R/(A/I)})^∧{−i}[−i]（Illusie の導来外冪つき余接複体） | (∧^i L)^∧ を Ω̂^i の **D(k)_{p-comp} での** Kan 延長（LΛ_p ∘ Lan）として定義（Illusie の定義の p 完備化と一致。W9-I-26 で「延長後の完備化」を明記） | 定義。Mathlib に余接複体はない |
| D34 | (1) は p 完全 smooth な R | 多項式代数（充満忠実な包含の Kan 延長）。(2)(3) は不要 | D29 と同じ範囲 |
| D35 | 値は (p,I) 完備な D(A) の可換代数対象 | CAlg_A の (p,d) 完備な対象（E∞）。D(A) 値の版は忘却で | E3 の二本立て（D18・D27・G-A1-11） |

## 5. 単位と順序

| 単位 | 内容 | 前提 |
| --- | --- | --- |
| A2-1 | `Poly k`、`AnimatedAlgebra k`、Yoneda、`discreteToAnimated` | G-A2-1・7 |
| A2-2 | 値の圏 𝒱、Δ_0（CAlg 版、A0 の Δ と G-A1-11）、`derivedPrismaticCohomology`、Frobenius、(1) | G-A2-3・4・5、A1 の Thm 6.3 は不要 |
| A2-3 | HT filtration、`cotangentWedge`、gr の同一視 | G-A2-2、Thm 6.3 |
| A2-4 | 導来 p 完備化不変性、(4) 底変換、(5) テンソルと sifted 余極限 | G-A2-3・6・8、Cor 4.12 |

骨組みは A2-1 → A2-2 → A2-3 → A2-4。A2-1 は既存の F2 だけで書ける。

## 6. 決定（2026-11-02、ユーザー。いずれも推奨どおり）

1. 値の圏は **CAlg_A（E∞-A 代数）を正**とし、D(A) 値は忘却で得る。G-A1-11（CAlg 値の RΓ と模型の E∞ 構造）を A2 の前提に格上げする。
2. D(A) の t 構造（G-A2-2）と (p,d) 完備化の ∞ 関手（G-A2-3）は **BS が drafts に骨組みを書き**、置き場所は M12 と同じ扱いで調整役に任せる
   （`drafts/DerivedSheaves/` か新しい `drafts/DerivedGeneral/`）。
3. `Poly k` の添字は **n : ℕ**（k[X_1,…,X_n]）。

## 7. 紙で確かめる項目

1. §2.1：離散環 R に対する P ↦ Hom_k(P, R) が有限余積を保つこと（Poly の余積はテンソル）と、R が多項式のとき j(R) に一致すること。
2. §2.3：Kan 延長が cofiber と交換し、exhaustive 性が Poly 上の有界性から出ること。gr^i の同一視の自然性（η^* が多項式代数の射と両立）。
3. (5)：多項式代数の Künneth を HT filtration の gr で示す議論（filtration つきの比較射が gr で同型 ⇒ 同型。完備性と exhaustive 性）。
4. D32：余接複体の p 完備化が R の導来 p 完備化で不変であること（L_{R^∧/R} の p 完備化が零）。
5. E3 の `perfd` に要る形：Δ_R（離散 R）とその Frobenius、H⁰ の環構造（CAlg 版なら H⁰ は環）、`unit`（R → Δ̄_R の H⁰ への射。A4 で S_perfd）。
