# A3 の設計：Δ が離散な場合（原典 Lemma 7.7・7.8、Example 7.9、Prop 7.10、2026-11-02）

概要：E3 を消す道筋の単位 A3。原典 BS 著者版 §7.2 のうち、導来 prismatic コホモロジー Δ_{R/A} が離散な場合の性質：Lemma 7.7（δ 構造、prism、
弱始対象）、Lemma 7.8（冪等完備な圏の始対象）、Example 7.9（lci 商の Δ は prismatic envelope で始対象）、Prop 7.10（quasiregular semiperfectoid
な S の Δ_S は離散で始 prism、S → Δ_S は p 完全忠実平坦）を、**定義は原典のまま、定理は E3 に要る特別な場合だけ**の方針で形式化するための
項目表・証明の筋・必要な一般論・差の記録・決定待ち。A2（Construction 7.6、HT filtration、(4)(5)）を前提にする。
方針：E3 の経路（Prop 8.5 の semiperfectoid の場合、Cor 8.14、Thm 10.11）で A3 から使うのは、(i) Lemma 7.7(2)(3)（離散な Δ から任意の prism への
写像と始対象）、(ii) Prop 7.10 を S′ = R⟨X_j^{1/p^∞}⟩/(X_j)^∧ と、その帰着先 T = R⟨X_1^{1/p^∞},…,X_r^{1/p^∞}⟩/(X_i − f_i) について、(iii) Ex 7.9 を T の
場合（完全 prism A′ = A_inf(R⟨X^{1/p^∞}⟩) 上、f_i := X_i − f_i）。Lemma 7.7(1) の一般の W₂ の議論は E3 に不要（δ 構造は envelope との同一視か、
p ねじれなしの Frobenius 持ち上げから得る）。
規約：向き付き基底。S′・T の R は perfectoid 環、A = A_inf(R) = 完全 prism（既存の `Prism/Perfectoid`）。Lean の名前は仮。ビルドしない。
使われ方：A4（Lemma 8.4 の「H⁰ は完全 δ 環」）、A5（Prop 8.5 の semiperfectoid の場合：Prop 7.10 で S′_perfd = R0）、A7（Cor 8.14）、
A8（Thm 10.11、Lemma 10.5）。ノート第 7 章の D10・D12（BR30）の再判断（§5）。

## 0. 範囲と前提

- 含む：Lemma 7.7(1)（特別な場合：Δ_R が p ねじれなし、または envelope と同一視できるとき）、(2)、(3)、Lemma 7.8（一般）、Ex 7.9（T の場合と、
  その証明に要る普遍の場合 A_univ = A_0{f_1,…,f_r}^∧）、Prop 7.10（S′ と T の場合）、quasiregular semiperfectoid の定義。
- 含まない：Lemma 7.7(1) の一般形（W₂ の pullback 四角形による導来 δ 構造。D36）、Prop 7.2（全 prism の中の始対象の超限構成。D37）、
  Prop 7.11・Ex 7.12・7.13（quasisyntomic 被覆の持ち上げ。André は証明済み。D38）、quasisyntomic 環の一般論。
- 前提：A2 の Δ（CAlg 値、Kan 延長）、HT filtration と gr = (∧^i L)^∧[−i]、(4) 底変換、(5) 余極限との両立（filtered 余極限、pushout）。
  A0-3c の envelope（変数の場合の存在）。A1-4 の普遍向き付き prism A_0。既存：Cor 7.3（完全試験 prism への始対象）、Thm 7.4、Lemma 3.9（完全化）、
  Thm 3.10（完全 prism ↔ perfectoid）、`Semiperfectoid/RootEnvelope/`（完全 prism 上の X^p − b 族の envelope の離散性・平坦性）。
  （11-13 追記：本体の Ex 7.9 は A1 の A_0 ではなく `universalOrientedPrism`（Ex 2.21・3.4、BS-W15 K2）を使う：`exists_bounded_lciRelationEnvelope`
  （Semiperfectoid/LciEnvelopeExistence:142）。）

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Lemma 7.7(1) | 定理。**特別な場合**：(1′) Δ_R 離散かつ p ねじれなし ⇒ φ_R から δ 構造（Rem 2.2）。(1″) Δ_R ≅ prismatic envelope なら envelope の δ 構造 | `deltaStructure_of_discrete_pTorsionFree`、`deltaStructure_of_envelopeIso` | Rem 2.2 の δ 構造は `Delta/Basic`（要確認：p ねじれなし環の Frobenius 持ち上げから δ） | A3-2 |
| Lemma 7.7(2) | 定理 | `isPrism_of_discrete` | 導来 (p,d) 完備性（A2 の値の圏）、Δ̄ 離散 | A3-1 |
| Lemma 7.7(3) | 定理（弱始性の射は一般、δ 射であることは (1) の場合） | `prismMapOfDiscrete`、`discrete_weaklyInitial`、`exists_initial_of_discrete` | S2 の極限の普遍性（RΓ = lim over site）、Lemma 7.8 | A3-1 |
| Lemma 7.8 | 定理（一般） | `initial_of_retraction_idempotent` | 圏論。prism の圏の冪等完備性 | A3-1 |
| Ex 7.9 | 定理。T の場合（と普遍の場合） | `prismaticCohomology_lci_eq_envelope` | A0-3c（変数の envelope）、A1-4 の A_0、A2 (4)(5)、HT の p 反転の議論 | A3-3 |
| Prop 7.10 | 定理。S′・T の場合 | `prismaticCohomology_qrsp_discrete`、`_initial`、`_completelyFaithfullyFlat` | Ex 7.9、filtered 余極限、余接複体の全射性（HT） | A3-4 |
| qrsp の定義 | 定義そのまま（原典 Not 7.1：semiperfectoid、**p 冪ねじれ有界**、L_{S/Z_p}[−1] の p 完備化が p 完全平坦。BMS19 Def 4.20） | `IsQuasiregularSemiperfectoid` | 余接複体（A2 の `cotangentWedge 1` を一般の基底 k で、D39）。**有界 p 冪ねじれの条件は W9-I-32 で復元**（他の条件から従わない：S = ∏ O_C/(p^n)） | A3-4 |
| Prop 7.2 | 不要（D37。qrsp では Δ_S が始 prism） | — | 既存 Cor 7.3 は完全試験 prism への始対象 | — |
| Prop 7.11、Ex 7.12・7.13 | 不要（D38） | — | — | — |

（11-13 追記）古典的な部分は BS-W15 K5（main 1d5a7113b）と BS-W17 H5（d6ecc3c58・9d8509776）で本体 `BhattScholze/Semiperfectoid/` などに入った。
Lemma 7.7(1)：`existsUnique_over_of_frobeniusLift`・`existsUnique_over_of_equiv`（DiscreteDelta:35・50）。Lemma 7.7(2)(3)：`OrientedPrism.ofDiscreteDelta`（DiscretePrism:36）、
`PrismOver.homOfFrobenius`（DiscretePrism:101）、`exists_initial_of_primeRegular_evaluation`（PrismRetract:160）。Lemma 7.8：`initial_of_retraction_idempotent`
（CategoryTheory/InitialOfRetraction:53）、`PrismOver.isIdempotentComplete`（PrismRetract:127）。Ex 7.9：`exists_bounded_lciRelationEnvelope_of_classifier`・
`exists_bounded_lciRelationEnvelope`（LciEnvelopeExistence:62・142）。Prop 7.10 の T・S′：`exists_rootRelationAinfEnvelope`、`exists_rootLiftRelationCompletion_initial`、
`exists_rootRelationCompletedInitial`、`exists_rootRelationPrismaticPerfection`（Root* の各ファイル）、完全化と Cor 7.3 は `classicalPrismPerfection`
（Prism/Perfection/ClassicalPrismPerfection:34）と `IsClassicalCor73Comparison`（Cor73PrismComparison:63）。Δ との同一視（A2 の上の主張）は drafts/A3 のまま。
Prop 7.10 の S′ の単位の p 完全忠実平坦性は後回し（design-status §0.2′ の「後回しの項目」(1)。E3 は使わない）。

## 2. 定義の形

### 2.1 離散な Δ（Lemma 7.7、7.8）

- 原典 Lemma 7.7 の仮定は「**Δ̄_{R/A} が次数 0 に集中**」（W9-I-33）。そこから Δ_R の離散性と d の正則性が出る：Δ_R は導来 d 完備で
  Δ_R ⊗^L A/d が離散なので、d 進 Nakayama で Δ_R は離散、H⁻¹(Δ_R ⊗^L A/d) = Δ_R[d] = 0 で d 正則。入口の述語は `IsDiscreteHodgeTate R`
  （Δ̄_R 離散）とし、`IsDiscretePrismatic`（Δ_R 離散かつ d 正則）はそこから導く。Δ_R := H⁰（可換環、`derivedPrismaticCohomology_h0_ring`）。
- (2) `isPrism_of_discrete`：Δ_R（環）は導来 (p,d) 完備（値の圏）、d 正則（上）、p ∈ (d, φ(d)) は A から、δ 構造は (1) から、よって (Δ_R, dΔ_R) は
  向き付き prism。**有界性は自動ではない**：Δ̄_R の p 冪ねじれの有界性を別に示す（Ex 7.9・Prop 7.10 では R の有界ねじれと p 完全平坦性から）。
  R → Δ_R/d は HT filtration の Fil_0（`hodgeTateUnitCAlg`、CAlg の単位）。
- (3) `prismMapOfDiscrete`：任意の prism (B, dB) over (A,(d)) と R → B/dB に対し、A 代数の射 Δ_R → B。構成：R の多項式分解 R_• → R
  （A2 の Kan 延長の bar 分解）について Δ_{R_k} = lim_{(R_k/A)_Δ} O_Δ（S2 の `derivedGlobalSections_of_isSheaf` と Cor 3.12）、B は各 (R_k/A)_Δ の
  対象（R_k → R → B/dB）なので極限の脚 Δ_{R_k} → B、k について両立、余極限で Δ_R → B。φ との可換性は O_Δ の Frobenius の自然性から。
  **δ 射であること（W9-I-34）**：φ と可換な環の射 f : C → B が δ 射であることを p·(f δ_C(x) − δ_B(f x)) = 0 から出すには**写像先 B の p ねじれなし**が要る
  （源の p ねじれなしでは足りない）。原典は (1) の W₂ の構成で一般の B に示す。本書（D36 改訂案、§7.1）では δ 射の主張を **p ねじれなしの標的**
  （Ex 7.9 の普遍 envelope B_univ、Δ_{S′}・Δ_T 自身、完全 prism（W(R^♭) は p ねじれなし））に限定する。E3 の経路で要るのはこの範囲：Ex 7.9 の retraction、
  Prop 7.10 の始性は「p ねじれなしの prism の中で」と「完全化は完全 prism の中で始」の二つで足りる（A5-2 で使うのは後者）。
  `discrete_weaklyInitial`：(Δ_R, dΔ_R) は p ねじれなしの標的に対して弱始。
  また「φ_R が mod p で Frobenius」は HT の gr 上の一致からは出ず（filtration をもつ環で gr の一致は全体の一致を含意しない）、A4 の P⁰ の結論
  （H⁰(Δ_perf) の完全 δ 環性）を A3 の証明に使うと循環する。これは **p ねじれなし環と Frobenius 持ち上げの独立の補題**（G-A3-9：Δ_R/p の
  E∞-F_p 代数としての Frobenius が π_0 で x ↦ x^p、A4 より前に、P⁰ の π_0 の性質の部分だけ）として分離する。
- Lemma 7.8 `initial_of_retraction_idempotent`：冪等完備な圏 C と X ∈ C、恒等関手が C_{X\} → C を経由する F : C → C_{X\} があれば、F(X) の射は
  冪等元で、その retract が始対象。prism の圏の冪等完備性：prism の冪等 δ 自己準同型の像は prism（導来完備性・δ・イデアルは retract で保たれる）。
- `exists_initial_of_discrete`（**W9-I-40 で範囲を明記**）：δ 射の主張を p ねじれなしの標的に限定する（D36 改訂案 (a)）なら、Lemma 7.8 を
  **p ねじれなしの prism の充満部分圏**（Δ_R 自身が p ねじれなしのとき）に適用し、結論もその部分圏での始性。全 prism の中の始性は、Ex 7.9・Prop 7.10 では
  上の envelope の押し出しの普遍性から別に得る（Lemma 7.7(3) を経由しない）。E3 で Lemma 7.7(3) の δ 射が要るのは A5 の完全 prism への脚（p ねじれなし）だけ。

### 2.2 Ex 7.9（lci 商）

**D4-02（11-03、BS-D4 の質問への回答）**：A3 の普遍の場合（A_0{f} の envelope と分類射）は A1 の具体的な普遍向き付き prism に結び付けず、**任意の有界向き付き prism A₀ と
d を保つ分類射 (A₀,(d₀)) → (A,(d))（および f の像）を明示引数**にして述べる。A1 の `universalOrientedPrismRing` は現状 p を引数に取らず `CommRing` インスタンスもない
（停止点 3 で直す）ので、A3 はそれに依存しない。停止点 3（A1）で A1 の具体的な A₀（Ex 2.21・3.4 の普遍向き付き prism、`universalOrientedPrism_hom`）に特殊化する。
（11-13 追記：本体（BS-W15 K5）では分類射を引数に取る形が `exists_bounded_lciRelationEnvelope_of_classifier`（LciEnvelopeExistence:62）、
`universalOrientedPrism` への特殊化が `exists_bounded_lciRelationEnvelope`（:142、:150 で `existsUnique_universalOrientedPrismHom` を使う）。）
数学的内容は同じ（原典 Ex 7.9 の「普遍の場合に帰着」は分類射の存在だけを使う）。

設定：(A,(d))、f_1,…,f_r ∈ A で f̄ が A/d 上 Koszul 正則、R := A/(d, f)、R の p ねじれ有界。主張：Δ_{R/A} は離散で d ねじれなし、
(Δ_R, dΔ_R) は (R/A)_Δ の始対象で、envelope B := A{f/d}^∧（(A, (d, f)) の prismatic envelope）に等しい。
- 普遍の場合：A_univ := A_0{f_1,…,f_r}^∧（A_0 は普遍向き付き prism、A1-4 の `universalOrientedPrism`。f_i は自由 δ 変数）。
  (A_univ, (d, f)) の envelope は A0-3c の変数の場合（`exists_prismaticEnvelope_of_variables` with S = {f_1,…,f_r}、Z = 全部、基底 A_0）：
  B_univ = A_0{Y_1,…,Y_r}^∧（f_i = dY_i）、離散・(p,d) 完全平坦・始対象（envelope の普遍性 ＝ (R_univ/A_univ)_Δ の始対象性）。
- 一般へ（**W9-I-39 で再訂正**。以前の「B_univ は A_univ 上 (p,d) 完全平坦」は偽：U := A_univ = A_0{f}^∧、E := B_univ = A_0{Y}^∧、f = dY で、
  U/(p,d) 上 f は正則だが E/(p,d) 上 f は零なので E/(p,d) は U/(p,d) 上平坦でない。Prop 3.13 の平坦性は**小さい基底 A_0 上**であって元の δ 代数 U 上ではない）。
  原典 Ex 7.9 の順序に戻す：
  (i) 分類射 U → A（d ↦ d、f_i ↦ f_i。普遍向き付き prism の普遍性と自由 δ 環）は有界 prism の射（U/d = (A_0/d){f}^∧ は p ねじれなし）。
  R = R_univ ⊗̂^L_U A（U/(d,f) ⊗^L_U A = Kos(A; f) mod d は f̄ の Koszul 正則性で A/(d,f) に集中）、A2 (4) で Δ_{R/A} ≃ Δ_{R_univ/U} ⊗̂^L_U A。
  (ii) **B := E ⊗̂^L_U A（CAlg の完備導来テンソル。離散性は仮定しない）**。普遍の場合の比較 E ≃ Δ_{R_univ/U}（下）を底変換して B ≃ Δ_{R/A}。
  (iii) Δ_{R/A} は離散で d 正則（HT filtration と R の有界 p 冪ねじれ、下の「離散性」）。よって B = LΛ_I(E ⊗^L_U A) も離散。
  **B の台環の同定（W9-I-41 で訂正：「Tor 独立」は主張しない）**：K := E ⊗^L_U A → N := E ⊗_U A（通常のテンソル）は非正次数の対象の H⁰ 同型。
  主イデアルの導来完備化は非正次数の H⁰ 同型を保つ（既存 `HomologicalAlgebra/DerivedCompletion/BoundedAboveCompletion（2b で改名、旧 CompletionH0Comparison）` の
  `derivedComplexCompletion_h0_map_isIso`、p・d の順に二回）ので H⁰ LΛ_I K ≃ H⁰ LΛ_I N、B は離散なので **B ≃ H⁰ LΛ_I N**（環として：K → N は CAlg の標準射）。
  通常の高次 Tor の消滅は要らず、主張もしない。
  (iv) N の通常の δ 構造（**W9-I-42**：`PerfectDeltaTensor` は完全 δ 環用で使えない）：E → W₂(E) → W₂(N) と A → W₂(A) → W₂(N) は U 上一致するので、
  環の押し出しで s : N → W₂(N)、W₂(N) → N との合成は両因子で恒等ゆえ恒等、よって δ 構造。標的 D への環準同型が δ 射であることも両因子で比較（p ねじれなし不要）。
  完備化：`Delta/Extension/DeltaPDCompletion` の `existsUnique_deltaPDCompletionHom`（通常の δ 環 N の (p,d) 完備化の H⁰ から導来完備な δ 標的への一意延長）を
  上の環同型で B へ移す。envelope の普遍性：prism D over A と R → D/dD に対し、U の f_i は dD に入るので E の A_0 上の envelope の普遍性（A0-3c）で唯一の
  δ-U 射 E → D、A → D と貼り合わせて N → D、完備化の一意延長で B → D。よって (B, dB) は (A,(d,f)) の envelope で、R → B/dB をもつ (R/A)_Δ の
  **全 prism の中の始対象**（D の p ねじれなしは使わない）。有界性は R の有界ねじれと R 上 p 完全平坦な完備 HT filtration から。
  普遍比較の底変換で得る φ と、この押し出しの構造射の φ の一致は構造射との両立として記録する。
  **B が A 上完全平坦であることは要求しない**（Codex の修復案の第 2〜4 段）。導来 δ 環は使わない（B は CAlg の対象、δ 構造は離散化後に押し出しから）。
  紙 7 を差し替え。
- 普遍の場合の証明（原典）：B → Δ_R の構成（原典は「単体的可換 δ-A 代数の射」。本書では D36 により、Δ_R が離散であることを先に HT で示してから
  (3) の retraction Δ_R → B を作り、次に B → Δ_R を envelope の普遍性で作る：Δ_R は (1′) により δ 環（A/d・R が p ねじれなし ⇒ Δ_R は p ねじれなし：
  HT filtration の gr が p ねじれなし）、(2) により prism、f ↦ 0 ∈ Δ̄_R なので f ∈ dΔ_R）。B → Δ_R → B は恒等（B の普遍性）。
  B/dB → Δ̄_R の余核は p ねじれなし（retraction、Δ̄_R は R が p ねじれなしなので p ねじれなし）。p を反転して全射：Δ̄_R[1/p] は gr^1 =
  J̄/J̄² = J/(J² + I)（**次数 0 の加群、[−1] は付かない**。J は A のイデアル (d, f)、J̄ := J/I は A/d のイデアル、W9-I-38）で R[1/p] 上 Banach 代数として
  生成され（HT filtration：gr^i = Γ^i(J̄/J̄²)、[Bha12, Claim 3.30] の変種）、B = A{f/d} は f/d を gr^1 へ全射に写す（R の A/d 上の自由分解による標準計算）。
  **A3 の最重量の議論**（§6 の 3）。
- 離散性（W9-I-38 で訂正）：HT filtration の gr^i = (∧^i L_{R/k})^∧[−i]、L_{R/k} = (J̄/J̄²)[1]（Koszul 正則な商の余接複体、G-A3-1）、∧^i(M[1]) = Γ^i(M)[i]
  （導来外冪の décalage、G-A3-2）、よって gr^i = Γ^i(J̄/J̄²)[0] は有限自由 R 加群で次数 0 に集中（**全 i ≥ 0 で非零、「有限」ではない**）。
  Fil_0 = R から有限帰納で各 Fil_i は離散で短完全列は R 加群として分裂、通常の余極限 M は非標準的に ⊕_i gr^i で、**R の有界 p 冪ねじれ**が M の
  一様な上界を与える。よって Δ̄_R = LΛ_p M は次数 0 に集中（BS §1.2 の有界ねじれの完備化）。完備圏の余極限なので「遷移が単射だから極限は離散」
  だけでは足りない。普遍の場合はさらに p ねじれなし。

### 2.3 Prop 7.10（quasiregular semiperfectoid）

- 定義 `IsQuasiregularSemiperfectoid S`（原典 Not 7.1 どおり）：S は導来 p 完備、semiperfectoid（perfectoid 環の商）、**p 冪ねじれが有界**、
  L_{S/Z_p}[−1] の p 完備化が p 完全平坦（BMS19 Def 4.20）。**W9-I-32 で有界ねじれの条件を復元**：以前の定義から抜けていたが他の条件から
  従わない（反例：R = ∏_n O_C perfectoid、f = (p^n)_n 正則、S = R/f = ∏_n O_C/(p^n) は perfectoid の商で L̂_{S/Z_p}[−1] ≃ S ⊕ S は p 完全平坦だが
  p 冪ねじれは非有界）。S′・T が有界 p 冪ねじれをもつことは入力として証明する（R の有界ねじれと平坦性から）。
  余接複体は A2 の `cotangentWedge` を基底 Z_p で（D39：一般の基底 k で独立に定義する、W9-I-36）。
- 主張（S qrsp、R → S perfectoid、A = A_inf(R)）：Δ_{S/A} は離散、(Δ_S, dΔ_S) は S 上の始 prism（R によらない）、S → Δ_S/d は p 完全忠実平坦。
  **始性の圏（W9-I-40）**：T の場合は Ex 7.9 の envelope の普遍性で全 prism over A′ の中で始、A′ 上の prism と A 上の prism は Lemma 4.8 で同じ
  （R′ → T → D/dD から A′ → D が一意に持ち上がる）ので A 上でも全 prism の中で始。S′ はその filtered 余極限（有限部分集合の T の完備 filtered 余極限、
  envelope の δ 射の余極限と完備化の普遍性）。完全化は完全 prism の中で始（Lemma 3.9）。
  **公開範囲（W9-I-43）**：始性の定理は E3 に要る **T・S′ に絞って**述べる（§0 の決定どおり）。一般の qrsp S の始性（原典は自然な δ 自己準同型の議論）は
  この経路では供給されないので、骨組みの一般形 `qrsp_initial` は「別単位、E3 不要」と注記する。離散性・平坦性 (a) は一般の qrsp でよい。
- 証明：(a) 離散・平坦：L_{S/R}[−1] p 完全平坦 ⇒ (∧^i L_{S/R})^∧[−i] は p 完全平坦な S 加群で離散（décalage、G-A3-2）⇒ HT filtration の各 gr が
  離散・平坦 ⇒ Δ̄_S 離散・p 完全忠実平坦（exhaustive、完備）。(b) 始対象：Lemma 7.7(3) の冪等元が恒等であること。R を R⟨Y_i^{1/p^∞}⟩ に替えて
  R → S 全射にし（余接複体は不変）、核の生成系 {f_j} で S′ := R⟨X_j^{1/p^∞}⟩/(X_j − f_j)^∧ → S（全射、余接複体で全射）、HT で Δ_{S′} → Δ_S 全射、
  S′ は T = R⟨X_1^{1/p^∞},…,X_r^{1/p^∞}⟩/(X_1 − f_1,…,X_r − f_r) の filtered 余極限、Δ は filtered 余極限と交換（A2 (5)）、T について
  Δ_{T/A} ≃ Δ_{T/A′}（A′ = A_inf(R⟨X^{1/p^∞}⟩)）は **A2 (4) の底変換ではない**（(4) は代数も底変換した対象を比べる。W9-I-35）：perfectoid の射 R → R′ と
  R′ 代数 T について比較射 Δ_{T/A} → Δ_{T/A′}（(4) の Δ_{T/A} ⊗̂_A A′ ≃ Δ_{(T ⊗̂_R R′)/A′} と乗法 T ⊗̂_R R′ → T）が、HT の gr で ∧^i L_{T/R} ≃ ∧^i L_{T/R′}
  （L̂_{R′/R} = 0）、導来 Nakayama で同値。これは A5 の G-A5-17 と同じ補題で、**A2 の隣（G-A2-10）に置いて A3 と A5 から使う**。Prop 7.10 の
  始対象性をこの補題の証明に使わない。Ex 7.9（A′ 上、f_i := X_i − f_i は Koszul 正則）で Δ_{T/A′} は始対象（p ねじれなしの標的の中で、D36 改訂案）。
- **E3 で要る形**：S′ = R⟨X_j^{1/p^∞}⟩/(X_j)^∧（f_j = 0 の場合、Prop 8.5 の最後の段落）について、Δ_{S′} は離散で始 prism、その完全化は
  Cor 7.3 の完全試験 prism の始対象（既存 `exists_perfectoidization_of_perfectPrism_quotient` の構成）に一致（Lemma 3.9 で始 prism の完全化は
  始完全 prism）。これが「S′_perfd = R0」（A5）。
  **既存入口へ渡すデータ（W9-I-44）**：完全 prism は A′ = A_inf(R′)（R′ = R⟨X_j^{1/p^∞}⟩、R → S′ は一般に全射でないので R′ から）、全射 r : A′ → S′ は
  θ と R′ → (R′/(X_j − f_j))^∧ の合成（p 完備な R′ からの商の完備化への全射）、r(d) = 0 は θ(d) = 0、p が A′/d の非単元は R′ ≠ 0 なら p 進分離性から
  （R′ = 0 は零 prism の分岐、`Fact (¬ IsUnit p)` を作らない）。完全化の普遍性は `Prism/Perfection` の `existsUnique_deltaPerfectionPDCompletionHom`
  （非完全な源から完全・完備な標的への一意延長）で、`existsUnique_perfectDeltaPDPrismHom`（源が既に完全）ではない。二つの候補は完全試験 prism の圏の
  始対象として S′ からの単位と両立する唯一の同型。
- RootEnvelope の再利用：`Semiperfectoid/RootEnvelope/` は完全 prism 上の X^p − b 族の割り算包 A{(X^p − b)/d}-型の離散性・p 完全忠実平坦性・
  完全化と perfectoid 候補の一致を示している。T の envelope A′{(X_i − f_i)/d}^∧（X_i は p 冪根をもつ変数）と形が近く、A3-3・A3-4 で
  Ex 7.9 の envelope の計算（特に完全化の同一視）に転用できる見込み。設計時に対応表を作る。
  （11-13 追記：BS-W17 H5 は RootEnvelope を使わず、`Semiperfectoid/RootRelation*`・`RootFamily*` を新しく作った。T・S′ の閉包から
  `Semiperfectoid/RootEnvelope/` には届かない。）

## 3. 必要な一般論（G-A3）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A3-1 | Koszul 正則な商の余接複体：L_{(k/f)/k} ≃ (J/J²)[1]（J = (f)、J/J² は自由 k/f 加群）。Kan 延長の定義（`cotangentWedge 1`）から：k/f = k ⊗^L_{k[x]} k（Koszul 正則）、L は pushout と交換、L_{k[x]/k} = Ω^1 | なし。A2 の定義と P_Σ の pushout | Ex 7.9、Prop 7.10 |
| G-A3-2 | 導来外冪の décalage：∧^i(M[1]) ≃ Γ^i(M)[i]（M 平坦）、p 完全平坦な M について (∧^i L)^∧ の離散性 | なし（Illusie I.4.3.2） | Ex 7.9、Prop 7.10 (a) |
| G-A3-3 | 余接複体の完全列（transitivity triangle）と、全射 S′ → S が余接複体で全射なら HT で Δ_{S′} → Δ_S 全射 | なし | Prop 7.10 (b) |
| G-A3-4 | Δ と filtered 余極限の交換（A2 (5) の系）、envelope と filtered 余極限 | A2-4 | Prop 7.10 (b) |
| G-A3-5 | prism の圏の冪等完備性、retract の始対象（Lemma 7.8） | なし（圏論、短い）。**11-13：済**（`initial_of_retraction_idempotent`（CategoryTheory/InitialOfRetraction:53）、`PrismOver.isIdempotentComplete`（Semiperfectoid/PrismRetract:127）） | Lemma 7.7(3) |
| G-A3-6 | p ねじれなし環の Frobenius 持ち上げから δ 構造（Rem 2.2）、一意性 | 要確認（`Delta/Basic`）。**11-13：済**（`existsUnique_over_of_frobeniusLift`（Semiperfectoid/DiscreteDelta:35）） | Lemma 7.7(1′) |
| G-A3-7 | Ex 7.9 の p 反転の議論：Δ̄_R[1/p] が gr^1 で生成される Banach 代数、[Bha12, Claim 3.30] の標準計算 | なし。A3 の最重量。**11-13：古典的な部分は本体**（`surjective_of_continuous_retraction_of_denseRange`・`surjective_of_dense_filtration_retraction`（Semiperfectoid/LciEnvelopeInvertP）、`surjective_of_dense_dividedPower_generators_retraction`（LciEnvelopeInvertPGenerators:44）） | Ex 7.9 |
| G-A3-8′ | 既存 Cor 7.3 入口（`exists_perfectoidization_of_perfectPrism_quotient`）への A′・r・非単元・零環の分岐の供給（W9-I-44） | 既存の型 | §2.3 |
| G-A3-8 | 始 prism の完全化は始完全 prism（Lemma 3.9 の普遍性）、既存 Cor 7.3 の対象との一致 | `Prism/Perfection`（`existsUnique_perfectDeltaPDPrismHom`）、`Semiperfectoid/Perfectoidization`。**11-13：本体（BS-W17 H5）が使ったのは `classicalPrismPerfection`（Prism/Perfection/ClassicalPrismPerfection:34）**、比較は `IsClassicalCor73Comparison`（Semiperfectoid/Cor73PrismComparison:63） | Prop 7.10 → A5 |
| G-A3-9 | p ねじれなし環 C と Frobenius 持ち上げ φ_C：φ_C が mod p で x ↦ x^p であることの判定。**A2 の模型から来る φ_R が C/p の E∞-F_p 代数の Frobenius 演算を誘導するという比較を含む**（π_0 への作用が p 乗という性質だけでは出ない、W9-I-45）。A4 の P⁰ の π_0 の部分を前倒しし、A4 の結論を使わない。段 II で A4 の P⁰ と同時に検証 | なし（W9-I-34・45） | (1′) |
| G-A3-10 | (a) 通常の δ 環の押し出し N = E ⊗_U A の δ 構造（W₂ への切断の貼り合わせ）と δ-A 射の普遍性 Hom_{δ-A}(N, D) = Hom_{δ-U}(E, D)（非完全な δ 環。`PerfectDeltaTensor` は使えない、W9-I-42）；(b) 完備化の H⁰ 比較：K = E ⊗^L_U A → N は H⁰ 同型で、LΛ_I 後も H⁰ 同型（既存 `derivedComplexCompletion_h0_map_isIso`、W9-I-41）；(c) `existsUnique_deltaPDCompletionHom` で完備化の一意延長 | (b)(c) は既存、(a) は Delta/ の隣に。**11-13：(a) も本体**（`tensorDeltaStructure`・`tensorDeltaStructure_isDeltaHom_iff`（Delta/Basic/Tensor:101・135、BS-W15）） | §2.2 (iii)(iv) |

## 4. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D36 | Lemma 7.7(1)：W₂ の pullback 四角形と単体的余単体的 δ 環 F_A(R) から、離散な Δ_R の δ 構造；(3) の δ 射は (1) から任意の prism へ | (1′) p ねじれなしの場合（Rem 2.2）と (1″) envelope と同一視できる場合だけ証明する。**(3) の δ 射は p ねじれなしの標的（B_univ、Δ_{S′}・Δ_T、完全 prism）に限定**（W9-I-34、§7.1 の決定項目）。一般形は述べない | E3 で (1) が要る場面はこの二つ（Lemma 8.4・Cor 8.14 の H⁰(Δ_perf) は p ねじれなし、Ex 7.9・Prop 7.10 は envelope）。導来 δ 環（W₂ の E∞ 版）を避ける。φ mod p の補題は A4 と独立に（G-A3-9） |
| D37 | Prop 7.2：全 prism の中の始対象 Δ^init_S を超限構成 | 形式化しない。qrsp S では Δ_S が始 prism（Prop 7.10）、Cor 7.3 の既存の対象はその完全化 | ノート D10 の再判断：Δ^init_S は一般には不要 |
| D38 | Prop 7.11（quasisyntomic 被覆の持ち上げ）、Thm 7.14 の一段を Prop 7.11(2) で | 形式化しない。André（Thm 7.14）は既存の経路（Rem 7.15 の pd 計算）のまま | ノート D12・BR30 の判断：A3 の後も Lean を保つ（Prop 7.11 は E3 に不要） |
| D39 | qrsp の定義は BMS19 の quasisyntomic の理論による | 余接複体（A2 の Kan 延長、基底 Z_p）で直接定義。quasisyntomic の一般論は作らない。**有界 p 冪ねじれを含む原典の条件のまま**（W9-I-32 で訂正） | 定義は同じ。理論の範囲を絞るだけ |
| D40 | Ex 7.9 の B → Δ_R は単体的可換 δ 代数の射（導来 δ 構造） | 先に Δ_R の離散性と p ねじれなし（普遍の場合）を示し、(1′) で δ 環にしてから envelope の普遍性で B → Δ_R。retraction Δ_R → B_univ の δ 性は B_univ の p ねじれなしで（W9-I-34） | 同じ写像。導来 δ 環を避ける |

## 5. ノート第 7 章の再判断（D10・D12）

- D10（Prop 7.2 を経由しない Cor 7.3）：**Lean を保つ**。A3 で Δ^init_S の一般構成は要らない。qrsp S については Prop 7.10 が Δ_S を始 prism として
  与え、既存の Cor 7.3 の対象（完全試験 prism への始対象）はその完全化（G-A3-8）。勉強ノートの D10 の行にこの結論を追記する（BR）。
- D12・BR30（Thm 7.14 の一段を原典の Prop 7.11(2) に揃えるか）：**揃えない**。Prop 7.11 は E3 の経路で使わず、André は証明済み。A3 の範囲に入れない。

## 6. 単位と順序

| 単位 | 内容 | 前提 |
| --- | --- | --- |
| A3-1 | Lemma 7.8（一般）、Lemma 7.7(2)(3)：離散な Δ の prism 性、任意の prism への射（極限の脚）、弱始性、始対象の存在 | A2-2・A2-3、S2、G-A3-5 |
| A3-2 | Lemma 7.7(1′)(1″) | G-A3-6、A0-3c |
| A3-3 | Ex 7.9：普遍の場合（A_0{f}）の envelope（A0-3c）、分類射と底変換、離散性（G-A3-1・2）、retraction と B → Δ_R、p 反転の議論（G-A3-7） | A1-4 の A_0、A2-4、A3-1・2 |
| A3-4 | qrsp の定義、Prop 7.10（S′・T）、Cor 7.3 の対象との接続（G-A3-8）、RootEnvelope の転用 | A3-3、G-A3-3・4・8 |

（11-13 追記：A3-1〜A3-4 の古典的な部分は本体に入った。対応は §1 の表の後の追記。）

骨組みは A3-1 → A3-2 → A3-4（主張）→ A3-3。A3-3 の p 反転の議論（G-A3-7）は一つの補題に閉じ込める（**証明予定**の補題であって恒久的な引用ではない。W9 で計算 ○、W9-III-12）。

## 7. 決定（2026-11-02、ユーザー。いずれも推奨どおり）

1. Lemma 7.7(1) は特別な場合（(1′) p ねじれなし、(1″) envelope と同一視できる）だけ。一般形（W₂ の E∞ 版）は述べない（D36）。
2. D12・BR30：Thm 7.14 の一段は原典に揃えない。Prop 7.11 は A3 の範囲外（D38）。ノート第 7 章の D12 の行に記録、BR30 は閉じる。
3. Ex 7.9 は原典の形（一般の Koszul 正則な f、R の p ねじれ有界）で述べ、証明は普遍の場合への帰着。

### 7.1 追加の決定項目（2026-11-02、Codex W9-I-34 から）

**D36 の射の範囲**：Lemma 7.7(3) の「Δ_R → B が δ 射」を、
- **(a) 推奨**：p ねじれなしの標的 B に限定して示す（p·(fδ_C(x) − δ_B(fx)) = 0 を B で消す）。E3 の経路で要る標的はすべて p ねじれなし：Ex 7.9 の普遍
  envelope B_univ（A_0{Y}^∧）、Δ_{S′}・Δ_T 自身（A = A_inf(R) 上 p 完全平坦で A は p ねじれなし）、完全 prism（W(R^♭)）。Prop 7.10 の始性は
  「p ねじれなしの prism の中で始」と「完全化は完全 prism の中で始（Lemma 3.9 の普遍性）」の二つで述べ、A5-2 は後者だけを使う。
- (b)：原典どおり任意の prism B への δ 射を、(1) の W₂ の構成（または別の自然性の証明）で示す。導来 δ 環（W₂ の E∞ 版）が要り、D36 の趣旨に反する。
併せて G-A3-9（φ_R が mod p で Frobenius：E∞-F_p 代数の Frobenius の π_0 の性質、A4 の P⁰ の一部を前倒し。与えられた φ_R と E∞ の演算の一致の比較を含む）を A3 の補題として置く。
**決定（2026-11-02、ユーザー）：(a)。** Lemma 7.7(3) の δ 射は p ねじれなしの標的に限定し、始性はその充満部分圏で述べる（W9-I-40）。G-A3-9 を A3 の補題に。
**補足（W9-I-39・40 の後）**：Ex 7.9・Prop 7.10 の全 prism の中の始性は envelope の押し出しの普遍性から得るので Lemma 7.7(3) の一般の δ 射は不要になり、
(3) の δ 射が E3 で要るのは A5 の完全 prism への脚（p ねじれなし）だけ。(a) で十分であることの根拠が一つ増えた。

## 8. 紙で確かめる項目

1. §2.2 の普遍の場合：A_univ/d と R_univ が p ねじれなし、f̄ が Koszul 正則、Δ_{R_univ} が p ねじれなし（HT filtration の gr = Γ^i(J/J²) が p ねじれなし）。
2. §2.2 の離散性：gr^i = Γ^i(J̄/J̄²)[0] が全 i ≥ 0 で非零なのに Δ̄_R が離散であること（W9 で確認済み：Fil_i は分裂、通常の余極限は有界ねじれ、
   LΛ_p で離散。「遷移が単射」だけでは足りない）。
3. G-A3-7：[Bha12, Claim 3.30] の計算の prismatic 版（B の f/d が gr^1 = J/(J²+I) へ全射に写ること）。W9 で ○：bar 分解の t̃ と Čech の差商 z = (t_1 − t_0)/d、
   D t̃ = f − dz、Y = f/d ↦ [z]、mod d で z = β(t) ∈ gr¹ は f mod f²。p 反転後の全射性は稠密性＋retraction による像の閉性。
4. §2.3 (b)：R を R⟨Y^{1/p^∞}⟩ に替えても L_{S/R} が変わらないこと、S′ → S が余接複体で全射であること、Δ_{S′} → Δ_S の全射性が HT から出ること。
5. G-A3-8：始 prism の完全化が始完全 prism であること（Lemma 3.9 の普遍性）と、既存の `exists_perfectoidization_of_perfectPrism_quotient` の構成
   （δ 除算 → d ねじれ除去 → 完全化 → 完備化）が (Δ_{S′})_perf に一致すること。
6. RootEnvelope の対応表：`PerfectPrismRootSource*`・`PerfectPrismRootPrismCompletelyFlat` などと T の envelope の対応。
   （11-13 追記：不要になった。W17 H5 は RootEnvelope を使わない（§2.3 の追記）。この二つは今はファイルではなく、`Semiperfectoid/RootEnvelope/PerfectPrism.lean` の中の section の名前。）
7. §2.2 の一般への帰着（W9-I-39・41・42 で差し替え、W9 で ○）：R = R_univ ⊗̂^L_U A（Koszul 正則性）、B := LΛ_I(E ⊗^L_U A) ≃ Δ_{R/A}（普遍の比較の底変換と A2 (4)）、
   Δ_{R/A} の離散性から B の離散性、H⁰ 比較で B ≃ H⁰ LΛ_I(E ⊗_U A)、通常の δ 押し出しと完備化の一意延長から envelope の普遍性と全 prism の中の始性。
