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

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Lemma 7.7(1) | 定理。**特別な場合**：(1′) Δ_R 離散かつ p ねじれなし ⇒ φ_R から δ 構造（Rem 2.2）。(1″) Δ_R ≅ prismatic envelope なら envelope の δ 構造 | `deltaStructure_of_discrete_pTorsionFree`、`deltaStructure_of_envelopeIso` | Rem 2.2 の δ 構造は `Delta/Basic`（要確認：p ねじれなし環の Frobenius 持ち上げから δ） | A3-2 |
| Lemma 7.7(2) | 定理 | `isPrism_of_discrete` | 導来 (p,d) 完備性（A2 の値の圏）、Δ̄ 離散 | A3-1 |
| Lemma 7.7(3) | 定理（弱始性の射は一般、δ 射であることは (1) の場合） | `prismMapOfDiscrete`、`discrete_weaklyInitial`、`exists_initial_of_discrete` | S2 の極限の普遍性（RΓ = lim over site）、Lemma 7.8 | A3-1 |
| Lemma 7.8 | 定理（一般） | `initial_of_retraction_idempotent` | 圏論。prism の圏の冪等完備性 | A3-1 |
| Ex 7.9 | 定理。T の場合（と普遍の場合） | `prismaticCohomology_lci_eq_envelope` | A0-3c（変数の envelope）、A1-4 の A_0、A2 (4)(5)、HT の p 反転の議論 | A3-3 |
| Prop 7.10 | 定理。S′・T の場合 | `prismaticCohomology_qrsp_discrete`、`_initial`、`_completelyFaithfullyFlat` | Ex 7.9、filtered 余極限、余接複体の全射性（HT） | A3-4 |
| qrsp の定義 | 定義そのまま（semiperfectoid かつ L_{S/Z_p}[−1] が p 完全平坦、BMS19 Def 4.20） | `IsQuasiregularSemiperfectoid` | 余接複体（A2 の `cotangentWedge 1` を一般の基底 k で、D39） | A3-4 |
| Prop 7.2 | 不要（D37。qrsp では Δ_S が始 prism） | — | 既存 Cor 7.3 は完全試験 prism への始対象 | — |
| Prop 7.11、Ex 7.12・7.13 | 不要（D38） | — | — | — |

## 2. 定義の形

### 2.1 離散な Δ（Lemma 7.7、7.8）

- 「Δ_R が離散」：A2 の `derivedPrismaticCohomology` の U での像が D(A) で次数 0 に集中（`IsCoconnectiveAt 0 ∧ IsConnectiveAt 0`）。
  このとき Δ_R := H⁰（可換環、`derivedPrismaticCohomology_h0_ring`）。
- (2) `isPrism_of_discrete`：Δ_R（環）は導来 (p,d) 完備（値の圏）、Δ̄_R = Δ_R ⊗^L A/d が離散なら d は Δ_R で正則、よって (Δ_R, dΔ_R) は向き付き prism
  （δ 構造は (1) から）。R → Δ_R/d は HT filtration の Fil_0（`hodgeTateFiltration_zero`）。
- (3) `prismMapOfDiscrete`：任意の prism (B, dB) over (A,(d)) と R → B/dB に対し、A 代数の射 Δ_R → B。構成：R の多項式分解 R_• → R
  （A2 の Kan 延長の bar 分解）について Δ_{R_k} = lim_{(R_k/A)_Δ} O_Δ（S2 の `derivedGlobalSections_of_isSheaf` と Cor 3.12）、B は各 (R_k/A)_Δ の
  対象（R_k → R → B/dB）なので極限の脚 Δ_{R_k} → B、k について両立、余極限で Δ_R → B。δ 射であることは (1) の場合に envelope の普遍性か
  p ねじれなしの一意性で。`discrete_weaklyInitial`：(Δ_R, dΔ_R) は (R/A)_Δ の弱始対象。
- Lemma 7.8 `initial_of_retraction_idempotent`：冪等完備な圏 C と X ∈ C、恒等関手が C_{X\} → C を経由する F : C → C_{X\} があれば、F(X) の射は
  冪等元で、その retract が始対象。prism の圏の冪等完備性：prism の冪等 δ 自己準同型の像は prism（導来完備性・δ・イデアルは retract で保たれる）。
- `exists_initial_of_discrete`：(R/A)_Δ は始対象をもち、それは (Δ_R, dΔ_R) の retract。

### 2.2 Ex 7.9（lci 商）

設定：(A,(d))、f_1,…,f_r ∈ A で f̄ が A/d 上 Koszul 正則、R := A/(d, f)、R の p ねじれ有界。主張：Δ_{R/A} は離散で d ねじれなし、
(Δ_R, dΔ_R) は (R/A)_Δ の始対象で、envelope B := A{f/d}^∧（(A, (d, f)) の prismatic envelope）に等しい。
- 普遍の場合：A_univ := A_0{f_1,…,f_r}^∧（A_0 は普遍向き付き prism、A1-4 の `universalOrientedPrism`。f_i は自由 δ 変数）。
  (A_univ, (d, f)) の envelope は A0-3c の変数の場合（`exists_prismaticEnvelope_of_variables` with S = {f_1,…,f_r}、Z = 全部、基底 A_0）：
  B_univ = A_0{Y_1,…,Y_r}^∧（f_i = dY_i）、離散・(p,d) 完全平坦・始対象（envelope の普遍性 ＝ (R_univ/A_univ)_Δ の始対象性）。
- 一般へ：分類射 A_univ → A（d ↦ d、f_i ↦ f_i。普遍向き付き prism の普遍性と自由 δ 環）。R = R_univ ⊗̂ A、B = B_univ ⊗̂ A（envelope の底変換、
  A0-3c）、Δ_R = Δ_{R_univ} ⊗̂ A（A2 (4)）。よって普遍の場合に帰着。
- 普遍の場合の証明（原典）：B → Δ_R の構成（原典は「単体的可換 δ-A 代数の射」。本書では D36 により、Δ_R が離散であることを先に HT で示してから
  (3) の retraction Δ_R → B を作り、次に B → Δ_R を envelope の普遍性で作る：Δ_R は (1′) により δ 環（A/d・R が p ねじれなし ⇒ Δ_R は p ねじれなし：
  HT filtration の gr が p ねじれなし）、(2) により prism、f ↦ 0 ∈ Δ̄_R なので f ∈ dΔ_R）。B → Δ_R → B は恒等（B の普遍性）。
  B/dB → Δ̄_R の余核は p ねじれなし（retraction、Δ̄_R は R が p ねじれなしなので p ねじれなし）。p を反転して全射：Δ̄_R[1/p] は gr^1 =
  (J/(J² + I))[−1] で R[1/p] 上 Banach 代数として生成され（HT filtration：gr^i = Γ^i(J/J²)、[Bha12, Claim 3.30] の変種）、B = A{f/d} は f/d を
  gr^1 へ全射に写す（R の A/d 上の自由分解による標準計算）。**A3 の最重量の議論**（§6 の 3）。
- 離散性：HT filtration の gr^i = (∧^i L_{R/k})^∧[−i]、L_{R/k} = (J/J²)[1]（Koszul 正則な商の余接複体、G-A3-1）、∧^i(M[1]) = Γ^i(M)[i]
  （導来外冪の décalage、G-A3-2）、よって gr^i は次数 0 に集中し、filtration は exhaustive・有限（Γ^i は i ≤ ∞ だが p 完備化で…要確認：gr^i は
  全 i ≥ 0 で非零。exhaustive 性と完備性から Δ̄_R は次数 0 に集中する：各 Fil_i が離散で遷移が単射、極限は離散）。

### 2.3 Prop 7.10（quasiregular semiperfectoid）

- 定義 `IsQuasiregularSemiperfectoid S`：S は p 完備、semiperfectoid（perfectoid 環の商）、L_{S/Z_p}[−1] の p 完備化が p 完全平坦（BMS19 Def 4.20、
  原典 Def 7.? は BMS19 を引用）。余接複体は A2 の `cotangentWedge 1` を基底 Z_p で（D39：`AnimatedAlgebra k` は任意の k で定義されているので
  k = Z_p で L_{S/Z_p}）。
- 主張（S qrsp、R → S perfectoid、A = A_inf(R)）：Δ_{S/A} は離散、(Δ_S, dΔ_S) は S 上の始 prism（R によらない）、S → Δ_S/d は p 完全忠実平坦。
- 証明：(a) 離散・平坦：L_{S/R}[−1] p 完全平坦 ⇒ (∧^i L_{S/R})^∧[−i] は p 完全平坦な S 加群で離散（décalage、G-A3-2）⇒ HT filtration の各 gr が
  離散・平坦 ⇒ Δ̄_S 離散・p 完全忠実平坦（exhaustive、完備）。(b) 始対象：Lemma 7.7(3) の冪等元が恒等であること。R を R⟨Y_i^{1/p^∞}⟩ に替えて
  R → S 全射にし（余接複体は不変）、核の生成系 {f_j} で S′ := R⟨X_j^{1/p^∞}⟩/(X_j − f_j)^∧ → S（全射、余接複体で全射）、HT で Δ_{S′} → Δ_S 全射、
  S′ は T = R⟨X_1^{1/p^∞},…,X_r^{1/p^∞}⟩/(X_1 − f_1,…,X_r − f_r) の filtered 余極限、Δ は filtered 余極限と交換（A2 (5)）、T について
  Δ_{T/A} ≃ Δ_{T/A′}（A′ = A_inf(R⟨X^{1/p^∞}⟩)、底変換 A2 (4)）、Ex 7.9（A′ 上、f_i := X_i − f_i は Koszul 正則）で Δ_{T/A′} は始対象。
- **E3 で要る形**：S′ = R⟨X_j^{1/p^∞}⟩/(X_j)^∧（f_j = 0 の場合、Prop 8.5 の最後の段落）について、Δ_{S′} は離散で始 prism、その完全化は
  Cor 7.3 の完全試験 prism の始対象（既存 `exists_perfectoidization_of_perfectPrism_quotient` の構成）に一致（Lemma 3.9 で始 prism の完全化は
  始完全 prism）。これが「S′_perfd = R0」（A5）。
- RootEnvelope の再利用：`Semiperfectoid/RootEnvelope/` は完全 prism 上の X^p − b 族の割り算包 A{(X^p − b)/d}-型の離散性・p 完全忠実平坦性・
  完全化と perfectoid 候補の一致を示している。T の envelope A′{(X_i − f_i)/d}^∧（X_i は p 冪根をもつ変数）と形が近く、A3-3・A3-4 で
  Ex 7.9 の envelope の計算（特に完全化の同一視）に転用できる見込み。設計時に対応表を作る。

## 3. 必要な一般論（G-A3）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A3-1 | Koszul 正則な商の余接複体：L_{(k/f)/k} ≃ (J/J²)[1]（J = (f)、J/J² は自由 k/f 加群）。Kan 延長の定義（`cotangentWedge 1`）から：k/f = k ⊗^L_{k[x]} k（Koszul 正則）、L は pushout と交換、L_{k[x]/k} = Ω^1 | なし。A2 の定義と P_Σ の pushout | Ex 7.9、Prop 7.10 |
| G-A3-2 | 導来外冪の décalage：∧^i(M[1]) ≃ Γ^i(M)[i]（M 平坦）、p 完全平坦な M について (∧^i L)^∧ の離散性 | なし（Illusie I.4.3.2） | Ex 7.9、Prop 7.10 (a) |
| G-A3-3 | 余接複体の完全列（transitivity triangle）と、全射 S′ → S が余接複体で全射なら HT で Δ_{S′} → Δ_S 全射 | なし | Prop 7.10 (b) |
| G-A3-4 | Δ と filtered 余極限の交換（A2 (5) の系）、envelope と filtered 余極限 | A2-4 | Prop 7.10 (b) |
| G-A3-5 | prism の圏の冪等完備性、retract の始対象（Lemma 7.8） | なし（圏論、短い） | Lemma 7.7(3) |
| G-A3-6 | p ねじれなし環の Frobenius 持ち上げから δ 構造（Rem 2.2）、一意性 | 要確認（`Delta/Basic`） | Lemma 7.7(1′) |
| G-A3-7 | Ex 7.9 の p 反転の議論：Δ̄_R[1/p] が gr^1 で生成される Banach 代数、[Bha12, Claim 3.30] の標準計算 | なし。A3 の最重量 | Ex 7.9 |
| G-A3-8 | 始 prism の完全化は始完全 prism（Lemma 3.9 の普遍性）、既存 Cor 7.3 の対象との一致 | `Prism/Perfection`（`existsUnique_perfectDeltaPDPrismHom`）、`Semiperfectoid/Perfectoidization` | Prop 7.10 → A5 |

## 4. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D36 | Lemma 7.7(1)：W₂ の pullback 四角形と単体的余単体的 δ 環 F_A(R) から、離散な Δ_R の δ 構造 | (1′) p ねじれなしの場合（Rem 2.2）と (1″) envelope と同一視できる場合だけ証明する。一般形は述べない | E3 で (1) が要る場面はこの二つ（Lemma 8.4・Cor 8.14 の H⁰(Δ_perf) は p ねじれなし、Ex 7.9・Prop 7.10 は envelope）。導来 δ 環（W₂ の E∞ 版）を避ける |
| D37 | Prop 7.2：全 prism の中の始対象 Δ^init_S を超限構成 | 形式化しない。qrsp S では Δ_S が始 prism（Prop 7.10）、Cor 7.3 の既存の対象はその完全化 | ノート D10 の再判断：Δ^init_S は一般には不要 |
| D38 | Prop 7.11（quasisyntomic 被覆の持ち上げ）、Thm 7.14 の一段を Prop 7.11(2) で | 形式化しない。André（Thm 7.14）は既存の経路（Rem 7.15 の pd 計算）のまま | ノート D12・BR30 の判断：A3 の後も Lean を保つ（Prop 7.11 は E3 に不要） |
| D39 | qrsp の定義は BMS19 の quasisyntomic の理論による | 余接複体（A2 の Kan 延長、基底 Z_p）で直接定義。quasisyntomic の一般論は作らない | 定義は同じ。理論の範囲を絞る |
| D40 | Ex 7.9 の B → Δ_R は単体的可換 δ 代数の射（導来 δ 構造） | 先に Δ_R の離散性と p ねじれなし（普遍の場合）を示し、(1′) で δ 環にしてから envelope の普遍性で B → Δ_R | 同じ写像。導来 δ 環を避ける |

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

骨組みは A3-1 → A3-2 → A3-4（主張）→ A3-3。A3-3 の p 反転の議論（G-A3-7）は A3 の黒箱として一つの補題に閉じ込める。

## 7. 決定（2026-11-02、ユーザー。いずれも推奨どおり）

1. Lemma 7.7(1) は特別な場合（(1′) p ねじれなし、(1″) envelope と同一視できる）だけ。一般形（W₂ の E∞ 版）は述べない（D36）。
2. D12・BR30：Thm 7.14 の一段は原典に揃えない。Prop 7.11 は A3 の範囲外（D38）。ノート第 7 章の D12 の行に記録、BR30 は閉じる。
3. Ex 7.9 は原典の形（一般の Koszul 正則な f、R の p ねじれ有界）で述べ、証明は普遍の場合への帰着。

## 8. 紙で確かめる項目

1. §2.2 の普遍の場合：A_univ/d と R_univ が p ねじれなし、f̄ が Koszul 正則、Δ_{R_univ} が p ねじれなし（HT filtration の gr = Γ^i(J/J²) が p ねじれなし）。
2. §2.2 の離散性：gr^i = Γ^i(J/J²)[0] が全 i ≥ 0 で非零なのに Δ̄_R が離散であること（Fil_i の遷移が単射で、exhaustive な増大 filtration の
   余極限が離散。完備性は p についてのみ要るか）。
3. G-A3-7：[Bha12, Claim 3.30] の計算の prismatic 版（B の f/d が gr^1 = J/(J²+I) へ全射に写ること）。
4. §2.3 (b)：R を R⟨Y^{1/p^∞}⟩ に替えても L_{S/R} が変わらないこと、S′ → S が余接複体で全射であること、Δ_{S′} → Δ_S の全射性が HT から出ること。
5. G-A3-8：始 prism の完全化が始完全 prism であること（Lemma 3.9 の普遍性）と、既存の `exists_perfectoidization_of_perfectPrism_quotient` の構成
   （δ 除算 → d ねじれ除去 → 完全化 → 完備化）が (Δ_{S′})_perf に一致すること。
6. RootEnvelope の対応表：`PerfectPrismRootSource*`・`PerfectPrismRootPrismCompletelyFlat` などと T の envelope の対応。
