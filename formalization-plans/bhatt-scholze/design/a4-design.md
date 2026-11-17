# A4 の設計：perfectoid 化の定義と coconnectivity（原典 Def 8.2、Example 8.3、Lemma 8.4、2026-11-02）

概要：E3 を消す道筋の単位 A4。原典 BS 著者版 §8.1 の最初の部分：完全 prism (A, I = (d))（R = A/I perfectoid）上の導来 p 完備な単体的 R 代数 S に対し、
Δ_{S/A,perf} := (colim_φ Δ_{S/A})^∧（Frobenius 余極限の (p,d) 完備化）と S_perfd := Δ_{S/A,perf} ⊗^L_A A/I を定義し（Def 8.2）、
両者が D^{≥0} にあること（Lemma 8.4）を示す。これが E3 の欄 `perfd`・`unit`・`h0` の構成であり、Lemma 8.4 は `universal`（Cor 8.14）・
`limitCone`（Prop 8.5）・`integral`（Thm 10.11）の証明で使う（界面の `coconnective` 欄は 10-26 に削除されたが、証明には要る）。
方針：A2 の Δ（CAlg 値）の上で、Frobenius 余極限（ℕ 添字の sequential 余極限）を CAlg_A で取り完備化（DerivedGeneral/CompletionFunctor）。
Lemma 8.4 は原典どおり E∞-F_p 代数の冪作用 P⁰（[Lur11, Rem 2.2.7]）で：Δ_perf/p は P⁰ が可逆な E∞-F_p 代数で、P⁰ は正次数（ホモロジー的）の
ホモトピーを殺すので coconnective。H⁰(Δ_perf) は p ねじれなしで完全 δ 環（A3 の (1′)）、d は正則（Lemma 2.34）、よって S_perfd も coconnective。
規約：基底は完全 prism（向き付き、`Prism/Perfectoid`）。値は CAlg_A を正（D35）、S_perfd は CAlg_R（R = A/d）と D(R)。E3 の始域は離散な
R 代数（`algebraNerve R`）で、Δ は離散 S に直接定義する（D32・D41）。Lean の名前は仮。ビルドしない。
使われ方：E3 の `perfd`・`unit`・`h0`（CAlg 版 `PerfectoidizationInterfaceCAlg` を構成すれば D(R) 版が従う、`nonempty_e3_of_cAlg`。11-13 追記：D71〜D73 の後の drafts は
`EInfinityTheory` 版の `TheoryPerfectoidizationInterface`・`nonempty_e3_of_theory`（EInfinity/Perfectoidization/TheoryInterface:138・194） で組み立てる）、
A5（Prop 8.5）、A6（Prop 8.10〜Cor 8.12）、A7（Prop 8.13、Cor 8.14）、A8（Thm 10.11）。

## 0. 範囲と前提

- 含む：Not 8.1、Def 8.2（Δ_perf、S_perfd、E∞-S 代数としての構造、φ の自己同型）、Lemma 8.4（両者の coconnectivity と、H⁰(Δ_perf) が p 完備な
  完全 δ 環で d が正則）、E3 の `perfd`・`unit`・`h0` の構成、Example 8.3（標数 p では通常の完全化 S_perf。A6 の Prop 8.10 の tilt の議論で要るか
  要確認。主張は入れ、証明は要るときに）。
- 含まない：Prop 8.5 以降（A5〜A7）、Def 8.2 の A によらないこと（Prop 8.5 の系、A5）。
- 前提：A2（Δ、Frobenius、HT filtration、(5)）、A3（(1′)：離散・p ねじれなしなら δ 構造、完全性）、DerivedGeneral（完備化、t 構造）、
  Sheaves/CAlgValued（CAlg 値）、既存の `Prism/Perfectoid`（perfectoid 環 ↔ 完全 prism）、Lemma 2.34（完全 p 完備 δ 環の distinguished 元は正則、
  既存の `Prism/Perfectoid` に相当する補題）。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Not 8.1 | 定義（perfectoid R と完全 prism (A,(d))） | `perfectPrismOf R` | `exists_perfectoidTrialPrism`（Thm 3.10）、A_inf | A4-1 |
| Def 8.2 (1) | 定義そのまま：Δ_perf := (colim_φ Δ_S)^∧ | `prismaticPerfection` | CAlg_A の sequential 余極限（G-A4-2）、完備化（G-A2-3）、φ_{A*} の扱い（G-A4-3） | A4-1 |
| Def 8.2 (2) | 定義そのまま：S_perfd := Δ_perf ⊗^L_A A/d | `perfectoidization` | D(A) → D(R) の底変換（CAlg 版も） | A4-1 |
| Ex 8.3 | 定理（標数 p）。要るときに | `perfectoidization_charP` | A6 で要るか確認 | A4-4 |
| Lemma 8.4 | 定理 | `prismaticPerfection_coconnective`、`perfectoidization_coconnective`、`prismaticPerfection_h0_perfectDelta` | **P⁰（G-A4-1）**、A3 (1′)、Lemma 2.34 | A4-2 |
| E3 `perfd` | 構成 | `e3Perfd : algebraNerve R ⟶ CAlg_R R`（と D(R) 版） | A2-1 の `discreteToAnimated` | A4-3 |
| E3 `unit` | 構成（S → S_perfd の coherent な単位） | `e3Unit : NatInfinity (J R) perfd` | A2-3 の Fil_0 = 単位、余極限の脚 | A4-3 |
| E3 `h0` | 構成（H⁰ の環の関手と整合） | `e3H0RingData` | CAlg 値の H⁰ は環（`derivedPrismaticCohomology_h0_ring`） | A4-3 |

## 2. 定義の形

### 2.1 Frobenius 余極限と完備化（Def 8.2）

- 基底：perfectoid 環 R、完全 prism (A,(d)) で A/d ≅ R（既存）。φ_A は A の自己同型（完全）。
- Frobenius φ : Δ_S → φ_{A*}Δ_S（A2。φ_{A*} = Res_{φ_A} はスカラー制限、a·m = φ_A(a)m）。**塔は原典どおり**
  Δ_S → φ_{A*}Δ_S → φ_{A*}²Δ_S → ⋯、遷移射は φ_{A*}^n(φ)。Δ_perf := (colim の (p,d) 完備化)（ℕ 添字の sequential 余極限を CAlg_A で取り完備化）。
  **訂正（W9-II-01）**：以前の「A 完全なので φ_{A*} の逆 φ_A^* で Δ → φ_A^*Δ → ⋯ と書ける」は誤り。φ_A 半線形な F : M → M は A 線形な M → Res_{φ_A} M
  であって M → Res_{φ_A^{-1}} M ではない（k = F_{p³}、A = W(k)、Δ = A、F = φ_A で F(a·1) = φ_A(a) ≠ φ_A^{-1}(a)·F(1)）。引戻し記法を使うなら
  Res_{φ_A} ≃ (φ_A^{-1})^* で、遷移射も移送する。A の完全性は余極限の shift が φ_A 半線形な**自己同型**になること（と完備化の位相 (p,d) = (p,φ(d))）にだけ使う。
- Δ_perf は (p,d) 完備な E∞-A 代数で、φ は自己同型（余極限の shift）。
- S_perfd := Δ_perf ⊗^L_A A/d（CAlg_R の対象。D(R) 版は忘却）。p 完備な E∞-S 代数（S → S_perfd は §2.3 の単位）。
- 定義域（D41、2026-11-02 決定）：Def 8.2 は原典どおり**導来 p 完備な S**（E3 の始域では p 完備な離散 R 代数）について定義する。p 完備でない離散 S については、
  E3 の界面の規約 (v) どおり `perfd S := perfectoidization (S^∧)`（S^∧ は E3 の `completionRing`、導来 p 完備化の H⁰ = π_0(LΛ_p S)）で**界面の欄として**定義し、
  これが直接の式（P_Σ 上の Δ_S を同じ構成に通したもの）に等しいことを定理にする。**二段**（W9-II-03 で同期）：Δ_S ≃ Δ_{LΛ_p S}（A2-4 の D32、animated 完備化）と
  (LΛ_p S)_perfd ≃ (π_0 LΛ_p S)_perfd（Prop 8.5 系 4 `perfectoidization_piZero`、A5-1。LΛ_p S は離散とは限らない）。Def 8.2 の定義域は原典と同じ。

### 2.2 Lemma 8.4

- (a) Δ_perf/p := Δ_perf ⊗^L_A A/p は E∞-F_p 代数（A/p は F_p 代数）で、φ が誘導する自己同型をもつ。**P⁰ の議論（W9-II-02 で訂正）**：P⁰ を
  忘却関手 U : CAlg_{F_p} → Sp 上の **coherent な自然自己変換**として用意し（Lurie DAG XIII Constr 2.2.6）、離散環 B では P⁰_{HB} = H(Frob_B)。U は極限と
  幾何学的実現を保つので、自然変換の錐との両立により、この同定は余単体的 Tot と単体的実現へ移る（G-A4-1 (ii) の正しい形）。A2 の模型の φ が levelwise
  Frobenius を誘導すること（G-A3-9 の比較）と合わせ、Δ_perf/p では塔の shift が P⁰ **と同じ作用**を誘導し、P⁰ は可逆。P⁰ は正次数（ホモロジー的 n > 0）の
  ホモトピー類を殺す（[Lur11, Rem 2.2.7]、G-A4-1 (i)）。よって π_n(Δ_perf/p) = 0（n > 0）、すなわち Δ_perf/p ∈ D^{≥0}、したがって Δ_perf ∈ D^{≥0}
  （p 完備性と導来 Nakayama）。「φ と P⁰ が可換」だけでは足りない。通常の p 重 cup 積で P⁰ を説明することはできない（次数が違う：S¹ の mod 2 で x ∪ x = 0 だが
  Frobenius は恒等）。
- (b)（W9-II-04 で訂正）X := Δ_perf、C := H⁰(X)。X --p→ X → X/p の長完全列から C[p] = H^{−1}(X/p) = 0 と **0 → C/p → H⁰(X/p)（単射。同型ではない）**。
  φ の自然性と P⁰ が H⁰(X/p) で p 乗であることから、単射を通じて φ(c) ≡ c^p mod p。p ねじれなしなので δ(c) := (φ(c) − c^p)/p が一意に定まり δ 環
  （**一般の p ねじれなし環の Rem 2.2、G-A3-6 を共用**。A3 の `deltaStructure_of_discrete_pTorsionFree` は `IsDiscretePrismatic` を仮定するので直接は使えない）、
  A → C は δ 射（p δ(f(a)) = f(φ_A(a) − a^p) を p 消去）、φ 可逆なので完全 δ 環、C の p 完備性は X の導来 p 完備性からコホモロジーの導来完備性を取り出し p ねじれなしを使う。
  X 自体の離散性は使わない。
- (c) d は H⁰(Δ_perf) で正則：完全 p 完備 δ 環の distinguished 元（d の像は distinguished）は正則（Lemma 2.34、既存の `Prism/Perfectoid` の
  Thm 3.10 の部品に相当）。よって S_perfd = Δ_perf ⊗^L A/d = cofib(d) は coconnective（H^{−1} = H⁰(Δ_perf)[d] = 0）。
- 帰結：(H⁰(Δ_perf), (d)) は完全 prism：H⁰ の導来 (p,d) 完備性、上の δ 構造、基底から来る p ∈ (d, φ(d))、Lemma 2.34 の d 正則性から**直接**組み立てる
  （A3 の (2) は「Δ と Δ̄ が離散」を仮定するので直接は使わない、W9-II-04）。S_perfd が連結なら離散で perfectoid 環（Cor 8.14 の前半、A7）。

### 2.3 E3 の欄（`perfd`・`unit`・`h0`）

- `e3Perfd`：algebraNerve R（離散 R 代数の nerve、Type u）→ CAlg_R R：S ↦ S_perfd。A2-1 の `discreteToAnimated`（基底 k = R = A/d）→ A2-2 の Δ →
  §2.1 の余極限・完備化・⊗ A/d。D(R) 版は忘却 U。
- `e3Unit`：J R ⇒ perfd（単体的ホモトピー、`NatInfinity`）：S → S_perfd は、Fil_0 Δ̄_S = S^∧（A2-3 の `hodgeTateFiltration_zero`、Δ̄_S = Δ_S ⊗ A/d）
  → Δ̄_S → Δ̄_perf = S_perfd（余極限の 0 番目の脚の mod d）の合成。coherent 性は各段が自然変換（Kan 延長の自然変換）であること。
- `e3H0RingData`：H⁰(S_perfd) の環の関手（CAlg 値なので環、A2-2 の `derivedPrismaticCohomology_h0_ring`）、加群構造との同型、射との整合、単位の整合。
  界面の `H0RingData` の各欄に対応（Interface.lean:477〜）。
- CAlg 版の界面（`PerfectoidizationInterfaceCAlg`）を構成する方針なので、D(R) 版の欄は `nonempty_e3_of_cAlg` で従う（EInfinity/Perfectoidization/DerivedCorollary）。
  （11-13 追記：今の drafts/A9/Assembly は `TheoryPerfectoidizationInterface`・`nonempty_e3_of_theory`（EInfinity/Perfectoidization/TheoryInterface:138・194） を使う。）

### 2.4 Example 8.3（標数 p）

R = A/d が標数 p（A = W(R)、d = p、結晶 prism）のとき、S_perfd ≅ S_perf := colim_φ S（通常の完全化の p 完備化）。証明：A によらないこと（Prop 8.5、A5）で
A = Z_p にし、HT 比較の Frobenius 同変な S → Δ_S/p が完全化で同型（∧^i L_{S/F_p}[−i] 上の Frobenius は i ≠ 0 で零）。
A6（Prop 8.10：Perfd 上の arc 層性を tilt で標数 p に帰着）で使う可能性があるので主張を置く。証明は A5 の後。

## 3. 必要な一般論（G-A4）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A4-1 | **E∞-F_p 代数の冪作用 P⁰**：(i) 定義（Lurie DAG XIII Constr 2.2.6 の強さ：忘却 U : CAlg_{F_p} → Sp 上の coherent な自然自己変換。Barratt–Eccles で実装するならこの強さとの対応を仕様に含める）と性質：π_0 では Frobenius、π_n（n > 0）では零（Rem 2.2.7）。(ii) 離散環 B で P⁰_{HB} = H(Frob_B)、U が極限・実現を保つことから余単体的 Tot・単体的実現への移送（**通常の p 重 cup 積による説明は誤り**、W9-II-02） | **なし**（EInfinity に冪作用・Frobenius なし）。A4 の最重量。置き場所は EInfinity/PowerOperation/（M14） | Lemma 8.4 (a) |
| G-A4-2 | CAlg_A の sequential（ℕ 添字）余極限と、U がそれを保つこと（filtered 余極限、HA 3.2.3.1）；完備化との合成 | G-A2-4 と同じ入力 | Def 8.2 |
| G-A4-3 | スカラー制限 φ_{A*} = Res_{φ_A}（D(A)・CAlg_A）とその正の反復、φ-半線形な射 φ : Δ → φ_{A*}Δ から塔 Δ → φ_{A*}Δ → φ_{A*}²Δ → ⋯（遷移射 φ_{A*}^n(φ)）、A 完全のとき shift が φ_A 半線形な自己同型（W9-II-01 で訂正） | G-A2-5 | Def 8.2 |
| G-A4-8 | 一般の p ねじれなし環と Frobenius 持ち上げの Rem 2.2（δ 構造の一意性、δ 射の判定）：A3 の G-A3-6 と共用（W9-II-04） | `Delta/Basic`（要確認） | Lemma 8.4 (b) |
| G-A4-4 | D(A) → D(R)・CAlg_A → CAlg_R の底変換 ⊗^L_A A/d（∞ 関手）と H⁰ の計算（cofib(d)） | A0 の要確認 (A)、G-A2-3 | S_perfd |
| G-A4-5 | Lemma 2.34：完全 p 完備 δ 環で distinguished 元は正則、R = A/d の p 冪ねじれは R[p] | 既存（`Prism/Perfectoid`、Thm 3.10 の部品。名前要確認） | Lemma 8.4 (c) |
| G-A4-6 | 導来 Nakayama（p 完備で mod p が D^{≥0} なら D^{≥0}） | DerivedGeneral/Truncation の `derived_nakayama` の変種 | Lemma 8.4 (a) |
| G-A4-7 | E3 の `NatInfinity`（単体的ホモトピー）としての coherent な単位の組み立て | E3 の `component`、A2 の Kan 延長の自然変換 | `unit` |

## 4. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D41 | S は導来 p 完備な単体的 R 代数 | Def 8.2 は原典どおり導来 p 完備な S に定義する。E3 の `perfd` の欄（任意の離散 S）は界面の規約 (v) どおり (S^∧)_perfd で定義し、直接の式との一致は定理（D32 の animated 版＋Prop 8.5 系 4、W9-II-03） | 定義域は原典と同じ。拡張は界面の欄の定義として別に置く |
| D42 | φ_*^n Δ（スカラー制限） | **撤回・訂正（W9-II-01）**：原典どおり φ_{A*}^n（スカラー制限の正の反復）で書く。「φ_A^{n*} と同じ」は偽（Res_φ ≃ (φ^{-1})^*）。A 完全は shift の自己同型性にだけ使う | 差なし |
| D43 | Lemma 8.4 は Lur11 の P⁰ を引用 | P⁰ を Barratt–Eccles 模型で定義し Rem 2.2.7 を証明する（G-A4-1） | 引用を定理に。E∞ 側の新しい一般論 |
| D44 | `coconnective` 欄（Lemma 8.4）は E3 の欄だった | 欄は削除済み（10-26）。Lemma 8.4 は Cor 8.14・Prop 8.5・Thm 10.11 の証明の中で使う定理として A4 に置く | 界面の型は変えない |

## 5. 単位と順序

| 単位 | 内容 | 前提 |
| --- | --- | --- |
| A4-1 | Not 8.1、Def 8.2（Δ_perf、S_perfd、φ の自己同型） | A2-2、G-A2-3、G-A4-2・3・4 |
| A4-2 | Lemma 8.4（(a) coconnectivity、(b) H⁰ 完全 δ 環、(c) d 正則と S_perfd の coconnectivity）、完全 prism (H⁰(Δ_perf), (d)) | G-A4-1・5・6、A3 (1′) |
| A4-3 | E3 の `perfd`・`unit`・`h0`（CAlg 版） | A4-1、A2-3、G-A4-7 |
| A4-4 | Example 8.3（主張。証明は A5 の後） | A5 |

骨組みは A4-1 → A4-3 → A4-2 → A4-4。G-A4-1 は E∞ 側の一般論として別ファイル（`drafts/Shared/EInfinityPowerOperation.lean`）に主張だけ置く。

## 6. 決定（2026-11-02、ユーザー）

1. **G-A4-1（P⁰）**：BS が主張の骨組み（P⁰ の定義の形、Rem 2.2.7、levelwise Frobenius との一致）を `drafts/Shared/EInfinityPowerOperation.lean` に書き、
   置き場所と担当は調整役（M12・M13 と同じ扱い）。
2. **E3 の始域（D41）**：Def 8.2 は原典どおり導来 p 完備な S に定義。非完備な離散 S への延長は界面の欄 `perfd` の定義として (S^∧)_perfd で置き、
   直接の式との一致を定理にする（§2.1）。
3. **構成する界面**：CAlg 版 `PerfectoidizationInterfaceCAlg` を正とし、D(R) 版は `nonempty_e3_of_cAlg` で得る。
   （11-13 追記：D71〜D73 の後は `EInfinityTheory` 版の `TheoryPerfectoidizationInterface`・`nonempty_e3_of_theory`（EInfinity/Perfectoidization/TheoryInterface:138・194）。）

### 6.1 Codex W9 第 2 部の訂正（2026-11-02）

- W9-II-01（致命）：D42 を撤回し、塔を原典の φ_{A*}^n に戻した（§2.1、G-A4-3、骨組み `frobeniusTower`）。
- W9-II-02：G-A4-1 (ii) の cup 積による説明を撤回し、coherent な P⁰ の自然変換（Lurie の強さ）と Tot・実現への移送に差し替えた（§2.2 (a)、G-A4-1、骨組み）。
- W9-II-03：D41 の説明を D32（animated）＋Prop 8.5 系 4 の二段に同期。
- W9-II-04：Lemma 8.4 (b) と prism 性は H⁰ の単射・一般の Rem 2.2（G-A4-8 = G-A3-6）・完備性・Lemma 2.34 から直接（A3 の離散 Δ 用の定理は使わない）。
- W9-II-05：InterfaceFields の単位名（integral は A8、excision は A6）とノート第 8 章の coconnective 欄の記述を同期。

## 7. 紙で確かめる項目

1. §2.1：塔は φ_{A*}^n（W9 ×→訂正）。φ-半線形な射は M → Res_φ M であって M → Res_{φ^{-1}} M ではない。
2. §2.2 (a)：Δ_perf/p で P⁰ が可逆であること（W9：cup 積の説明は ×。coherent な P⁰ の自然変換と離散環での同定を Tot・実現へ移し、G-A3-9 の比較で模型の φ と結ぶ）。
3. §2.2 (b)：C/p ↪ H⁰(X/p) の単射から φ(c) ≡ c^p、一般の Rem 2.2（G-A3-6）で δ、A → C が δ 射、prism 性を H⁰ の完備性・d 正則性から直接（W9 ○）。
4. §2.3：`unit` の coherent 性（Kan 延長の自然変換の合成として `NatInfinity` が得られる形）。
5. Example 8.3 が A6 で要るか（Prop 8.10・Lemma 8.8 の tilt の議論）。
