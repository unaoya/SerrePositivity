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
使われ方：E3 の `perfd`・`unit`・`h0`（CAlg 版 `PerfectoidizationInterfaceCAlg` を構成すれば D(R) 版が従う、`nonempty_e3_of_cAlg`）、
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
- Frobenius φ : Δ_S → φ_{A*}Δ_S（A2）。A が完全なので φ_{A*} は D(A)・CAlg_A の自己同値で、φ_A^* := (φ_{A*})^{-1} と書く。
  Δ_perf := (colim(Δ_S → φ_A^*Δ_S → φ_A^{2*}Δ_S → ⋯))^∧（ℕ 添字の sequential 余極限を CAlg_A で取り、(p,d) 完備化）。
  原典の φ_*^n は、A 完全なので φ_A^{n*} と同一視（D42：A 完全の場合に限る。Not 8.1 の設定どおり）。
- Δ_perf は (p,d) 完備な E∞-A 代数で、φ は自己同型（余極限の shift）。
- S_perfd := Δ_perf ⊗^L_A A/d（CAlg_R の対象。D(R) 版は忘却）。p 完備な E∞-S 代数（S → S_perfd は §2.3 の単位）。
- D32・D41：S は離散な R 代数（E3 の始域）で、p 完備でなくてよい。Δ_S は `discreteToAnimated` で直接。E3 の界面の規約 (v)（非完備な始域は導来 p 完備化の
  H⁰ を介して延ばす）は、Δ_S ≃ Δ_{S^∧}（A2-4 の D32）により同じものになる。

### 2.2 Lemma 8.4

- (a) Δ_perf/p := Δ_perf ⊗^L_A A/p は E∞-F_p 代数（A/p は F_p 代数）で、φ が誘導する自己同型をもつ。**P⁰ の議論**：単体的余単体的 F_p 代数
  （Čech–Alexander mod p の多項式分解）の levelwise Frobenius x ↦ x^p は実現の P⁰ 作用を誘導する（G-A4-1 (ii)）ので、Δ_perf/p では P⁰ が可逆。
  P⁰ は正次数（ホモロジー的 n > 0）のホモトピー類を殺す（[Lur11, Rem 2.2.7]、G-A4-1 (i)）。よって π_n(Δ_perf/p) = 0（n > 0）、すなわち
  Δ_perf/p ∈ D^{≥0}、したがって Δ_perf ∈ D^{≥0}（p 完備性と導来 Nakayama）。
- (b) H⁰(Δ_perf) は p ねじれなし（H^{−1}(Δ_perf/p) = H⁰(Δ_perf)[p] = 0）。φ は H⁰ の自己同型で、mod p で Frobenius（P⁰ が π_0 で Frobenius）。
  A3 の (1′)（Rem 2.2）で δ 構造、φ 全単射なので完全 δ 環、p 完備。A → H⁰(Δ_perf) は δ 射（Frobenius と両立）。
- (c) d は H⁰(Δ_perf) で正則：完全 p 完備 δ 環の distinguished 元（d の像は distinguished）は正則（Lemma 2.34、既存の `Prism/Perfectoid` の
  Thm 3.10 の部品に相当）。よって S_perfd = Δ_perf ⊗^L A/d = cofib(d) は coconnective（H^{−1} = H⁰(Δ_perf)[d] = 0）。
- 帰結：(H⁰(Δ_perf), (d)) は完全 prism（A3 の (2) と完全性）。S_perfd が連結なら離散で perfectoid 環（Cor 8.14 の前半、A7）。

### 2.3 E3 の欄（`perfd`・`unit`・`h0`）

- `e3Perfd`：algebraNerve R（離散 R 代数の nerve、Type u）→ CAlg_R R：S ↦ S_perfd。A2-1 の `discreteToAnimated`（基底 k = R = A/d）→ A2-2 の Δ →
  §2.1 の余極限・完備化・⊗ A/d。D(R) 版は忘却 U。
- `e3Unit`：J R ⇒ perfd（単体的ホモトピー、`NatInfinity`）：S → S_perfd は、Fil_0 Δ̄_S = S^∧（A2-3 の `hodgeTateFiltration_zero`、Δ̄_S = Δ_S ⊗ A/d）
  → Δ̄_S → Δ̄_perf = S_perfd（余極限の 0 番目の脚の mod d）の合成。coherent 性は各段が自然変換（Kan 延長の自然変換）であること。
- `e3H0RingData`：H⁰(S_perfd) の環の関手（CAlg 値なので環、A2-2 の `derivedPrismaticCohomology_h0_ring`）、加群構造との同型、射との整合、単位の整合。
  界面の `H0RingData` の各欄に対応（Interface.lean:477〜）。
- CAlg 版の界面（`PerfectoidizationInterfaceCAlg`）を構成する方針なので、D(R) 版の欄は `nonempty_e3_of_cAlg` で従う（EInfinity/Perfectoidization/DerivedCorollary）。

### 2.4 Example 8.3（標数 p）

R = A/d が標数 p（A = W(R)、d = p、結晶 prism）のとき、S_perfd ≅ S_perf := colim_φ S（通常の完全化の p 完備化）。証明：A によらないこと（Prop 8.5、A5）で
A = Z_p にし、HT 比較の Frobenius 同変な S → Δ_S/p が完全化で同型（∧^i L_{S/F_p}[−i] 上の Frobenius は i ≠ 0 で零）。
A6（Prop 8.10：Perfd 上の arc 層性を tilt で標数 p に帰着）で使う可能性があるので主張を置く。証明は A5 の後。

## 3. 必要な一般論（G-A4）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A4-1 | **E∞-F_p 代数の冪作用 P⁰**：(i) Barratt–Eccles 模型での定義（Steenrod 作用、Berger–Fresse／May）と性質：π_0 では Frobenius、π_n（n > 0）では零（[Lur11, Rem 2.2.7]、DAG XIII §2.2）。(ii) 単体的余単体的可換 F_p 代数の levelwise Frobenius が実現の P⁰ を誘導すること | **なし**（EInfinity に冪作用・Frobenius なし）。A4 の最重量。E∞ 側の一般論で、置き場所は EInfinity | Lemma 8.4 (a) |
| G-A4-2 | CAlg_A の sequential（ℕ 添字）余極限と、U がそれを保つこと（filtered 余極限、HA 3.2.3.1）；完備化との合成 | G-A2-4 と同じ入力 | Def 8.2 |
| G-A4-3 | 完全 prism の φ_A による D(A)・CAlg_A の自己同値 φ_{A*}・φ_A^* と、φ-半線形な射の sequential 図式 | G-A2-5 | Def 8.2 |
| G-A4-4 | D(A) → D(R)・CAlg_A → CAlg_R の底変換 ⊗^L_A A/d（∞ 関手）と H⁰ の計算（cofib(d)） | A0 の要確認 (A)、G-A2-3 | S_perfd |
| G-A4-5 | Lemma 2.34：完全 p 完備 δ 環で distinguished 元は正則、R = A/d の p 冪ねじれは R[p] | 既存（`Prism/Perfectoid`、Thm 3.10 の部品。名前要確認） | Lemma 8.4 (c) |
| G-A4-6 | 導来 Nakayama（p 完備で mod p が D^{≥0} なら D^{≥0}） | DerivedGeneral/Truncation の `derived_nakayama` の変種 | Lemma 8.4 (a) |
| G-A4-7 | E3 の `NatInfinity`（単体的ホモトピー）としての coherent な単位の組み立て | E3 の `component`、A2 の Kan 延長の自然変換 | `unit` |

## 4. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D41 | S は導来 p 完備な単体的 R 代数 | S は離散な R 代数（E3 の始域）、p 完備でなくてよい（Δ_S = Δ_{S^∧}、D32）。単体的 S は A2 の P_Σ 上で定義されるが E3 では使わない | E3 の界面の規約 (v) と同じ結論 |
| D42 | φ_*^n Δ（スカラー制限） | A 完全なので φ_A^{n*}（自己同値の逆）で書く | Not 8.1 の設定（完全 prism）では同じ |
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

## 6. 決定待ち

1. **G-A4-1（P⁰）の扱い**：E∞ 側の一般論で、EInfinity レーンは休止中。(a) BS が主張の骨組み（P⁰ の定義の形、Rem 2.2.7、levelwise Frobenius との一致）を
   drafts/Shared に書き、置き場所と担当は調整役（M12・M13 と同じ扱い）。(b) Lemma 8.4 の別証明を探す（HT filtration は Frobenius 安定でないので
   mod d では使えない。mod p の Frobenius 安定な filtration（conjugate filtration）は原典にない）。推奨：**(a)**。
2. E3 の始域：離散 S に Δ を直接定義する（D41）。推奨：**可**。
3. 構成する界面：CAlg 版 `PerfectoidizationInterfaceCAlg` を正とし、D(R) 版は `nonempty_e3_of_cAlg` で得る。推奨：**可**（D35 と整合）。

## 7. 紙で確かめる項目

1. §2.1：φ_{A*} が CAlg_A の自己同値で、φ-半線形な射 Δ → φ_{A*}Δ が sequential 図式 Δ → φ_A^*Δ → ⋯ を与えること（A 完全）。
2. §2.2 (a)：Δ_perf/p で P⁰ が可逆であること（φ の自己同型が P⁰ を誘導する：levelwise Frobenius ＝ P⁰ の主張 (ii) を、Čech–Alexander mod p の
   δ 環の Frobenius x ↦ x^p に適用）。
3. §2.2 (b)：φ が H⁰(Δ_perf) の mod p で Frobenius であること（P⁰ が π_0 で Frobenius）と、A → H⁰ が δ 射であること。
4. §2.3：`unit` の coherent 性（Kan 延長の自然変換の合成として `NatInfinity` が得られる形）。
5. Example 8.3 が A6 で要るか（Prop 8.10・Lemma 8.8 の tilt の議論）。
