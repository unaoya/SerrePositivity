# A5 の設計：perfectoid 化の極限表示（原典 Prop 8.5、Lemma 8.6、Rem 4.6・Lemma 4.8、2026-11-02）

概要：E3 を消す道筋の単位 A5。原典 BS 著者版 §8.1 の後半：完全 prismatic site (S/A)^perf_Δ（Rem 4.6。Lemma 4.8 により perfectoid 環への写像
S → T の圏と同じで、A によらない）の上で、比較写像 Δ_{S/A,perf} → RΓ((S/A)^perf_Δ, O_Δ) が flat と chaotic の間のどの位相でも同値（Prop 8.5）。
特に S_perfd ≃ RΓ((S/A)^perf_Δ, Ō_Δ) ≃ lim_{S→R′} R′（S から perfectoid 環への写像全体の導来極限）で A によらず、S が semiperfectoid なら
Cor 7.3 の perfectoid 化と一致する。証明に要る Lemma 8.6（T = R⟨X_1,…,X_n⟩ → T_∞ = R⟨X_i^{1/p^∞}⟩ について Δ_{T/A} → Δ_{T_∞/A} と
その完全化が descendable、[Mat16]）。これが E3 の欄 `limitCone`・`limit_isLimit` の構成。
方針：定義は原典どおり。完全 prismatic site は A0 の site の完全 prism からなる充満部分圏（A0 の `PerfectPrismaticSite`）に flat 位相、
RΓ は β（S2）。E3 の Type u の添字圏と κ-small の site は、S3（脚注 10 の補題：弱始対象の Čech 余脈体）で同じ Tot に結ぶ。証明は原典の四段
（(1) 弱始対象と位相非依存、(2) filtered 余極限、(3) Lemma 8.6 による降下、(4) semiperfectoid の場合）をそのまま追う。Lemma 8.6 は
Mathew の descendability を定義して（G-A5-1）原典の証明（n = 1 への帰着、(p, φ^{-1}(d)) での底変換、de Rham 比較と Cartier、dg 加群の計算 (∗)）。
規約：S は導来 p 完備な animated R 代数（D45 改訂、決定 6。完全 site は π_0 S で定義し、系 4「π_0 S のみによる」を述べる。E3 の始域の離散 S は特別な場合）。基底は Not 8.1 の完全 prism。値は CAlg_A・CAlg_R（D35）、E3 の欄は
CAlg 版 `BSLimitConeDataCAlg`。Lean の名前は仮。ビルドしない。
使われ方：E3 の `limitCone`・`limit_isLimit`。Cor 8.11（A6）は Prop 8.5 と Prop 8.10 を合わせる。Cor 8.14（A7）、Thm 10.11（A8）。

## 0. 範囲と前提

- 含む：Rem 4.6 の完全 prismatic site、Lemma 4.8（完全 prism からの射は環の射から一意に持ち上がる。系：site は perfectoid 環への写像の圏と同じ）、
  Lemma 7.7(3) の関手的写像 Δ_S → B から作る比較写像、Prop 8.5（主張と系：Ō の RΓ、極限の形、A によらない、semiperfectoid なら Cor 7.3 と一致）、
  Lemma 8.6（両方の主張）、descendability の一般論、E3 の `limitCone`・`limit_isLimit`。
- 含まない：§8.2（A6）、Prop 8.13 の導来版（A7。（旧：系 4 を含まない — D45 改訂で含むことにした、W9-II-08）
  §3.4 では Construction 7.6 (5) の形で使う）。
- 前提：A0（site、`PerfectPrismaticSite`、O_Δ、Cor 3.12 の層性 A0-3d）、S1〜S3（層条件、RΓ、脚注 10）、A2（Δ の Kan 延長、(4)(5)、HT filtration）、
  A3（Lemma 7.7(3) `prismMapOfDiscrete`、Prop 7.10、Cor 7.3 との接続）、A4（Def 8.2、Lemma 8.4、`prismaticPerfectionPrism`）。
  既存：Thm 3.10（`Prism/Perfectoid`）、Lemma 4.8（`Prism/PerfectPrismHomLift`、要確認）、Thm 7.4（`Semiperfectoid/Surjectivity`、要確認）、
  Thm 7.14（`Semiperfectoid/CompatibleRoot*`、要確認）、Cor 7.3 の普遍 perfectoid 環（`Semiperfectoid/Perfectoidization`、要確認）、
  完全 δ 環の完備テンソル（`Delta/Perfect/PerfectDeltaTensor`）。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Rem 4.6 | 定義：(S/A)^perf_Δ ＝ 完全 prism の充満部分圏＋flat 位相 | `PerfectPrismaticSite`（A0）、`perfectFlatTopology` | A0 | A5-1 |
| Lemma 4.8 | 定理（既存を確認）：完全 (A,I) と任意の (B,J) で A/I → B/J は prism の射に一意に持ち上がる。系：(S/A)^perf ≃ Perfd_{S/}（perfectoid 環への写像の圏、濃度 ≤ κ） | `perfectPrismHomLift`、`perfectSiteEquivPerfectoidUnder` | Thm 3.10 の関手版（G-A5-4） | A5-1。**標的の範囲（11-03、BS-D3 の質問への回答）**：原典 Lemma 4.8 は任意の prism (B,J) が標的だが、A0 の site の対象は有界 prism（Def 4.1）で、A5 で使う標的もその範囲なので、`hQ : IsBoundedPrism Q` の特別な場合として述べる（既存 `existsUnique_perfectPrismHomLift_to_bounded`。「定理は特別な場合だけ」の方針、D 番号なし） |
| Lemma 7.7(3) | 既存（A3-1）：関手的 Δ_S → B | `prismMapOfDiscrete` | A3 | — |
| 比較写像 | 定義 | `perfectionComparison : Δ_perf ⟶ lim_{(S/A)^perf} O` | S2、G-A4-3 | A5-1 |
| Prop 8.5 | 定理（S は導来 p 完備な animated、D45 改訂）：⊥ ≤ J ≤ flat の全ての J で比較写像は同値 | `perfectionComparison_isIso`、`perfectionComparison_isIso_topology` | §3 全体 | A5-1〜A5-4 |
| Prop 8.5 系 1 | S_perfd ≃ RΓ(Ō) ≃ lim_{S→R′} R′（κ-small の site でも Type u の Perfd_{S/} でも） | `perfectoidization_isLimit`、`perfectoidization_isLimit_u` | S3、G-A5-9 | A5-1 |
| Prop 8.5 系 2 | A によらない | `perfectoidization_indep` | 系 1 と Lemma 4.8 | A5-1 |
| Prop 8.5 系 3 | semiperfectoid なら Cor 7.3 の perfectoid 化と一致 | `perfectoidization_semiperfectoid` | §3.4 そのもの | A5-2 |
| Prop 8.5 系 4 | Δ_{S,perf}・S_perfd は π_0 S のみによる | 定理（決定 6、2026-11-02）：Perfd_{S/} = Perfd_{π_0 S/}（perfectoid 環は離散）と系 1 から | `perfectoidization_piZero` | A5-1 |
| descendable | 定義（[Mat16, Def 3.18]） | `IsDescendable` | なし（G-A5-1） | A5-3 |
| Lemma 8.6 | 定理 | `prismaticCohomology_rootMap_descendable`、`prismaticPerfection_rootMap_descendable` | G-A5-1、de Rham 入力 G-A5-15 | A5-3 |
| E3 `limitCone` | 構成 | `e3LimitCone S : BSLimitConeDataCAlg R p e3Perfd e3Unit e3H0RingData S` | 系 1（Type u 版）、A4-3 の欄 | A5-1 |
| E3 `limit_isLimit` | 構成 | `e3LimitCone_isLimit` | 同 | A5-1 |

## 2. 定義の形

### 2.1 完全 prismatic site と Lemma 4.8

- `PerfectPrismaticSite P S κ`（A0 既存）：`PrismOverSmall P S κ` の Frobenius 全単射な対象の充満部分圏の opposite。位相 `perfectFlatTopology` は
  A0 の `flatTopology` と同じ形：完全 prism の間の忠実平坦な単射 f の生成 sieve を含む位相の sInf（原典 "the flat topology"）。包含関手による
  引き戻し位相との一致は使わないので述べない。
- site の有限積（**W9-II-06 で訂正**）：以前の「完全 prism の完備テンソル B ⊗̂_A B′」は誤り。A 上のテンソルでは S からの二つの構造射を一致させる条件が
  入らない（反例：A = Z_p、S = F_p[t]、T = F_p[t^{1/p^∞}] は Perfd_{S/} の始対象で自己余積は T 自身だが、W(T) ⊗̂_{Z_p} W(T) の mod p は T ⊗_{F_p} T で
  t の二つの像 u ≠ v。この式を S3 に渡すと Tot が F_p になり極限が変わる）。**正しい余積**：Perfd_{S/} の余積は (T₁ ⊗̂_S T₂)_perfd（T₁ ⊗̂_S T₂ は
  perfectoid T₁ ⊗̂_R T₂ の商の完備化で semiperfectoid、Cor 7.3 の普遍 perfectoid 環 Q(−) について Hom_S(Q(C), U) = Hom_S(C, U) = Hom_S(T₁,U) × Hom_S(T₂,U)。
  未証明の Prop 8.5 は使わない）。これを Lemma 4.8 の圏同値で完全 site に運び、S3 の `CechNerveData` を得る（§3.1 の `perfUnder_cechNerveData` と同じ構成）。
  **flat 被覆の相対 Čech 項**（B₀ → B₁ について B₁ ⊗̂_{B₀} B₁。二つの S 構造射は B₀/d 経由で一致）とは別物で、G-A5-5（O の flat 層性）はこちらについて述べる。
  「完全 site の Čech 余脈体は大きい site と同じ」という一括の理由づけは撤回。
- Lemma 4.8：既存の `PerfectPrismHomLift` を確認する（要確認）。系（`perfectSiteEquivPerfectoidUnder`）：関手 (B,J) ↦ B/J は
  (S/A)^perf_Δ から「S → T、T perfectoid、濃度 ≤ κ」の圏への圏同値。Hom の全単射は Lemma 4.8 を (A,I) := (B,J) に使い、本質的全射は Thm 3.10
  （`exists_perfectoidTrialPrism`）。これで site が A によらない。

### 2.2 比較写像と Prop 8.5

- Lemma 7.7(3)（A3-1）：各 (B,J) ∈ (S/A)_Δ に関手的な A 線形・Frobenius 両立の f : Δ_{S/A} → B（CAlg_A）。**形式化の入口（11-03、BS-D3 の質問への回答）**：A3 の `prismMapOfDiscrete`
  は `IsDiscretePrismatic` を仮定して環準同型を返す離散版で、A5 が要るのは仮定なしの CAlg_A の射。これは Δ_{S/A} = RΓ((S/A)_Δ, O_Δ) の**極限の射影**（S2 の `derivedGlobalSectionsCAlg` の
  site の対象 B での脚、O_Δ(B) = B。A0 の `structurePresheaf` を `ringPresheafToCAlg` で CAlg 値にしたもの、A2 の `prismaticCohomologyCAlg`）で、Frobenius 両立は `structurePresheafFrobenius` の
  自然性から。完全 prism B は有界なので site の対象。A5 の骨組みでは「A0/S2 の CAlg 値 RΓ の射影待ち」の型つき仮置きとして置く（A3 待ちではない）。animated S（D45）では
  π_0 S の site で同じ。塔（A4、原典の φ_{A*}^n）の第 n 項への脚は
  f_n := φ_B^{-n} ∘ f : Res_{φ_A}^n Δ_S → B（B 完全なので φ_B 可逆。f_n(φ_A^n(a) x) = a f_n(x) で A 線形、f_{n+1} ∘ φ = f_n で塔と整合、B について自然。
  W9-II-07 で D42 撤回後の記法に揃えた）。余極限から colim → B、B は (p,d) 完備なので完備化を通り Δ_{S/A,perf} → B。自然性から O の上の錐、
  よって `perfectionComparison : Δ_perf → lim O`。
- RΓ_J(O) = lim O となるのは O が J 層のとき（S2 `derivedGlobalSections_of_isSheaf`）。O は完全 site で flat 層（G-A5-5：A0-3d の制限）なので、
  ⊥ ≤ J ≤ flat の全てで J 層（S1 `IsSheaf.of_le`）。これが原典の「位相の取り方によらない」の形式的な部分。
- Prop 8.5 の主張：`IsIso perfectionComparison`（実体、chaotic）と、各 J についての `Δ_perf ≃ derivedGlobalSections J O`（層性で従う）。
- 系 1：Ō = O ⊗^L_A A/d（A0 `reducedStructurePresheaf`）。⊗^L_A A/d は cofib(d) なので極限と可換（G-A5-9）、完全 prism では B ⊗^L_A A/d = B/J
  （d 正則、Lemma 2.34）。よって S_perfd ≃ lim_{(S/A)^perf} Ō ≃ lim_{Perfd_{S/},κ} T。Type u 版（lim over `PerfUnder_u p S`）は §3.1 の弱始対象で
  両方が同じ Tot に等しいことから。
- 系 2：lim_{Perfd_{S/}} T は A を含まない。二つの完全 prism (A,(d))、(A′,(d′))（A/d ≅ R ≅ A′/d′）で S_perfd ≃ S′_perfd（CAlg_R の同型）。
- 系 3：§3.4。

### 2.3 E3 の欄

- `e3LimitCone S : BSLimitConeDataCAlg R p (e3Perfd p R) (e3Unit p R) (e3H0RingData p R) S`：
  - S^∧ への帰着：`PerfUnder_u p (completionRing p S) ≌ PerfUnder_u p S`（Interface.lean:347、既存）。
  - `cone : JoinCone (targetCAlgDiagram R p S)`：頂点 (S^∧)_perfd、脚は (S^∧)_perfd = Δ_perf ⊗ A/d → B_T ⊗ A/d = T（比較写像の脚の mod d）。
    coherent な錐は「Δ_perf → lim O」の極限の錐（S2）を Lemma 4.8 の同値で Perfd_{S/} に移したもの。
  - `underlying`（D(R) 版 `BSLimitConeData`）の各欄：`sourceCone`（通常の S → T の錐）、`overSource`（単位で因数分解）、`projectionEdge`、
    `projection`（H⁰ の環準同型：CAlg の射の H⁰）、`projection_unit`、`projection_naturality`、`projection_compat`。
  - `comparison`：U は極限の錐を保つ（S4 の CAlg 版 `forget_isLimitCone`、G-A5-16）。
- `e3LimitCone_isLimit S : IsLimitCone (e3LimitCone S).cone`：系 1 の Type u 版を CAlg_R で。U が極限を反映する（`forget_reflects_isLimitCone`）ので
  D(R) で示して移す。

### 2.4 descendability と Lemma 8.6

- 定義（[Mat16, Def 3.18]）：対称モノイダルな安定 ∞ 圏 𝒞（ここでは D_comp(A) や Mod_{Δ_T}(D_comp(A))）の可換代数対象の射 B → B′ が descendable ⇔
  Mod_B(𝒞) の中で B′ の生成する thick ⊗-ideal（有限余極限・retract・shift・任意の対象とのテンソルで閉じた最小の充満部分圏）が単位 B を含む。`IsDescendable`。
  **W9-II-13**：底は離散環 A に限らず E∞ 代数（Δ_T は離散でない）。離散環 A を底とする版はその特殊化。index：fib(B → B′)^{⊗n} → B が零になる最小の n（[BS17, §11.2]）。
- 性質（G-A5-1）：(a) 底変換で安定、(b) 合成で安定、(c) テンソル積（A → B、A → C が descendable ⇒ A → B ⊗ C）、(d) 判定：descendable ⇔ ∃ n,
  fib^{⊗n} → A が零（index）、(e) 降下：A → B descendable ⇒ ∀ M ∈ D(A)、M ≃ Tot(M ⊗_A B^{⊗•+1})（[Mat16, Prop 3.22]）、(f) 十分条件：
  RHom_A(F^{⊗2}, A) ∈ D^{<0} ⇒ index ≤ 2（F = fib）、(g) [BS17, Lemma 11.22]：φ と両立する descendable（index ≤ n）の colim_φ は index ≤ 2n、
  (h) D_comp(A)（完備テンソル）での版。原典は Lemma 8.6 を D_comp(A) の可換代数の射として述べる。
- Lemma 8.6 の主張：T = R⟨X_1,…,X_n⟩、T_∞ = R⟨X_i^{1/p^∞}⟩（p 完備化）。Δ_{T/A} → Δ_{T_∞/A} と Δ_{T/A,perf} → Δ_{T_∞/A,perf} は D_comp(A) の
  可換代数の射として descendable。
- 使う形（§3.3）：S̃ := S ⊗̂_T T_∞ について Δ_{S,perf} ≃ Tot Δ_{S̃^{⊗_S •+1},perf}（(a)、Construction 7.6 (5)、完全化のテンソル可換 G-A5-3、(e)）、
  および各 perfectoid R′ under S について B_{R′} ≃ Tot Δ_{R′ ⊗̂_S S̃^{•+1},perf}。使うのは perf 版だけで、非 perf 版は perf 版の証明の途中（(g)）。

## 3. 証明の筋（Prop 8.5、S は導来 p 完備な animated R 代数。離散 S はその特別な場合）

決定 6（2026-11-02）により S は animated。原典 p.64 のとおり完全 site は (π_0 S/A)^perf、弱始対象 S̃ は π_0 S から、T = R⟨X⟩ → S は π_0 で全射、
semiperfectoid の場合は π_0 S について（HT の連結性は L_{S/Z_p}[−1] の連結性 ⇔ Ω^1_{π_0 S}/p = 0、Thm 7.4 は π_0 S に）。以下の各段の「S」はそのまま
animated S と読み、離散化が要る箇所を π_0 S と書く。骨組みの定義域の書き換え（`variable (S : Type u) [CommRing S]` → `CompleteAnimatedAlgebra`）は
中身の段階で行う（design-status §5）。

### 3.1 弱始対象と位相非依存（原典 (1)）

- S̃ の構成（D51）：S_0 = S、S_{k+1} = (S_k⟨X_s, Y_s : s ∈ S_k⟩/(s − X_s^p − pY_s))^∧、S̃ = (colim_k S_k)^∧。
  (i) 任意の perfectoid T と S → T は S̃ → T に延びる（帰納的に：s ↦ t、y^p ≡ t mod p の y を選び（Frobenius 全射）、X_s ↦ y、Y_s ↦ (t − y^p)/p の
  任意の原像）。(ii) S̃/p は semiperfect（各元は次の段で p 乗根をもつ）。p 完備な R 代数で mod p semiperfect なら semiperfectoid（G-A5-14、
  [BMS19, Rem 4.22]：θ : W(S̃^♭) → S̃ が全射で R ⊗̂ W(S̃^♭) は perfectoid。**perfectoid 基底 R は本質的**で基底なしでは偽（W9-II-16、a6-design §2.1 の ℤ_p の反例）；A6 の Lemma 8.8 は R₀ = ℤ_p[p^{1/p^∞}]^∧ 上へ移す前段 G-A6-11 の後に使う）。(iii) 濃度 ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ。(iv) S ↦ S̃ は関手的。
  **（iv′）完備化した filtered 余極限とは可換でない（W9-II-09 で訂正、以前の主張は偽）**：完備化で初めて現れる元 s（例：R = Z_p[p^{1/p^∞}]^∧、
  S_n = R⟨t_1..t_n⟩、S = (colim S_n)^∧、s = Σ p^j t_j）に付く独立な変数 Y_s は有限段からの比較射の像に入らず、(colim_n S̃(S_n))^∧ → S̃(S) は
  エピ射ですらない。S̃ の用途は弱始対象（と濃度管理）に限る。filtered 余極限の段では §3.2 の整合する被覆 E を使う。
- S̃_perfd（Cor 7.3 の普遍 perfectoid 環。§3.4 で Δ_{S̃,perf}/d と一致）は `PerfUnder_u p S`（Type u）でも κ 側の site でも弱始：S → T を S̃ → T に
  延ばし、普遍性で S̃_perfd → T。
- S3（脚注 10）：弱始対象の Čech 余脈体で lim_{Perfd_{S/}} T = Tot((S̃^{⊗_S •+1})_perfd)。Perfd_{S/} の余積は (T₁ ⊗̂_S T₂)_perfd（T₁ ⊗̂_S T₂ は
  perfectoid の商なので semiperfectoid、Cor 7.3 の普遍性で余積。紙 1）。κ-small の site でも同じ Tot なので二つの極限は一致（D47）。
- 位相：O は flat 層（G-A5-5）なので ⊥ ≤ J ≤ flat で RΓ_J(O) = lim O（§2.2）。

### 3.2 filtered 余極限（原典 (2)）

- 左辺 S ↦ Δ_{S,perf}：A2 の Δ は sifted 余極限を保ち、colim_φ と (p,d) 完備化は（完備化した）filtered 余極限と可換。
- 右辺（**W9-II-09 で書き直し**）：S̃ の連続性は使えないので、図式に整合する被覆を**完備化前に**作る（G-A5-18）：通常の環 C に対し
  E_0(C) = C、E_{k+1}(C) = E_k(C)[X_a, Y_a : a ∈ E_k(C)]/(a − X_a^p − pY_a)、E(C) = colim_k E_k(C)（途中で完備化しない）。E は**通常の環の** filtered
  余極限と可換（添字の元も関係式の有限個の演算も有限段から来る）。filtered 図式 S_i に対し S_alg := colim_i S_i、S = S_alg^∧ とし、S_i の被覆を E(S_i)^∧_p、
  S の被覆を **E(S_alg)^∧_p**（E(S)^∧_p と同一視しない）に選ぶと、後者は前者の完備 filtered 余極限。各段は Y 変数上の X のモニック関係で自由な拡大なので
  p 完備忠実平坦、mod p の根の議論で semiperfectoid（G-A5-14）。原典 p.65 の「任意の flat semiperfectoid 被覆 S → S̃ で同じ Čech–Alexander 計算ができる」
  に沿う。**ただし（W9-II-11）**：E 被覆 U = E(S_alg)^∧_p は単なる flat 被覆以上で、任意の perfectoid T への S → T が U → T に延びる（各段で根と p 除算の原像を選ぶ）
  ので **Q(U) は Perfd_{S/} の弱始対象**。よって Čech 計算は S3 で閉じ（Q(U) の余積の余脈体 Q(U^{⊗̂_S (•+1)})）、S̃ による計算との一致も同じ極限の錐の比較。
  一般の flat semiperfectoid 被覆（例：F_p → F_{p²}）では Q(U) は弱始とは限らず、原典 p.65 の一般形には flat 層性による別の説明が要る。
  G-A5-18 は E 被覆に限定して述べ、一般形は別の補題（E3 では不要）とする。
  semiperfectoid の (−)_perfd（Cor 7.3）は（完備化した）filtered 余極限と可換（普遍性）。Tot は一様に coconnective（ここでは離散）な余単体的対象では
  filtered 余極限と可換（H^k(Tot) = H^k(Tot_{≤k+1})、G-A5-2）。最後に (p,d) 完備化（紙 3）。
- よって S = (colim S_i)^∧（S_i は π_0 が位相的有限生成）に帰着し、以下 S は R⟨X_1,…,X_r⟩ → S（π_0 で全射）をもつとする。

### 3.3 Lemma 8.6 による降下（原典 (3)）

- T = R⟨X_1,…,X_r⟩ → S（全射）、S̃ = S ⊗̂_T T_∞、S̃^n = (S̃^{⊗_S n+1})^∧。各 S̃^n は semiperfectoid（T → S 全射なので S/p の元は R/p 係数の
  x_i の多項式で p 乗根をもつ）。
- 左辺：Δ_{S,perf} → Δ_{S̃,perf} は Δ_{T,perf} → Δ_{T_∞,perf} の底変換（(5) と G-A5-3）で descendable（Lemma 8.6 と (a)）。(e) で
  Δ_{S,perf} ≃ Tot Δ_{S̃^•,perf}。
- 右辺：L_n : Perfd_{S/} → Perfd_{S̃^n/}、R′ ↦ (R′ ⊗̂_S S̃^n)_perfd は忘却関手の左随伴なので始的（G-A5-7）、lim_{Perfd_{S̃^n/}} T =
  lim_{R′ ∈ Perfd_{S/}} (R′ ⊗̂_S S̃^n)_perfd。各 R′ で B_{R′} ≃ Tot_n Δ_{R′ ⊗̂_S S̃^n,perf}（Lemma 8.6 の底変換、§3.4 で各項が perfectoid の
  prism）。極限の交換（G-A5-8）で lim_{Perfd_{S/}} B_{R′} ≃ Tot_n lim_{Perfd_{S̃^n/}} O（紙 4）。
- 両辺の Tot の各項で semiperfectoid の場合（§3.4）が成り立てば比較写像は同値。

### 3.4 semiperfectoid の場合（原典 (4)）

- S semiperfectoid（離散）。R′ := Cor 7.3 の普遍 perfectoid 環（既存）。示すこと：Δ_{S,perf} ⊗^L_A A/d → R′ が同型。
- 連結性：HT filtration（A2-3）の gr^i = (∧^i L_{S/R})^∧[−i]{−i}。semiperfectoid なら L_{S/R} の p 完備化は [−1] shift が連結（G-A5-11）なので
  Δ̄_S が連結、Nakayama で Δ_S が連結、colim_φ と完備化は連結性を保つ（G-A5-10）ので Δ_{S,perf} が連結。Lemma 8.4 と合わせて離散、
  A4 の `prismaticPerfectionPrism` で完全 prism、S_perfd = Δ_{S,perf}/d は perfectoid 環。
- 写像 S → S_perfd → R′（第二は比較写像の脚 Δ_{S,perf} → B_{R′} の mod d）。合成は Thm 7.4 で全射。普遍性で R′ → S_perfd があり、
  R′ → S_perfd → R′ = id（R′ の始性）なので第二の射は分裂全射。S → S_perfd が全射なら R′ → S_perfd も全射で同型。
- S → S_perfd の全射性：
  (α) perfectoid な R_1 → S 全射を取る（R_1 = R⟨Y_k^{1/p^∞}⟩ または R ⊗̂ W(S^♭)、θ の全射性、G-A5-14）。
  (β) 原典の「R を R⟨Y_k^{1/p^∞}⟩ に替えてよい」は、Prop 7.10 の証明（p.60）の同じ一文の理由で正当化する（決定 4、原典どおり）：
  「余接複体を変えないので Δ_{S/R} も変えない」。すなわち **G-A5-17**：perfectoid 環の射 R → R_1 と R_1 代数 S について、自然な比較写像
  Δ_{S/A} → Δ_{S/A_1}（(4) の Δ_{S/A} ⊗̂_A A_1 ≃ Δ_{(S ⊗̂_R R_1)/A_1} と乗法 S ⊗̂_R R_1 → S の関手性の合成）は同型。証明：HT filtration と両立し、
  gr^i では ∧^i L_{S/R} → ∧^i L_{S/R_1} を誘導する。perfectoid の間では L_{R_1/R}^∧ = 0（ker θ の生成元が共通）なので遷移三角形から同型、
  よって Δ̄ で同型、d 進 Nakayama で Δ で同型。これで S を R_1 代数とみなし Δ_{S/A_1,perf} を扱ってよく、R_1 → S 全射。
  Thm 7.14 の段（R_1 → R_1′ 忠実平坦で f_j が p 冪根の系をもつ）も同じ G-A5-17 で R_1′ 上に移れる（原典は底変換 (4) を理由にするが、
  S を R_1′ 代数にするのは S ⊗̂_{R_1} R_1′ であり、こちらは (5) で Δ_{S ⊗̂_{R_1} R_1′} = Δ_S ⊗̂_{B_{R_1}} B_{R_1′}、全射性は忠実平坦性で反映。
  どちらでも書ける。骨組みでは G-A5-17 で統一する）。
  (γ) S′ := (R_1′⟨X_j^{1/p^∞}⟩/(X_j))^∧ → S（または S ⊗̂_{R_1} R_1′）は π_0 と π_1(L_{−/Z_p}/p) で全射なので、HT 比較で H⁰(Δ̄) が全射、
  完全化と Nakayama で S′_perfd → S_perfd 全射。
  (δ) J 有限に帰着（filtered 余極限、§3.2）。
  (ε) Prop 7.10（A3-4）：S′ = (R_1′⟨X_j^{1/p^∞}⟩/(X_j))^∧（J 有限）で S′_perfd = R_1′⟨X^{1/p^∞}⟩/(X^{1/p^∞}) かつ S′ → S′_perfd 全射。
  A3-4 の主張が R_1′ を基底にして述べてあればそのまま、R を基底にして述べてあれば G-A5-17 で移す。
  (ζ) S′ → S′_perfd → S_perfd 全射、S′ → S → S_perfd と等しい ⇒ S → S_perfd 全射。

### 3.5 Lemma 8.6 の証明

- perf 版：非 perf 版と (g)（[BS17, Lemma 11.22]）。
- n = 1 への帰着：Δ_{T_n} = Δ_{T_1}^{⊗̂_A n}（(5)）、descendable のテンソル (c)。
- n = 1：F := fib(Δ_T → Δ_{T_∞}) ∈ D(Δ_T)。(f) で M := RHom_{Δ_T}(F^{⊗2}, Δ_T) ∈ D^{<0} を示せばよい。**底変換との接続（G-A5-6′、W9-II-12。W9 続き 6 で紙 ○、仕様を確定）**：D := Δ_T、N := F ⊗^L_D F、
  M := RHom_D(N, D)、e := φ_A^{-1}(d)、C := A/(p,e)。M は第二引数の完備性から導来 (p,e) 完備。**C が perfect であることも、M ⊗^L_A C と底変換後の RHom の一致も
  仮定できない**ので、次の順で行う。(1) **任意の離散 C 加群 L を係数にした (∗)**：D_C = D ⊗^L_A C を Ω = B ⊕ Bε（B = C[X^p]、|ε| = 1、ε² = 0、微分 0）と書き
  （G-A5-15＋一変数 Cartier）、F_C ≃ B^{(J)}[−1]、Q := B ⊗_C L（B は C 上自由なので導来的にも離散）。B の Ω 上の半自由分解 P（次数 0 の生成元 e_n、d(e_0) = 0、
  d(e_n) = εe_{n−1}）で Hom_Ω(P, Ω ⊗_C L) は次数 0・1 に ∏_n Q、微分は shift (a_0, a_1, …) ↦ (0, a_0, a_1, …) で核 0・余核 Q、よって RHom_Ω(B, Ω ⊗_C L) ≃ Q[−1]、
  B ⊗^L_Ω B ≃ ⊕_n B は次数 0。F_C の二乗と shift を戻して RHom_Ω(N_C, Ω ⊗_C L) ≃ (∏ Q)[1] ∈ D^{≤−1}（積は完全、L の平坦性は不要）。(2) 随伴で任意の C 加群 L に
  RHom_D(N, D ⊗^L_A L) ≃ RHom_{D_C}(N_C, D_C ⊗^L_C L) ∈ D^{≤−1}。(3) 有限 Koszul 複体 K := K_A(p,e) は A 上双対可能、H^j(K) は j ∈ [−2,0] にあり p・e の作用が
  ホモトピーで零なので各 H^j(K) は C 加群。K の有限 Postnikov filtration の段階 H^j(K)[−j]（j ≤ 0）に (2) を当てると各段階は D^{≤−1}、よって
  RHom_D(N, D ⊗^L_A K) ∈ D^{≤−1}。双対可能性で**ここで初めて** RHom とテンソルを交換し、これは M ⊗^L_A K。(4) 完備性の Koszul 判定：K(p^n, e^n) は K(p,e) から有限拡大で
  作られ遷移の最高次コホモロジーは全射なので、M ≃ Rlim_n(M ⊗^L_A K(p^n,e^n)) に lim¹ の次数 0 の項はなく M ∈ D^{≤−1}。(p,e) と (p,d) は同じ根基。原典の
  "By completeness" の一文の形式化はこの (1)〜(4)。Lemma 8.6 の perf 版は有限 index と Frobenius 余極限の一般補題へ渡す。Prop 8.13（A7）は使わない。Δ_T ⊗_A A/φ^{-1}(d) = φ_A^*Δ_T ⊗_A A/d（φ_A は自己同型、A/φ^{-1}(d) ≅ A/d = R）は de Rham 比較（Thm 6.4 の T = R⟨X⟩ の場合、mod p、
  G-A5-15）で Ω^•_{(T/p)/(R/p)}、T_∞ では L_{T_∞/R}^∧ = 0 なので T_∞/p。Cartier（一変数、任意の F_p 代数 R_0 上で初等的：
  Ω^•_{R_0[X]/R_0} ≃ R_0[X^p] ⊕ R_0[X^p]·X^{p−1}dX[−1] は cdga の擬同型、G-A5-12）で (∗) に帰着：Ω := T ⊕ Ω^1[−1]（分裂二乗零拡大、T は
  R_0[X^p] ≅ T^{(1)}）、F = fib(Ω → T → T_∞) ≅ T^{⊕J}[−1]（T_∞ は T 上自由で 1 を基底に含む）、RHom_Ω((T[−1])^{⊗2}, Ω) ∈ D^{<0} を分解
  (⋯ → Ω[−2] → Ω[−1]) ≃ T[−1] で計算（G-A5-13。**任意の離散 C 加群 L を係数にした形** RHom_Ω(N_C, Ω ⊗_C L) ≃ (∏ Q)[1]、Q = B ⊗_C L、で述べる。W9 続き 6）。
- de Rham 入力（G-A5-15）：Thm 6.4 の T = R⟨X_1,…,X_n⟩（ここでは n = 1）での mod p の形。E∞ 代数の同型として、T → T_∞ と両立するもの。A1 では
  HT 比較（Thm 6.3）までしか計画していない。選択肢は §7 の 3。

## 4. 必要な一般論（G-A5）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A5-1（入口 11-03、D3-04：`IsDescendableOver A R B f`・`HasDescentIndexLEOver`、R・B は CAlg_A の頂点、f は `SSet.Edge`。離散版 `IsDescendable` は単位対象の特殊化） | descendability（[Mat16, Def 3.18]）：定義、(a) 底変換、(b) 合成、(c) テンソル、(d) index の判定、(e) 降下 M ≃ Tot(M ⊗ B^{⊗•+1})、(f) RHom(F^{⊗2}, A) ∈ D^{<0} ⇒ index ≤ 2、(g) [BS17, Lemma 11.22]、(h) 完備版 | なし | Lemma 8.6、§3.3 |
| G-A5-2 | 一様に coconnective な余単体的対象の Tot は filtered 余極限と可換（H^k(Tot) = H^k(Tot_{≤k+1})） | なし（Tot = 全複体 G10 の隣） | §3.2 |
| G-A5-3 | 完全化（colim_φ と完備化）と完備テンソルの可換性 | G-A4-2・G-A2-3 の隣 | §3.3・§3.5 |
| G-A5-4 | Thm 3.10 の関手版：完全 prism ↔ perfectoid 環の圏同値（Hom は Lemma 4.8） | `Prism/Perfectoid`、`PerfectPrismHomLift`（要確認） | §2.1 |
| G-A5-5 | O_Δ は完全 site で flat 層（A0-3d Cor 3.12 の制限。完全 prism の余積は完全） | A0-3d（D、2b 後）、`PerfectDeltaTensor` | §2.2 |
| G-A5-6 | 導来完備な M で M ⊗^L A/(p,d) ∈ D^{<0} ⇒ M ∈ D^{<0}（Nakayama の上界版） | DerivedGeneral/Truncation の `derived_nakayama` の変種 | §3.5 |
| G-A5-6′ | RHom と底変換の接続（W9-II-12、W9 続き 6 で ○）：任意の C 加群 L を係数とする (∗)（G-A5-13）→ 随伴で RHom_D(N, D ⊗^L_A L) ∈ D^{≤−1} → 有限 Koszul 複体 K = K_A(p,e) の Postnikov filtration（H^j(K) は C 加群）で RHom_D(N, D ⊗ K) ∈ D^{≤−1} → 双対可能性で = M ⊗ K → K(p^n,e^n) の Rlim（lim¹ なし）で M ∈ D^{≤−1}。C を perfect と仮定しない | なし | §3.5 |
| G-A5-7 | 左随伴は始的：lim_{D} F ≃ lim_{C} F ∘ L（L ⊣ U） | ∞ 側（HTT 4.1.1.8 の系） | §3.3 |
| G-A5-8 | 極限の交換 | ∞ 側 | §3.3 |
| G-A5-9 | ⊗^L_A A/d（cofib d）は極限と可換；完全 prism で B ⊗^L_A A/d = B/J | G-A4-4、Lemma 2.34（G-A4-5） | 系 1 |
| G-A5-10 | 連結性の保存：sequential 余極限・導来完備化は D^{≤0} を保つ；gr が連結な完備 filtration の全体は連結 | DerivedGeneral | §3.4 |
| G-A5-11 | semiperfectoid S：L_{S/R}^∧[−1] は連結（L^∧ は**次数 −1 以下**：Ω^1_{(S/p)/F_p} = 0。「次数 −1 集中」や I/I² の平坦性は qrsp/lci 型の別条件、W9-II-14） | A3 の qrsp（D39）の隣 | §3.4 |
| G-A5-12 | 一変数 de Rham 複体の Cartier・形式性（任意の F_p 代数上、cdga の擬同型） | Shared/DeRhamPolynomial の隣 | §3.5 |
| G-A5-13 | (∗)、**任意の離散 C 加群 L を係数に**：Ω = B ⊕ Bε 上で RHom_Ω(N_C, Ω ⊗_C L) ≃ (∏ B ⊗_C L)[1] ∈ D^{≤−1}（半自由分解 P と shift 微分の核・余核、B ⊗^L_Ω B ≃ ⊕B。L = C だけの形より一段強く、G-A5-6′ に要る） | なし（dg 加群の計算） | §3.5 |
| G-A5-14 | p 完備な R 代数で mod p semiperfect ⇒ semiperfectoid（θ 全射、[BMS19, Rem 4.22]）；perfectoid の商・完備テンソル T₁ ⊗̂_S T₂ の semiperfectoid 性 | 既存の Semiperfectoid（要確認） | §3.1・§3.4 |
| G-A5-15 | de Rham 比較（Thm 6.4）の T = R⟨X⟩・mod p の形、E∞ 代数として、T → T_∞ と両立 | なし（A1 は HT まで） | §3.5 |
| G-A5-16 | U : CAlg_R → D(R) が極限の錐を保ち反映する | Sheaves/CAlgValued の `forget_isLimitCone`・`forget_reflects_isLimitCone` | §2.3 |
| G-A5-18 | **図式に整合する被覆**（W9-II-09・11）：完備化前の代数的な根添加 E(C)（通常の filtered 余極限と可換）、U = E(S_alg)^∧_p の p 完備忠実平坦性と semiperfectoid 性、**Q(U) が Perfd_{S/} の弱始対象**であること（延長性）、S3 による Čech 計算と S̃ の計算の一致。一般の flat semiperfectoid 被覆の形は別補題（E3 不要） | なし | §3.2 |
| G-A5-17 | perfectoid の射 R → R_1 と R_1 代数 S で Δ_{S/A} ≃ Δ_{S/A_1}（比較写像は (4) と乗法、HT の gr で ∧^i L_{S/R} ≃ ∧^i L_{S/R_1}、L_{R_1/R}^∧ = 0、Nakayama）。Prop 7.10 の「R によらない」の導来版 | A2-3・A2-4 の隣（なし） | §3.4 |

## 5. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D45 | S は導来 p 完備な単体的 R 代数、「π_0 S のみによる」 | **改訂（2026-11-02、決定 6）**：S は導来 p 完備な animated R 代数（A7-1 の `CompleteAnimatedAlgebra`、D60 と同じ定義域）。完全 site は π_0 S で定義（原典 p.64）。系 4 を述べる。E3 の始域の離散 S はその特別な場合。（旧：S 離散、系 4 は述べない — W9-I-29 で E3 の非完備 S との接続に系 4 が要ると判明） | 原典の定義域そのもの |
| D46 | 「flat と chaotic の間の任意の位相」 | Grothendieck 位相の順序 ⊥ ≤ J ≤ `perfectFlatTopology` で述べる。位相非依存は O の flat 層性（G-A5-5）と S2 から形式的 | 同じ主張 |
| D47 | 極限の添字は全ての perfectoid 環 | κ-small の site と Type u の `PerfUnder_u` の両方で、同じ弱始対象の Čech 余脈体の Tot（S3） | II-a の整合（補い、差ではない） |
| D48 | semiperfectoid の場合の「R を R⟨Y^{1/p^∞}⟩ に替える」 | 取り下げ（決定 4、原典どおり）。原典 Prop 7.10 の証明と同じ理由（余接複体が変わらない）を G-A5-17 として定理にし、§3.4 (β) で使う | 差なし |
| D49 | descendable は [Mat16] を引用 | [Mat16, Def 3.18] の thick ⊗-ideal で定義し、index の判定は定理 | 引用を定義と定理に（決定項目 2） |
| D50 | Lemma 8.6 は de Rham 比較（Thm 6.4）を使う | Thm 6.4 の多項式・mod p の特別な場合を定理として置く（G-A5-15） | 特別な場合の定理（決定項目 3） |
| D51 | S̃ は超限帰納 | 全元を一度に添加する ω 段の帰納。**用途は弱始対象と濃度管理に限る**（完備 filtered 余極限は保たない、W9-II-09。filtered 余極限の段は G-A5-18 の E） | 同じ対象（原典 "repeating this transfinitely"） |
| D52 | Cor 7.3 との一致は Prop 8.5 の系 | 証明 (4) がそのもの。既存の普遍 perfectoid 環を R′ として使う | 同じ |

## 6. 単位と順序

| 単位 | 内容 | 依存 |
| --- | --- | --- |
| A5-1 | 完全 site の位相、Lemma 4.8 の系、Perfd_{S/} の余積から完全 site の Čech 余脈体、比較写像、Prop 8.5 の主張と系 1〜4（animated 版を含む）、E3 の `limitCone`・`limit_isLimit`（系 1 の Type u 版から） | A0、S1〜S3、A3-1、A4、A5-2（Cor 7.3 の普遍環） |
| A5-2 | semiperfectoid の場合（§3.4）、系 3 | A2-3、A3-4、A4、Thm 7.4・7.14（既存） |
| A5-4 | 弱始対象 S̃・S3 の適用・位相非依存・filtered 余極限・降下の形式部分（§3.1〜3.3） | A5-2、G-A5-2・7・8・14、Lemma 8.6 |
| A5-3 | descendability の一般論（G-A5-1）と Lemma 8.6（§2.4・§3.5）、de Rham 入力（G-A5-15） | A2-4、G-A5-6・12・13 |

骨組みは A5-1 → A5-2 → A5-4 → A5-3。G-A5-1 は Shared（E∞ 側の一般論）、G-A5-12・13 は Shared/DeRham の隣に主張だけ置く。

## 7. 決定事項

決定（2026-11-02、ユーザー）：1・2・3・5 は推奨案、4 は原典どおり。
- 1：Prop 8.5 は原典どおり「flat と chaotic の間の任意の位相」で述べ、O の flat 層性（G-A5-5）は別の定理。
- 2：descendable は [Mat16, Def 3.18]（thick ⊗-ideal）で定義し、index の判定は定理（D49）。
- 3：Lemma 8.6 の de Rham 入力は、Thm 6.4 を T = R⟨X_1,…,X_n⟩・mod p の特別な場合として A1 の装置で証明する新単位 **A1-5**（D50。a1-design §6 に追記）。
- 4：§3.4 (β) は原典の理由（Prop 7.10 の証明の「余接複体を変えないので Δ も変えない」）で正当化する。G-A5-17 を立て、D48 は取り下げ。
- 5：Prop 8.13 の導来版は A5-2 の前に出さず、(5) を直接使う。

相談した選択肢（記録）：

1. Prop 8.5 の述べ方：原典どおり「flat と chaotic の間の任意の位相」で述べ、O の flat 層性（A0-3d の制限、G-A5-5）を別の定理にする（推奨）／
   極限の形（chaotic）だけ述べる。
2. descendable の定義：[Mat16, Def 3.18]（thick ⊗-ideal）で定義し index の判定を定理にする（推奨、D49）／index で定義する（D49 の形を変える）。
3. Lemma 8.6 の de Rham 入力（G-A5-15、D50）：(a) Thm 6.4 を T = R⟨X_1,…,X_n⟩・mod p の特別な場合として、A1 の装置（Construction 6.1、普遍 prism）で
   証明する新単位 A1-5 を立てる（推奨。結晶の範囲は増えない）／(b) A1 の結晶黒箱と同列の第二の黒箱 `deRham_iso_polynomial_modp`／
   (c) (∗) を HT 比較だけで済ませる — 不可（Ω の形式性が要る）。
4. semiperfectoid の場合の底変換（D48）：§3.4 (β) の代案を採る／原典の一文の正当化を先に紙で詰める。
5. Prop 8.13 の導来版（A7）を A5-2 の前に出すか：(5) を直接使えば不要（推奨）。

### 7.1 追加の決定項目（2026-11-02、Codex W9-I-29 から）

6. **Prop 8.5 の定義域と系 4**：D45 で「S は離散、π_0 S の文は述べない」としたが、E3 の非完備な離散 S の欄（D41：perfd S := (completionRing S)_perfd、
   completionRing S = H⁰(LΛ_p S)）と、A8 の Thm 10.11（原典は「整写像の p 完備化」＝animated LΛ_p S について）・A4-3 の `e3Perfd_eq_direct` を結ぶには、
   (LΛ_p S)_perfd ≃ (π_0 LΛ_p S)_perfd が要る。これは原典 Prop 8.5 の系 4「Δ_{S,perf} と S_perfd は π_0 S のみによる」。
   **提案（推奨）**：A7 の D60 で Def 8.2 の定義域を導来 p 完備な animated R 代数に戻したのに合わせ、Prop 8.5 も原典どおり導来 p 完備な animated S で述べる
   （site は π_0 S で定義：(S/A)^perf = (π_0 S/A)^perf、原典 p.64）。証明の四段は animated S でも同じ（(2) filtered 余極限、(3) T → S は π_0 で全射、
   (4) π_0 S semiperfectoid：HT の連結性は L_{S/Z_p}[−1] の連結性 ⇔ Ω^1_{π_0 S}/p = 0 で、Thm 7.4 は π_0 S に）。系 4 はこれから直ちに出る
   （Perfd_{S/} = Perfd_{π_0 S/}）。D45 を「S は導来 p 完備な animated（E3 の始域の離散 S はその特別な場合）」に改める。
   ／代案：Prop 8.5 は離散のまま、Thm 10.11 と E3 の欄を H⁰ 完備化 S^∧ の離散環について直接述べる（S^∧ が整写像の p 完備化であることの確認と、
   filtered 余極限の議論を S^∧ で組み直す必要があり、原典から離れる）。
   **決定（2026-11-02、ユーザー）：推奨案 (a)。** D45 を改訂し、系 4 `perfectoidization_piZero` を A5-1 に置く。E3 の非完備 S の欄との接続
   （`e3Perfd_eq_direct`、A8 の integral）は系 4 で。

## 8. 紙で確かめる項目

1. Perfd_{S/} の余積が (T₁ ⊗̂_S T₂)_perfd（T₁ ⊗̂_S T₂ が semiperfectoid、Cor 7.3 の普遍性）。W9 で ○。完全 site の余積は**これを Lemma 4.8 で移したもの**であり、
   A 上の完備テンソルではない（W9-II-06 の反例）。
2. S̃ の (i)〜(iv)（§3.1）。W9 で (i)(ii)(iii)・関手性は ○、完備 filtered 余極限との可換性は ×（W9-II-09、撤回）。
3. §3.2 の完備化と Tot の順序、Tot_{≤k} と filtered 余極限の交換。W9 で ○（一様な下界で部分 Tot、Koszul 複体で完備化と Tot を交換。O と Ō の係数（完全 prism と
   その mod d）を区別して書く）。
3′. §3.2 の整合する被覆 U = E(S_alg)^∧_p：p 完備忠実平坦・semiperfectoid・filtered 余極限との可換（W9 ○）、Q(U) の弱始性から S3 で Čech 計算、S̃ との一致（W9 ○）。
   一般の flat semiperfectoid 被覆への一般化は未（別補題、W9-II-11）。
4. §3.3 右辺：L_n の左随伴性と始性、極限の交換。W9 で ○（comma 圏に終対象、Prop 8.13 は不要）。
5. §3.4 (β)：G-A5-17（= G-A2-10）の比較写像が HT filtration と両立し gr で余接複体の射を誘導すること、perfectoid の間で L^∧ = 0。(γ)（HT の段）。W9 で ○
   （次数 0 の全射性は gr の décalage と有限段の帰納、網羅性・完備化・Nakayama。animated S でも π_0 S の semiperfectoid 性で足りる）。
6. §3.5：A/(p, φ^{-1}(d)) ≅ R/p（φ_A による係数の取り替え込み）、一変数 Cartier の分裂、(∗) の分解（RHom_Ω(T,Ω) ≃ T[−1]、RHom_Ω((T[−1])^{⊗2},Ω) ≃ (∏T)[1]）は
   W9 で ○。完備性による底変換の正当化（G-A5-6′）は W9 続き 6 の任意係数の (∗) と有限 Koszul 複体の Postnikov filtration の計算で ○（W9-II-12 解消。仕様は §3.5）。
7. Lemma 8.6 の perf 版：W9 で ○。結論は descendable でよく、index の数値（変数の個数 n と元の index の上界 m を区別。一変数で index ≤ 2 なら perf 版は ≤ 4）は公開しない。
