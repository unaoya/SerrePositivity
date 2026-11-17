# A6 の設計：arc 降下と excision（原典 Def 8.7、Lemma 8.8、Prop 8.10、Cor 8.11、Cor 8.12、2026-11-02）

概要：E3 を消す道筋の単位 A6。原典 BS 著者版 §8.2：p 進形式スキームの arc 位相（Def 8.7、[BM18]）、perfectoid が基底をなすこと（Lemma 8.8）、
構造層 O が Perfd 上の arc 層で affine perfectoid の高次コホモロジーが消えること（Prop 8.10）、S_perfd = RΓ_arc(Spf S, O)（Cor 8.11）、
excision（Cor 8.12）：S → S′ が導来 p 完備な環の射、I ⊂ S が導来 p 完備なイデアルで、S → S′ が I の外で arc 層の同型（I を殺さない
p 完備な階数 1 の付値環 V への写像 S → V が S′ → V に一意に延びる）なら、S_perfd・S′_perfd・(S/I)_perfd・(S′/I)_perfd の四角形は
E∞-S 代数の引き戻し。これが E3 の欄 `excision`。
方針：E3 で使うのは Cor 8.12 だけで、その原典の証明は site Perfd（affine で足りる）の上の層の議論：F_T := Hom(−, Spf T) が Perfd 上の
層で、Γ(F_T, O) = lim_{Perfd_{T/}} O = T_perfd（Prop 8.5）、そして F_S = F_{S′} ⊔_{F_{S′/I}} F_{S/I} が空間の層として成り立つこと
（F_{S′/I} ↪ F_{S′} なので押し出しは離散で、集合の層で計算してよい）。これを原典どおり追う：arc site は affine perfectoid（κ-small）の上に
定義し（D53）、Prop 8.10 の affine 部分（O の arc 層性）は原典の tilt による帰着と完全スキームの v 降下（[BS17, Thm 4.1]）・arc 降下の
判定（[BM18, Thm 1.6]、[BS17, Lemma 6.3]）に帰着する。後者三つは結晶側と同じ扱いの黒箱候補（決定項目 2）。Cor 8.12 の層の議論は
∞ 側の一般論 S8（site 上の空間値前層、その層化、0 切り捨て＝集合の層、E 値の層が局所同値で局所的）を要する（決定項目 3）。
規約：S・S′ は離散（E3 の始域、D45 と同じ）。R は Not 8.1 の perfectoid 環、A は完全 prism。値は CAlg_R（界面は CAlg 版）。
Lean の名前は仮。ビルドしない。
使われ方：E3 の `excision`。Cor 8.11 の「S ↦ S_perfd の arc 降下」は E3 では使わない。

## 0. 範囲と前提

- 含む：Def 8.7 の affine 版（κ-small の perfectoid 環の圏の arc 位相、[BM18, Def 1.2] の有限族の形）、arc 被覆の底変換・合成での安定性、
  Prop 8.10（O が arc 層；affine T について Hom(T, −) が集合の arc 層）、Cor 8.12、E3 の `excision`、Lemma 8.8 の affine 版（cover-dense。前段 G-A6-11 で R₀ 上へ移してから A5-4 の S̃、W9-II-16）。
- 含まない：p 進形式スキーム fSch とその上の arc 位相（D53）、Cor 8.11 の RΓ_arc(Spf S, O)（fSch 上の層コホモロジー。E3 で使う等式
  S_perfd = Γ(F_S, O) は Prop 8.5 の極限の形そのもの、D55）、Prop 8.10 の後半の非 affine T、Rem 8.9。
- 前提：A5（Prop 8.5 の極限の形、Type u 版、Perfd_{S/} の余積、弱始対象）、S1〜S4（E 値の層）、**S8**（空間値の層、§4）、
  既存：perfectoid の tilt（`Prism/Perfectoid/WittQuotientTilt`）、完備テンソル（`Perfectoidization/CompletedTensor`）、
  E3 の界面の `ArcOutside`・`ordinarySquare`・`quotientProjection`・`IsPullbackSquare`（Interface.lean:570〜650）、
  環の帰結（`Perfectoidization/Derived/Excision`：`excision_of_disc` など、界面から証明済み）。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Def 8.7 | 定義（affine 版、D53・D54）：perfectoid 環 R → R_i の有限族が arc 被覆 ⇔ p 完備な階数 1 の付値環 V への R → V は、忠実平坦な拡大 V ⊂ W と或る R_i → W に持ち上がる；位相は生成される Grothendieck 位相 | `IsArcCoverFamily`、`arcTopology` | `ArcOutside`（界面、同じ V の条件） | A6-1 |
| arc 被覆の安定性 | 定理：底変換・合成・有限族の合併で安定（coverage） | `isArcCover_baseChange`、`_comp` | なし | A6-1 |
| Lemma 8.8 | 定理（affine 版、cover-dense として証明の中で使う）：任意の p 完備 S は perfectoid による arc 被覆をもつ（S → S₀ → S̃₀ → (S̃₀)_perfd。S₀ := completionRing(S ⊗_{ℤ_p} R₀)、R₀ := ℤ_p[p^{1/p^∞}]^∧ の上で A5-4 の根添加。W9-II-16） | `exists_perfectoid_arcCover` | G-A6-11（前段）、A5-4 の `rootClosure`（R₀ 上）、A5-2、G-A6-3 | A6-1 |
| Rem 8.9 | 不要 | — | — | — |
| Prop 8.10 前半 | 定理：O は affPerfd_κ 上の arc 層（Čech 層、D-S1） | `structurePresheaf_isArcSheaf` | tilt への帰着（§3.1）、**黒箱 G-A6-1** | A6-2 |
| Prop 8.10 後半 | 定理（affine T）：Hom(T, −) は集合の arc 層 | `homPresheaf_isArcSheaf` | 前半から（環の等化子） | A6-2 |
| Cor 8.11 | 不要（D55）。E3 で使う等式 T_perfd = Γ(F_T, O) := lim_{Perfd_{T/}} O は Prop 8.5 | `perfectoidization_eq_sectionsOf` | A5 | A6-4 |
| Cor 8.12 | 定理（S・S′ 離散） | `perfectoidization_excision` | §3.2、S8 | A6-3・A6-4 |
| 脚注 14 | 既存（整写像で V(I) の外で同型なら条件を満たす） | 既存（要確認：名前） | — | — |
| E3 `excision` | 構成 | `e3Excision` | Cor 8.12、`e3Perfd_of_complete`（A4-3） | A6-4 |

## 2. 定義の形

### 2.1 arc site（Def 8.7 の affine 版）

- 台：`PerfdSmall p κ` := 濃度 ≤ κ の perfectoid 環（Type u）の圏（`IsIntegralPerfectoid`、`SmallModel`）。site はその opposite。
  κ は Cor 8.12 で使う S・S′・S/I・S′/I と A5-4 の S̃ の濃度を超えるように取る（κ 不変性は A5 の D47 と同じ：極限は弱始対象の Tot）。
- `IsArcCoverFamily (R) (ι : Finite) (R_i : ι → PerfdSmall)`：∀ V（p 完備な階数 1 の付値環、Type u、`ValuationRing`・`ringKrullDim V = 1`・
  `IsAdicComplete (span {p}) V`、界面の `ArcOutside` と同じ条件の書き方）、∀ R → V、∃ i, ∃ W（同じ種類の付値環）、V → W 忠実平坦、∃ R_i → W で
  R → R_i → W = R → V → W。原典 Def 8.7 の "faithfully flat extension V ⊂ W of p-adically complete valuation rings of rank 1"。
- `arcTopology`：有限 arc 被覆族の生成 sieve を含む Grothendieck 位相の sInf（A0 の `flatTopology` と同じ形、D22）。coverage であること
  （底変換で安定：R → R′ と arc 被覆 {R → R_i} に対し {R′ → R_i ⊗̂_R R′}（完備テンソルは perfectoid、`CompletedTensor`）が arc 被覆；
  V への R′ → V は R → V を与え、持ち上げ R_i → W と R′ → V → W で R_i ⊗̂_R R′ → W）で、S1 の「生成系で十分」の補題が使える。
- Lemma 8.8（cover-dense、**W9-II-16 で修復**）：A5-4 の `rootClosure` の semiperfectoid 性（G-A5-14）は perfectoid 基底 R を仮定するので、全 p 完備環の
  affCompl_κ の対象にそのまま当てることはできない。反例：S = ℤ_p から基底なしで同じ根添加 C_{k+1} = (C_k⟨X_a, Y_a⟩/(a − X_a^p − pY_a))^∧ を始めると、
  各段で x^p ≡ z mod p の x ∈ ℤ_p を選んで C_{k+1} → ℤ_p が延び、ℤ_p → C_∞ → ℤ_p は恒等。perfectoid 環 P から ℤ_p への環準同型は存在しない
  （p = uϖ^p から 1 = v_p(p) = p·v_p(ϖ) で矛盾、零環からも不可）ので C_∞ は perfectoid の商でなく semiperfectoid でない（C_∞/p の Frobenius 全射は正しい。
  誤りは基底なしに semiperfectoid 性へ進む所）。そこで**前段**を置く（G-A6-11）：R₀ := ℤ_p[p^{1/p^∞}]^∧（perfectoid）、
  S₀ := completionRing(S ⊗_{ℤ_p} R₀)（p 完備な R₀ 代数、#S₀ ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ）とし、S₀ に R₀ 上の A5-4 の根添加を施して S̃₀、その普遍 perfectoid 環
  (S̃₀)_perfd（A5-2）を取る。S → S₀ → S̃₀ → (S̃₀)_perfd が arc 被覆であること：S → V（試験付値環）に対し**先に** V を perfectoid な W（絶対整閉包の p 完備化、
  G-A6-3）に忠実平坦に埋め、W の中で p の両立する p 冪根を選んで R₀ → W、S → V → W と合わせて S ⊗_{ℤ_p} R₀ → W、W は p 完備なので S₀ → W；
  `rootClosure_extends`（標的は perfectoid）で S̃₀ → W；S̃₀ は R₀ 上 semiperfectoid（`rootClosure_isSemiperfectoid`）なので普遍性で (S̃₀)_perfd → W。
  旧記述「S̃ → V に延びてから W に替える」は `rootClosure_extends` の標的が perfectoid であることと順序が合わないので改めた。
  記録：S → S₀ は p 完備忠実平坦（ℤ_p → R₀ が p 完備忠実平坦）で、原典 Lemma 8.8 の証明の「semiperfectoid な p 完備忠実平坦被覆」は S → S̃₀ がそれにあたる
  （S₀ → S̃₀ も p 完備忠実平坦、A5-4）。E3 には arc 被覆性だけ要る。未証明の E3 や A7 の普遍性は使わない。

### 2.2 Prop 8.10（affine）

- **Čech 条件の形（BS-D1 の D1-01、11-03）**：S3 の `CechNerveData` は全 site の絶対積ではなく、単射被覆 f : R → S の生成 sieve Q の圏 sieveCategory Q の中で取る
  （U = f.op が弱終、U の冪は op R 上のファイバー積＝相対完備テンソル冪。全 site の絶対積は S ⊗̂_{ℤ_p} S で別物）。二つの主張を分ける：(1) 個々の生成 sieve の層条件 ⇔ 相対 Čech の Tot
  （`isSheaf_generateSieve_iff_cech`）、(2) arc 層 ⇔ 全ての単射 arc 被覆で (1)（coverage `arcCoverage` と S1 の生成系の補題、有限族は ∏ へ。`isSheaf_arc_iff_cech`）。
  A5 の完全 site は Perfd_{S/} で最初から相対なのでこの区別は要らない。
- `structurePresheaf_isArcSheaf`：O : R ↦ R（**CAlg_ℤ 値**、A0 の `ringPresheafToCAlg` の底を ℤ に。**W9-II-22**：global な affPerfd_κ の対象には固定 R からの射がないので
  CAlg_R 値とは書けない。F_U の元の圏 Perfd_{U/}（R → U）の上では R → U → T で CAlg_R 値に持ち上がり、極限・引き戻しは忘却 CAlg_R → CAlg_ℤ が作る（保ち反映する）ので
  E3 の型（CAlg_R の四角形）に戻せる。global な site は変えない）は arc 位相の Čech 層。S1 の生成系の補題で、
  有限 arc 被覆族 {R → R_i} について O(R) ≃ Tot(O(Čech 余脈体)) を示せばよく、Čech 余脈体は完備テンソル冪（S3 の `CechNerveData`、
  Perfd の余積 = 完備テンソル、既存）。R → ∏ R_i =: S に置き換え（∏ R_i は perfectoid：G-A6-12 の直接証明。E3 を使う既存の `isIntegralPerfectoid_finPi` は不可、W9-III-08。11-13 追記：BS-W10 作業 A（main cc67ea88e）で `isIntegralPerfectoid_finPi` は `BhattScholze/Perfectoid/FiniteProduct` の E3 非依存の直接証明になり、使える）、単射 arc 被覆 R → S に帰着。**D1-02（BS-D1、11-03）**：この置き換えで位相は変わる（k × k → k の二つの射影の族は有限 arc 被覆だが、その生成 sieve は一点 arc 被覆を含まない）ので、
  「単射の生成 sieve と同じ位相」は誤り。正しくは arcTopology = K₁（一点被覆）⊔ K_ext（有限積の射影）で、任意の前層の層条件は「有限積を保つ ∧ 一点被覆の Čech 条件」
  （`isSheaf_arc_iff_cech`、extensive 側は S1 の一般補題 S1-E）。O（CAlg_ℤ 値、環の積は CAlg の積）と Hom(T, −) は有限積を保つので、Prop 8.10 と F_T の層性は一点被覆の Čech 条件だけでよい。
  反例（任意の前層では一点被覆だけで足りない）：二点集合に値を取る定数前層は全ての一点 Čech 条件を満たすが、零環の空族の条件 F(0) ≃ * を満たさない。
- 離散な余単体的環の Tot は Čech 複体 0 → R → S → S ⊗̂_R S → ⋯（非正規化 Tot、A0 の決定）なので、主張は「arc 被覆 R → S の完備 Čech 複体の完全性」。
- `homPresheaf_isArcSheaf (T)`：R ↦ Hom(T, R) は集合の arc 層：H⁰ の等化子 R = eq(S ⇉ S ⊗̂_R S) に Hom(T, −) を当てる。原典 "immediate"。

### 2.3 Cor 8.12 と E3 の欄

- 主張：S → S′ 離散で導来 p 完備、I ⊂ S 導来 p 完備（S 加群として）、`ArcOutside f I` ⇒ CAlg_R の四角形
  S_perfd → S′_perfd、S_perfd → (S/I)_perfd、S′_perfd → (S′/IS′)_perfd、(S/I)_perfd → (S′/IS′)_perfd は引き戻し。
  原典の "(S′/I)_perfd" は S′/IS′（界面の `quotientAlgebra R T (I.map f)`）。
- E3 の欄：`e3Excision f I h_S h_T h_I harc : IsPullbackSquare (ordinarySquare … ≫ e3Perfd)`。S・T 完備なので `e3Perfd_of_complete`（A4-3）で
  S_perfd などに読み替える。**商の扱い（W9-II-15 で訂正）**：S/I は S・I の導来 p 完備性から導来 p 完備（cofiber で閉じる）だが、**T/IT は一般に導来 p 完備でない**
  （反例：R = Z_p[p^{1/p^∞}]^∧、S = R ⊕ c₀(R)、T = R⟨t⟩ ⊕ c₀(R⟨t⟩) の平方零拡大、I = 0 ⊕ c₀(R)。S・T・I は完備で `ArcOutside` も成り立つが、IT は c₀(R) の
  R⟨t⟩ 線形包で (p^n t^n)_n を含まず、T/IT の直和因子 c₀(R⟨t⟩)/IT は非零で p 可除）。界面の仮定に IT の完備性はないので、四頂点を完備として
  `e3Perfd_of_complete` を使うことはできない。**修復**：一般の離散 R 代数 U について、perfectoid 標的 P は p 完備なので `completionRing` の普遍性から
  F_U = Hom_R(U, −) ≃ F_{completionRing U}（Perfd 上の前層として自然同型）、よって Γ(F_U, O) ≃ Γ(F_{completionRing U}, O) ≃ (completionRing U)_perfd = e3Perfd(U)
  （Prop 8.5 の Type u 版、D41 の定義そのもの）。四角形は商写像・比較写像・二つの合成の一致を含めて前層の自然変換として移し、S8 の押し出しは元の商 U の
  Hom 前層で取る（F_{T/IT} ↪ F_T の単射性は T → T/IT の全射性から。T → completionRing(T/IT) の全射性は要らない）。affCompl_κ の対象として商を使う箇所は
  completionRing(T/IT) を用いる。
- 証明の筋は §3.2。

### 2.4 S8：空間値の層と E 値の層の局所性（∞ 側の一般論、新）

Cor 8.12 の原典の証明に要る一般論。Sheaves/ の層（S1〜S4、E 値）に加えて：
1. site 𝒞 上の空間値前層 PSh(𝒞) = Fun(𝒞^op, 𝒮)（E = 𝒮、F2 の `SigmaPresheafInfinity` と同じ台）と J 層（Čech、HTT 6.2.2.6）、層化 L
   （HTT 6.2.2.7。S4 は `IsStable E` を仮定しているので 𝒮 には別の構成：HTT 6.2.2.7 の ∞ トポスの局所化）。
2. 0 切り捨て：離散な前層（集合の前層）の L は離散で、1 圏の層化（Mathlib `CategoryTheory.Sheaf`、`presheafToSheaf`）に一致（HTT 6.4.?・
   5.5.6.28：左完全な左随伴は n 切り捨てを保つ）。よって集合の前層の射が 1 圏の層化で同型なら L で同値（J 局所同値）。
3. 単射に沿う離散対象の押し出しは離散（空間で成り立ち、前層では点ごと、層化は 2 で離散を保つ）。
4. E 値の層 O（E 表示可能）と空間値前層 F に対する切断 Γ(F, O) := lim_{el(F)} O（el(F) は F の元の圏、重み付き極限）。F ↦ Γ(F, O) は前層の
   余極限を極限に送る。O の制限的 Kan 延長 O^ : PSh(𝒞)^op → E（HTT 5.1.5.6、極限を保つ）と Γ(F, O) = O^(F)。
5. 局所性：O が J 層 ⇔ O^ が生成 sieve の射 h_S ↪ h_c を同値に送る ⇒ O^ はすべての J 局所同値を同値に送る（O^ の逆像の類は強飽和で生成系を含む、
   HTT 5.5.4.20 の筋）。よって集合の前層の射 P → Q が 1 圏の層化で同型なら Γ(Q, O) ≃ Γ(P, O)。
6. 代表可能前層 h_c の切断 Γ(h_c, O) = O(c)（Yoneda）、前層 F_T := Hom(T, −)（T は site の外の環）の元の圏は Perfd_{T/} で Γ(F_T, O) = lim_{Perfd_{T/}} O。

S8 の 1〜3 は ∞ トポスの基本（HTT 6.2.2・6.4）で、Sheaves/ の層に置くか別層にするかは調整役。4〜6 は E 値の層の側で Sheaves/ の続き。
Cor 8.12 で使うのは 2・3・5・6（1 は 2 の前提）。**決定項目 3**。

## 3. 証明の筋

### 3.1 Prop 8.10 前半（arc 被覆 R → S の完備 Čech 複体の完全性）

原典 p.67–68 を affine で追う：
1. tilt（零環を含む `tiltRing`、G-A6-14）：R^♭ → S^♭ は完全 F_p 代数の射、d は ker(A_inf(R) → R) の生成元で、R = W(R^♭)/d、S = W(S^♭)/d、S ⊗̂_R S = W(S^♭ ⊗̂_{R^♭} S^♭)/d
   （a := d mod p ∈ R^♭ 進完備テンソル。原典は d と書く。G-A6-4：perfectoid の完備テンソルの tilt）。よって「0 → R^♭ → S^♭ → S^♭ ⊗̂ S^♭ → ⋯（a 進完備）が完全」を
   示せばよい（G-A6-5、**W9-II-20 で訂正**：正則なのは Witt 環 W(B)（B 完全）上の distinguished 元 d であって、tilt 上の a ではない。R が標数 p なら d = p、
   a = 0 で「tilt は d ねじれなし」は偽。手順：augmented 余単体的な完全環 B^• に levelwise に W_n を当て、加法群の短完全列 0 → W_{n−1}(B^•) → W_n(B^•) → B^• → 0
   （V による）から帰納で各 W_n(B^•) の Čech 複体が完全、遷移 W_n → W_{n−1} は項ごとに全射なので Rlim = lim（Mittag-Leffler）で W(B^•) の複体も完全、
   各 W(B^k) で d は正則（Lemma 2.34）なので d の cofiber は通常の商の複体 W(B^•)/d で完全。「W を交代和微分に直接当てる」意味ではない）。
2. Spec(S^♭) ⊔ Spec(R^♭[1/a]) → Spec(R^♭)（a := d mod p）は完全スキームの arc 被覆（[BM18, Def 1.2]：階数 ≤ 1 の付値環で試す）。**W9-II-21 で分岐を補記**：
   試験射 R^♭ → V を取る。V → V_perf は整・局所・単射で忠実平坦なので最初から V は完全としてよい。
   - a が V で単元なら R^♭[1/a] → V が持ち上げ。
   - V が階数 1 で a が非零非単元なら、a 進位相は付値位相と一致し、a 進完備化 V̂ は完全な階数 1 の付値環、V → V̂ は局所単射で忠実平坦。untilt V̂^♯ := W(V̂)/d は
     p 完備な階数 1 の付値環（G-A6-6）。
   - V が階数 1 で a = 0 なら a 進完備化は V 自身、W(V) で d は p の単元倍なので V^♯ = W(V)/d = V（階数 1 を保つ）。
   - V が階数 0（完全体 k）で a が非単元なら a = 0。完全な階数 1 の付値環 V₁ := k[t^{1/p^∞}]_{(t^{1/p^∞})} の t 進完備化へ移る（k → V₁ は忠実平坦）と前の分岐に戻る。
     階数 0 を p 完備版 Def 8.7 にそのまま代入する必要はない。
   R → V̂^♯ に仮定（R → S が arc 被覆）を当て、必要なら perfectoid な W（G-A6-3）に拡大して S → W、V̂ → W^♭ は局所単射で忠実平坦、S^♭ → W^♭。これを前の拡大と
   合成すれば {R^♭ → S^♭, R^♭ → R^♭[1/a]} は階数 ≤ 1 の全試験対象について arc 被覆。G-A6-6（階数 1 の付値環の tilt と untilt：V 完全 a 進完備 ⇒
   V^♯ = W(V)/d は p 完備階数 1 付値環で (V^♯)^♭ = V；W perfectoid 階数 1 付値環 ⇒ W^♭ も。untilt が付値環であることの計算：完全 prism の商として U は局所・被約・
   p ねじれなし、非零元を p 冪で割って mod p 非零にし Teichmüller の像で x = b^♯ + ϖc、V̂ の可除性の全順序で x = b^♯(1 + (ϖ^♭/b)^♯c) と単元倍の sharp に書ける。
   [Česnavičius–Scholze, Purity for flat cohomology, Prop 2.1.9] の証明と同じ。証明の参照であって第四の黒箱ではない）。
3. **G-A6-1**（三つの引用 1a・1b・1c から）：完全 F_p 代数の arc 被覆 A → B について 0 → A → B → B ⊗_A B → ⋯ は完全。
   A = R^♭、B = S^♭ × R^♭[1/d] に適用。
4. 導来 d 進完備化：完備化は完全関手で R^♭[1/d] を含む項の完備化は零。よって 0 → R^♭ → S^♭ → S^♭ ⊗̂ S^♭ → ⋯ が完全（G-A6-7：
   Čech 複体の完備化と、B ⊗_A B の各項の分解で R^♭[1/d] が混じる項の消え方。紙 2）。

### 3.2 Cor 8.12

原典 p.69 を affPerfd_κ の上で追う。S′ は与えられたもの、S″ := S′ × S/I。
1. S → S″ は arc 被覆（S → V が I を殺せば S/I を通り、殺さなければ `ArcOutside` で S′ → V に延びる。W = V でよい）。
2. perfd は有限積を保つ（G-A6-2）：Prop 8.5 の極限の形で Perfd_{(S′ × S/I)/} ≅ Perfd_{S′/} × Perfd_{(S/I)/}（冪等元で分解、perfectoid の
   因子は perfectoid）、積圏上の T′ × T″ の極限は極限の積。よって S″ の四角形（S → S″、I）が引き戻しなら S′ の四角形も引き戻し
   （S″/IS″ = S′/IS′ × S/I。左上の S_perfd は積に変わらないので「S′ の四角形と恒等の四角形の文字どおりの積」ではない（W9-II-19）。
   B := S′_perfd、C := (S/I)_perfd、D := (S′/IS′)_perfd、g : B → D（S′ → S′/IS′ から）、h : C → D（S/I → S′/IS′ から）と書くと、S″ の四角形の引き戻しは
   (B × C) ×_{D × C} C（B × C → D × C は (g, id_C)、C → D × C は (h, id_C)）で、
   有限極限の計算により B ×_D C に標準的に同値、各射影は元の商写像と両立する。よって S″ の四角形が引き戻しなら S′ の四角形も引き戻し）。以下 S′ := S″。
3. 集合の層の等式（1 圏、Mathlib の `Sheaf` で）：arc 層 F（集合値、affPerfd_κ 上）とその延長 F(T) := lim_{Perfd_{T/}} F = Hom(F_T, F) に対し
   F(S) = F(S′) ×_{F(S′/I)} F(S/I)。証明：S → S′ に沿う降下 F(S) = eq(F(S′) ⇉ F(S′ ⊗̂_S S′))（延長が arc 被覆で層条件を満たすこと：
   F_{S′} → F_S が局所全射で Čech 脈体の余等化子が F_S、G-A6-8）。S′ ⊗̂_S S′ → S′ × (S′/I ⊗̂_{S/I} S′/I)（乗法と mod I）は arc 被覆
   （S′ ⊗̂_S S′ → V で I ↦ 0 なら第二因子、そうでなければ `ArcOutside` の一意性で二つの S′ → V が一致し乗法を通る）ので
   F(S′ ⊗̂_S S′) ↪ F(S′) × F(S′/I ⊗̂ S′/I)。x ∈ F(S′) の二つの像は乗法成分では両方 x、mod I 成分では x̄ ∈ F(S′/I) の二つの像。
   よって等化子 = {x : x̄ ∈ eq(F(S′/I) ⇉ F(S′/I ⊗̂_{S/I} S′/I)) = F(S/I)}（S/I → S′/I は分裂 arc 被覆）= F(S′) ×_{F(S′/I)} F(S/I)
   （F(S/I) ↪ F(S′/I) は分離性）。
4. 3 は「F_S は集合の層の圏で F_{S′} ⊔_{F_{S′/I}} F_{S/I}」と同値（Yoneda：Hom(F_T, F) = F(T)）。F_{S′/I} ↪ F_{S′} は単射（S′ → S′/I 全射）
   なので前層の押し出し P := F_{S′} ⊔_{F_{S′/I}} F_{S/I}（点ごとの集合の押し出し）は離散で、S8 の 2・3 により P → F_S は J 局所同値。
5. S8 の 5・6：O（arc 層、Prop 8.10）に対し Γ(F_S, O) ≃ Γ(P, O) = Γ(F_{S′}, O) ×_{Γ(F_{S′/I}, O)} Γ(F_{S/I}, O)、Γ(F_T, O) = lim_{Perfd_{T/}} O = T_perfd
   （Prop 8.5、Type u 版と κ 版の一致。O は CAlg_ℤ 値で、F_T の元の圏の上で CAlg_R 値に持ち上げてから極限を取る、W9-II-22）。引き戻しの射が perfd の関手性の射に一致することは紙 4。
6. CAlg_R の引き戻し：U は極限を保ち反映する（G-A5-16）。界面の `IsPullbackSquare` の形へ。

## 4. 必要な一般論（G-A6）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A6-1a | （11-13 追記：11-05 夜の改訂（D56・D59 改訂、a9-design §3）で引用ではなく証明する。⑥ の BS17 Thm 4.1 (i) `cech_exact_of_vCover_perfect`、原典どおりの経路）**引用（`sorry`）**[BS17, Thm 4.1 (i)]（n = 1、E = O）：完全 F_p 代数 A と**完全** F_p 代数 B への v 被覆 A → B（[BS17, Def 2.1]：任意の付値環 V と A → V に付値環の拡大 V ↪ W と B → W。被覆と Čech の各項は完全スキームの圏で取る、W9-II-18）について A = RΓ_v(Spec A, O)、すなわち 0 → A → B → B ⊗_A B → ⋯ が完全（有限族の形で述べる） | なし | Prop 8.10 |
| G-A6-1b | （11-13 追記：11-05 夜の改訂（D56・D59 改訂、a9-design §3）で主経路から外した。G-A6-1 は BS-W12 の経路 B で直接示す）**引用（`sorry`）**[BM18, Thm 1.7]（BS の引用では Thm 1.6）：finitary（filtered 余極限と可換）な F : (qcqs スキーム)^op → D(ℤ)^{≥0}（cohomological に coconnective：H^i = 0 for i < 0。環の圏の上では**共変** Ring_{F_p} → D(ℤ)^{≥0}、W9-II-17）について、F が arc 層 ⇔ F が v 層かつ、分数体が代数閉な任意の付値環 V と素イデアル 𝔭 ⊂ V について F(V) → F(V/𝔭)、F(V_𝔭) → F(κ(𝔭)) の四角形が cartesian。affine 版（F_p 代数の圏上の共変 finitary 関手、κ-small）で述べる（D59。affine から qcqs への延長の根拠は Zariski 降下：v 層は有限 affine 開被覆の降下を満たすので affine の値から qcqs 上へ延長でき、finitary 性は有限段の降下と一様に coconnective な Tot の filtered 余極限との交換で確認する。定義の変更でも第四の黒箱でもない） | なし | Prop 8.10 |
| G-A6-1c | （11-13 追記：本体で証明済み。`valuationRing_milnorSquare`・`valuationRing_milnorSquare_perfect`（Perfectoidization/Derived/ArcValuationMilnor:43・87））**引用（`sorry`、後で証明）**[BS17, Lemma 6.3]（Lemma 6.2 は付値環による v 被覆の主張で、この四角形ではない。W9-II-18）：**完全**付値環 V と素イデアル 𝔭 について 0 → V → V_𝔭 ⊕ V/𝔭 → κ(𝔭) → 0 が完全、すなわち V → V_𝔭、V → V/𝔭、→ κ(𝔭) の四角形は環の圏で cartesian（V = V_𝔭 ×_{κ(𝔭)} V/𝔭）かつ cocartesian。任意の付値環での同じ主張は引用ではなく初等補題として証明する（𝔭V_𝔭 = 𝔭：a ∈ 𝔭、s ∉ 𝔭 で a/s ∉ V なら s/a ∈ V、s ∈ 𝔭 で矛盾；よって V_𝔭/𝔭 = κ(𝔭) で核が一致し短完全列、cocartesian は局所化と商の可換性）。引用はその特殊化。適用する付値環（分数体が代数閉、標数 p）は完全なので特殊化で足りる | なし（Mathlib の `ValuationRing` で証明可能） | Prop 8.10 |
| G-A6-1 | （11-13 追記：11-05 夜の改訂（D56・D59 改訂、a9-design §3）と BS-W12（`bhatt-scholze-codex-w12.md`）の経路 B では、[BM18, Prop 4.8] の議論を O の場合に 1 圏で直接示す（1b は使わない）。B1〜B5 は本体（`HomologicalAlgebra/Cech/`、`Perfectoidization/Derived/Arc*`、`CommutativeAlgebra/ValuationInterval/`）、組み立て B6 は ⑥ の BS17 待ちで drafts/A6/ArcRouteB）三つから：完全 F_p 代数の有限族の arc 被覆 {A → B_i} について 0 → A → ∏B_i → ∏ B_i ⊗_A B_j → ⋯ が完全。F := (A ↦ A_perf) は F_p 代数上の finitary な関手で、v 層（1a を完全化に当てる。完全化は v 被覆を保つ）、分数体が代数閉な付値環は完全なので四角形は 1c の Milnor 四角形、よって 1b で arc 層 | 上の三つ | Prop 8.10 |
| G-A6-2 | perfd は有限積を保つ（Prop 8.5 の極限の形、Perfd_{(S′×S″)/} ≅ Perfd_{S′/} × Perfd_{S″/}、perfectoid の因子は perfectoid） | なし | Cor 8.12 の 2 |
| G-A6-12 | perfectoid 環の有限積は perfectoid（§2.2 の ∏R_i、G-A6-2 の逆向き）。**直接証明**：有限積と tilt・Witt ベクトルの可換性、各因子の核生成元の組、空積は零環として別処理。既存 `isIntegralPerfectoid_finPi`（CompletedTensor.lean）は E3 の `Inputs.exists_perfectoidization_of_integral` を使うので**使えない**（W9-III-08）。骨組み：`drafts/A6/PerfectoidFiniteProduct.lean`（`isIntegralPerfectoid_prod`・`isIntegralPerfectoid_pi`・`isIntegralPerfectoid_finPi'`、11-03）。**11-13 追記：済**（BS-W10 作業 A、main cc67ea88e。`isIntegralPerfectoid_finPi`（BhattScholze/Perfectoid/FiniteProduct:250）は E3 非依存の直接証明、drafts の骨組みは削除） | `IsIntegralPerfectoid`（既存の判定）、Mathlib `Perfection`・`WittVector`・`fontaineTheta` | §2.2、Cor 8.12 の 2 |
| G-A6-3 | p 完備な階数 1 の付値環 V は perfectoid な p 完備階数 1 付値環 W に忠実平坦に埋まる（絶対整閉包の p 完備化、付値の延長）。W には p の両立する p 冪根があり R₀ → W が取れる | なし（Mathlib の付値の延長、要確認） | Lemma 8.8（G-A6-11 と合わせて。W を**先に**取る）、§3.1 の 2 |
| G-A6-4 | perfectoid の完備テンソルの tilt：(S ⊗̂_R S′)^♭ = (S^♭ ⊗_{R^♭} S′^♭)^∧_a（a = d mod p 進）。**零環を含む**（D1-03：両因子が非零でも相対完備テンソルは零になり得る。F_p × F_p の二つの射影） | `CompletedTensor` の芯、`WittQuotientTilt`（部分） | §3.1 の 1 |
| G-A6-14 | 零環を含む tilt `tiltRing`（D1-03、11-03）：p 完備 O が零環なら零環、非零なら Mathlib `PreTilt O p`（p 完備で非零なら p は Jacobson 根基に入り非単元）。関手性 `tiltMap`（零→零、非零→零、非零→非零の三つ。零→非零の環準同型はない）。原典の tilt は零環で零環なので定義の変更ではなく、Mathlib の `PreTilt` の環構造が `¬IsUnit p` を仮定することへの対処 | Mathlib `PreTilt`・`Perfection.map` | A6 の tilt を使う全主張 |
| G-A6-5 | 余単体的な完全環 B^• に levelwise の W_n、V の短完全列 0 → W_{n−1} → W_n → B → 0 で Čech 複体の完全性を帰納、項ごとに全射な遷移の Rlim で W(B^•) へ、各 Witt 環で正則な d（Lemma 2.34）の cofiber で mod d へ（W9-II-20：正則なのは W(B) 上の d。tilt 上の a = d mod p は零になり得る） | Mathlib `WittVector`（部分） | §3.1 の 1 |
| G-A6-6 | 階数 1 の付値環の tilt・untilt（V 完全 a 進完備 ⇒ W(V)/d は p 完備階数 1 付値環、(V^♯)^♭ = V；a = 0 なら V^♯ = V；perfectoid 付値環の tilt は付値環）。分岐（a 単元／階数 1 で a ≠ 0／階数 1 で a = 0／階数 0 は V₁ = k[t^{1/p^∞}]^∧ へ）は W9-II-21。付値環性の計算は [Česnavičius–Scholze, Prop 2.1.9] の証明と同じ（参照のみ） | `WittQuotientTilt`（環の部分）、付値は なし | §3.1 の 2 |
| G-A6-7 | 導来 d 進完備化は完全列を保ち、d が可逆な項を殺す；Čech 複体の各項の分解 | HA/DerivedCompletion（2b 後の名前） | §3.1 の 4 |
| G-A6-8 | 基底上の集合の層の延長 F(T) := lim_{Perfd_{T/}} F は arc 被覆で層条件を満たす（1 圏、右 Kan 延長） | Mathlib `Functor.IsCoverDense`、`Functor.inducedTopology`、`Functor.sheafInducedTopologyEquivOfIsCoverDense`（= `Functor.IsDenseSubsite.sheafEquiv`、`Sites/DenseSubsite/{InducedTopology,Basic}.lean`。包含は opposite `affPerfdInclusion.op` で渡し、値の圏 Set は `HasLimitsOfShape (StructuredArrow X G.op)` を満たす。W9-II-25 で名前を訂正。**向き（11-03、D3-06）**：同値は `Sheaf (G.inducedTopology K) A ≌ Sheaf K A` なので、affPerfd_κ の層から affCompl_κ の層への延長 F ↦ F̃ はこの同値の `.functor`（右 Kan 延長）、`.inverse` が G に沿う制限。「制限の逆」の意味で `.functor` を使う） | §3.2 の 3 |
| G-A6-9 | 完備テンソルの arc 被覆（§3.2 の 3 の二つ）と `ArcOutside` からの arc 被覆性 | なし | §3.2 |
| G-A6-10 | S・I 導来 p 完備 ⇒ S/I 導来 p 完備（cofiber）。**T/IT には成り立たない**（W9-II-15 の反例）ので、一般の商 U は `completionRing U` 経由：F_U ≃ F_{completionRing U}（perfectoid 標的は p 完備）と Γ(F_U, O) ≃ e3Perfd(U) の自然同型、四角形全体を自然変換として移す | HA/DerivedCompletion（要確認）、`completionRing` の普遍性（既存） | E3 の欄 |
| G-A6-11 | Lemma 8.8 の前段（W9-II-16）：R₀ := ℤ_p[p^{1/p^∞}]^∧ は perfectoid；S₀ := completionRing(S ⊗_{ℤ_p} R₀) は p 完備な R₀ 代数で #S₀ ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ；S → S₀ は p 完備忠実平坦（記録。E3 には不要）；S → V（試験付値環）は perfectoid な W（G-A6-3）と p の p 冪根の選択を経て S₀ → W に延びる | R₀ の perfectoid 性（要確認：既存の例があるか）、`completionRing`（既存） | Lemma 8.8 = cover-dense |
| S8 | §2.4 の 1〜6 | なし（Sheaves/ の続き、∞ トポス） | Cor 8.12 の 4・5 |

## 5. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D53 | arc 位相は p 進形式スキーム fSch の上、Perfd ⊂ fSch | affine（κ-small の p 完備環 affCompl_κ）の上に定義し、affPerfd_κ は誘導位相の充満部分 site（決定 4 の (a′)）。非 affine は定義しない | fSch の affine 部分。E3 の経路は affine で閉じる（§9） |
| D54 | arc 被覆は qcqs な一つの射、位相は arc 被覆と開被覆で生成 | [BM18, Def 1.2] の有限族の形で定義（affine では開被覆は有限族に含まれる） | 同じ位相（affine 上） |
| D55 | Cor 8.11：S_perfd = RΓ_arc(Spf S, O)（fSch 上の層コホモロジー）と arc 降下 | affine 版「S_perfd ≃ RΓ_arc(affPerfd_κ/S, O)」を記録として述べる（Prop 8.10＋Prop 8.5）。fSch・affCompl_κ 上の RΓ との比較（∞ 版の比較補題）はしない。Lemma 8.8 の affine 版は cover-dense として証明の中で使う | E3 で使う等式は Prop 8.5 の極限の形 |
| D56 | Prop 8.10 の証明は [BS17, Thm 4.1]・[BM18, Thm 1.6]・[BS17, Lemma 6.3] を引用 | （11-13 追記：11-05 夜に改訂。引用はなし：1a は ⑥ の BS17 で証明、1b の一般形は主経路から外し G-A6-1 を O の場合に 1 圏で直接（BS-W12 の経路 B）、1c は本体。以下は改訂前）三つを**別々に**引用の形で述べ `sorry`（G-A6-1a・1b・1c）、三つから G-A6-1 を導き、tilt への帰着は証明する（決定 2、2026-11-02） | 引用を定理の形に。1c は完全付値環の Lemma 6.3 の形で引用し、一般の付値環版は初等補題（W9-II-18） |
| D59 | [BM18, Thm 1.7] は qcqs スキーム上の関手について | （11-13 追記：11-05 夜の改訂で 1b の一般形は主経路から外したので、この差は主経路では使わない。以下は改訂前）affine 版（F_p 代数の圏上の共変 finitary 関手 Ring_{F_p} → D(ℤ)^{≥0}、v 被覆・arc 被覆は有限族）で述べる。qcqs スキームへの延長は使わない（根拠の Zariski 降下は G-A6-1b の行に記録、W9-II-17） | 特別な場合 |
| D57 | Cor 8.12 の証明は Perfd 上の空間の層 | S8（空間値の層と E 値の層の局所性）を一般論として立てる。集合の層の等式は 1 圏（Mathlib）で | 同じ証明。∞ 側の一般論が一つ増える（決定項目 3） |
| D58 | 「S′ を S′ × S/I に替える」 | perfd が有限積を保つこと（G-A6-2）を Prop 8.5 から示して戻す | 原典が省く一歩を補う |

## 6. 単位と順序

| 単位 | 内容 | 依存 |
| --- | --- | --- |
| A6-1 | arc site（affCompl_κ と affPerfd_κ、coverage、Lemma 8.8 の affine 版＝cover-dense） | 既存の perfectoid、`CompletedTensor`、S1、Mathlib `IsCoverDense` |
| A6-2 | Prop 8.10（tilt への帰着、黒箱 G-A6-1、Hom の層性） | A6-1、G-A6-4〜7 |
| A6-3 | 集合の層の等式（§3.2 の 1〜4、1 圏）、G-A6-2、G-A6-9 | A6-1、A5 |
| A6-4 | Cor 8.12（S8 を入力に）と E3 の `excision` | A6-2、A6-3、S8、A4-3、A5-1 |

骨組みは A6-1 → A6-3 → A6-2 → A6-4。S8 は Sheaves/ の続きとして drafts/Sheaves/SpaceValued.lean に主張だけ置く（置き場所は調整役）。

## 7. 決定事項

決定（2026-11-02、ユーザー）：
- 1：(a) affine（κ-small の perfectoid 環）の上、有限族の形。**ただし必要な証明が affine で閉じることを確認する**（§9 に確認結果）。
- 2：三つの引用 [BS17, Thm 4.1]・[BM18, Thm 1.7（BS の引用では 1.6）]・[BS17, Lemma 6.2/6.3] を**別々に**、原典が引用している形で述べて `sorry` にする
  （G-A6-1a・1b・1c）。合わせた G-A6-1 はそこから導く。1c は初等的なので後で証明する。
  （11-13 追記：11-05 夜の改訂（ユーザー、sorry 0）でこの決定は改めた。上の D56 の行と a9-design §3。）
- 3：(a) S8 を ∞ 側の一般論として立て、集合の層の等式は Mathlib の 1 圏の層で証明する。
- 4：**案 (a′)**（§10、2026-11-02 決定）：arc site は κ-small の p 完備環 `affCompl_κ` の上に定義し、affPerfd_κ は cover-dense な充満部分 site。
  Lemma 8.8 の affine 版は `IsCoverDense`、集合の層の延長は Mathlib の `Functor.sheafInducedTopologyEquivOfIsCoverDense`（W9-II-25 で名前を訂正）、Cor 8.11 は affPerfd_κ/S 上の RΓ で記録として述べる。
  **W9-II-16（2026-11-03）**：cover-dense の証明は前段 G-A6-11（R₀ = ℤ_p[p^{1/p^∞}]^∧ 上へ移す被覆）の後に A5-4 の根添加。global な affCompl_κ は維持
  （Codex の推奨 (a)。別案 (b)「固定 perfectoid R 上の相対 site に全体を揃える」は D53・型・比較補題の範囲の書き換えが要るので採らない）。
- 5：(a) 付値環の tilt・untilt は A6 の中で主張を置く。

相談した選択肢（記録）：

1. arc site の範囲：affine（κ-small の perfectoid 環）の上にだけ定義し、有限族の形で（D53・D54、推奨）／p 進形式スキームを定義する（範囲外）。
2. Prop 8.10 の外部入力：三つの引用を合わせた一つの黒箱 G-A6-1（完全 F_p 代数の arc 被覆の Čech 完全性）として置き、tilt への帰着は証明する
   （D56、推奨。結晶の黒箱と同列、独立の作業単位）／[BS17, Thm 4.1]・[BM18, Thm 1.6] を証明する（長い。別計画）。
3. Cor 8.12 の層の議論：S8（空間値の層の層化・0 切り捨て・E 値の層の局所性）を ∞ 側の一般論として立て（D57、推奨）、集合の層の等式は Mathlib の
   1 圏の層で証明する／S8 を避けて E 値の Tot で直接「ほどく」— 検討したが見通しが立たない（arc 被覆に沿う Tot の各項をさらに被覆で分解する必要）。
4. Lemma 8.8・Cor 8.11：記録のみ（Lemma 8.8 の affine 版は A5-4 の S̃ から一行、Cor 8.11 は述べない、D55、推奨）／Cor 8.11 も affine の形で述べる。
   （※「S̃ から一行」は誤り：A5-4 の semiperfectoid 性は perfectoid 基底を要する。前段 G-A6-11 が要る、W9-II-16。）
5. G-A6-3・G-A6-6（付値環の tilt・untilt、絶対整閉包への埋め込み）：A6 の中で主張を置く（推奨）／既存の CLMST の付値の道具（`Prop247*Valuation`）を
   先に確認する。

## 8. 紙で確かめる項目

1. arc 被覆の底変換・合成の安定性（W の取り方）、有限族と単射 R → ∏ R_i の同値。
2. §3.1 の 4：R^♭[1/d] を含む項の完備化が消えること、Čech 複体の項の分解と完備化の交換。
3. §3.1 の 2：V を完全にとってよいこと、a 進完備化しても付値環であること、untilt の付値環性（G-A6-6）。W9 続き 6 で ○（分岐 a 単元／階数 1 で a ≠ 0／階数 1 で a = 0／階数 0、W9-II-21）。
4. §3.2 の 5：引き戻しの射が perfd の関手性の射（S → S′ など）の像に一致すること。
5. §3.2 の 3：延長 F(T) の層条件（G-A6-8）と、二つの arc 被覆の確認。
6. G-A6-2：perfectoid の因子 eT が perfectoid であること、Perfd_{(S′×S″)/} の分解。
7. §2.3 の商の扱い（W9-II-15）：F_U ≃ F_{completionRing U} の自然同型、Γ(F_U, O) ≃ e3Perfd(U)、商写像を含む四角形の自然変換としての移送、
   S8 の押し出しを元の商の Hom 前層で取ること（Codex W9 続き 5 で ○）。
8. Lemma 8.8 の前段（G-A6-11、W9-II-16）：R₀ の perfectoid 性、S₀ の R₀ 代数構造と濃度、W の中での p の p 冪根の選択と R₀ → W、`rootClosure_extends` の
   順序（W を先に取る）、修復後の cover-dense から `sheafInducedTopologyEquivOfIsCoverDense` による層の延長までの全接続（W9 続き 6 で ○：R₀ の perfectoid 性は
   W(F_p[t^{1/p^∞}]^∧_t)/([t] − p) との同型で具体的に、濃度は μ = (#S + ℵ₀)^{ℵ₀} で閉じる、右 Kan 延長の T での値が lim_{Perfd_{T/}} F）。
9. §2.2 の O の値域（CAlg_ℤ）と、F_U の元の圏での CAlg_R への持ち上げ・忘却が極限を作ること（W9-II-22）。

## 9. affine で閉じることの確認（決定 1 の確認、2026-11-02）

原典 §8.2 の証明で site・層・被覆が使われる箇所をすべて挙げ、affine（κ-small の perfectoid 環、有限族の arc 被覆）で足りるかを確かめた。

| 箇所 | 原典の対象 | affine 版での扱い | 判定 |
| --- | --- | --- | --- |
| Prop 8.10 の冒頭「Zariski 降下で affine に帰着」 | 非 affine X | site の対象が最初から affine なので不要 | ○ |
| Prop 8.10 の被覆 R → S | 単射 arc 被覆 | 有限族 {R → R_i} を R → ∏R_i に置き換える（∏R_i は perfectoid、単射の生成 sieve と同じ位相） | ○ |
| Prop 8.10 の tilt と Čech 複体 | perfectoid 環の完備テンソル | すべて環の計算（G-A6-4・5・7。正則性の記述は W9-II-20 で訂正） | ○ |
| Spec(S^♭) ⊔ Spec(R^♭[1/a]) → Spec(R^♭) | 完全スキームの arc 被覆 | 有限族 {R^♭ → S^♭, R^♭ → R^♭[1/a]} として G-A6-1 に当てる（階数 0・a = 0 の分岐込み、W9-II-21） | ○ |
| [BS17, Thm 4.1]・[BM18, Thm 1.7] | qcqs スキーム上 | affine の特別な場合（Spec の有限族）として述べる（D59）。引用は `sorry` なので形だけ合わせる | ○（D59） |
| 付値環の試験対象 V・W | p 完備な階数 1 の付値環（任意の大きさ） | site の対象ではなく Type u の試験対象。κ の制限を受けない。界面の `ArcOutside` と同じ条件 | ○ |
| Prop 8.10 後半（Hom(X, T) の層性） | 一般の形式スキーム T | 使うのは T affine（S・S′・S/I・S′/I）だけ：H⁰ の等化子から直ちに出る | ○（非 affine は不要） |
| Cor 8.12 の F_T = Hom(−, Spf T) | Perfd 上の層 | affPerfd_κ 上の集合の前層 R ↦ Hom(T, R)、層性は Prop 8.10 後半 | ○ |
| Cor 8.12 の Spf S′ ⊔ Spf(S′/I) ×_{Spf(S/I)} Spf(S′/I) → Spf S′ ×_{Spf S} Spf S′ | 形式スキームのファイバー積と非交和 | 完備テンソル S′ ⊗̂_S S′、S′/I ⊗̂_{S/I} S′/I と有限積 S′ × (⋯)。有限族の arc 被覆 | ○ |
| Cor 8.12 の降下「Spf S′ → Spf S に沿う」 | S は perfectoid でない | 集合の層を affPerfd_κ から p 完備環へ延長して使う（G-A6-8。§10 の案なら Mathlib の dense subsite で。cover-dense の証明は前段 G-A6-11 つき、W9-II-16） | ○（延長が要る） |
| Γ(F_T, O) = T_perfd | Cor 8.11（fSch 上の RΓ_arc） | Prop 8.5 の極限の形（Type u 版と κ 版の一致は A5 の D47） | ○（Cor 8.11 不要） |
| κ の制限 | — | 使う環（S・S′・S/I・S′/I・S₀・S̃₀・(S̃₀)_perfd・完備テンソル冪・有限積）はすべて濃度 ≤ κ（κ^{ℵ₀} = κ。前段 S₀ の分は W9-II-16 で追加、#S₀ ≤ (#S + ℵ₀)^{ℵ₀}） | ○（前段を含めて W9 続き 6 で ○） |

結論：E3 に要る Prop 8.10（affine）と Cor 8.12 の証明は affine で閉じる。非 affine の主張は引用 1a・1b の原典の形だけで、そこは affine の
特別な場合として述べる。唯一の注意は「集合の層の p 完備環への延長」（G-A6-8）で、§10 の案で自然に扱える。

## 10. 決定 4 の再検討（Lemma 8.8・Cor 8.11）

§9 の確認で、Cor 8.12 の集合の層の等式（§3.2 の 3）は「arc 層 F を perfectoid でない p 完備環 S・S′・S/I に延長して、S → S′ に沿う降下を使う」
段を含むことが分かった。これは原典が Lemma 8.8（Perfd が基底）を使って暗黙に行っている延長で、affPerfd だけの site では G-A6-8 として
手で作ることになる。そこで決定 1 の範囲を少し広げる案：

- **案 (a′)**：arc site を **κ-small の p 完備環**（affine の p 進形式スキーム、`affCompl_κ`）の上に Def 8.7 の affine 版で定義し、affPerfd_κ はその
  充満部分圏に誘導位相（原典の "Perfd ⊂ fSch with the induced topology" の affine 版）。
  - Lemma 8.8 の affine 版「任意の p 完備環は perfectoid による arc 被覆をもつ」が **affPerfd_κ ⊂ affCompl_κ が cover-dense** という
    load-bearing な主張になり、Mathlib の `Functor.IsCoverDense` と `Functor.sheafInducedTopologyEquivOfIsCoverDense`（= `IsDenseSubsite.sheafEquiv`、1 圏の層の圏同値、比較補題。W9-II-25）で
    集合の層の延長 G-A6-8 がそのまま得られる。§3.2 の 3 の降下は affCompl_κ の site の層条件そのもの。
  - Cor 8.11 の affine 版「S_perfd ≃ RΓ_arc(affCompl_κ/S, O^♯)」も述べられる：∞ 版の比較補題（dense subsite で E 値の層の圏が同値）が
    あれば Prop 8.5＋Prop 8.10 から従う。∞ 版の比較補題は S8 に入れるか、Cor 8.11 を「affPerfd_κ/S 上の RΓ」で述べて fSch との比較は
    しないかのどちらか。E3 には不要なので後者（記録）でよい。
  - 費用：site の定義は同じ（被覆の条件は環の種類によらない）。cover-dense の証明は**前段 G-A6-11（R₀ 上へ移す被覆）＋A5-4 の S̃**
    （W9-II-16 で訂正。元の「S̃ から一行」は A5-4 の perfectoid 基底の仮定を見落としていた。§2.1）。
- **案 (a)（元の案）**：affPerfd_κ だけ。G-A6-8 を手で作る（右 Kan 延長が層になることを直接示す）。Lemma 8.8 は記録、Cor 8.11 は述べない。

推奨は (a′)：原典の構造（fSch ⊃ Perfd、Perfd は基底）に近く、Mathlib の dense subsite が使え、Lemma 8.8 が証明の中で実際に使われる形になる。
Cor 8.11 は affine 版を記録として述べる（RΓ は affPerfd_κ/S の上、D55 をその形に直す）。
