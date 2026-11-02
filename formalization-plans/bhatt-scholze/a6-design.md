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
  Prop 8.10（O が arc 層；affine T について Hom(T, −) が集合の arc 層）、Cor 8.12、E3 の `excision`、Lemma 8.8 の affine 版（記録。A5-4 の S̃ から）。
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
| Lemma 8.8 | 定理（affine 版、記録）：任意の p 完備 S は perfectoid による arc 被覆をもつ（S → S̃ → S̃_perfd） | `exists_perfectoid_arcCover` | A5-4 の `rootClosure` | A6-1 |
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
- Lemma 8.8（記録）：p 完備 S に対し S → S̃ → S̃_perfd（A5-4）は arc 被覆（S → V は S̃ → V に延び（A5-4 の (i)）、V を perfectoid に取り替えてから
  S̃_perfd → W。G-A6-3）。

### 2.2 Prop 8.10（affine）

- `structurePresheaf_isArcSheaf`：O : R ↦ R（CAlg_R 値、A0 の `ringPresheafToCAlg`）は arc 位相の Čech 層。S1 の生成系の補題で、
  有限 arc 被覆族 {R → R_i} について O(R) ≃ Tot(O(Čech 余脈体)) を示せばよく、Čech 余脈体は完備テンソル冪（S3 の `CechNerveData`、
  Perfd の余積 = 完備テンソル、既存）。R → ∏ R_i =: S に置き換え（∏ R_i は perfectoid、`PerfdSmall` の有限積）、単射 arc 被覆 R → S に帰着。
- 離散な余単体的環の Tot は Čech 複体 0 → R → S → S ⊗̂_R S → ⋯（非正規化 Tot、A0 の決定）なので、主張は「arc 被覆 R → S の完備 Čech 複体の完全性」。
- `homPresheaf_isArcSheaf (T)`：R ↦ Hom(T, R) は集合の arc 層：H⁰ の等化子 R = eq(S ⇉ S ⊗̂_R S) に Hom(T, −) を当てる。原典 "immediate"。

### 2.3 Cor 8.12 と E3 の欄

- 主張：S → S′ 離散で導来 p 完備、I ⊂ S 導来 p 完備（S 加群として）、`ArcOutside f I` ⇒ CAlg_R の四角形
  S_perfd → S′_perfd、S_perfd → (S/I)_perfd、S′_perfd → (S′/IS′)_perfd、(S/I)_perfd → (S′/IS′)_perfd は引き戻し。
  原典の "(S′/I)_perfd" は S′/IS′（界面の `quotientAlgebra R T (I.map f)`）。
- E3 の欄：`e3Excision f I h_S h_T h_I harc : IsPullbackSquare (ordinarySquare … ≫ e3Perfd)`。S・T 完備なので `e3Perfd_of_complete`（A4-3）で
  S_perfd などに読み替え、S/I・T/IT も導来 p 完備（I 完備な商、要確認：`IsModuleComplete` の商での保存）。
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
1. tilt：R^♭ → S^♭ は完全 F_p 代数の射、d は ker(A_inf(R) → R) の生成元で、R = W(R^♭)/d、S = W(S^♭)/d、S ⊗̂_R S = W(S^♭ ⊗̂_{R^♭} S^♭)/d
   （d 進完備テンソル。G-A6-4：perfectoid の完備テンソルの tilt）。よって「0 → R^♭ → S^♭ → S^♭ ⊗̂ S^♭ → ⋯（d 進完備）が完全」を示せばよい
   （W は完全 F_p 代数の完全列を完全列に送る（W_n は V^k による A の反復拡大、Mittag-Leffler）、mod d は d が各項で正則（perfectoid の tilt は
   d ねじれなし）なので完全性を保つ。G-A6-5）。
2. Spec(S^♭) ⊔ Spec(R^♭[1/d]) → Spec(R^♭) は完全スキームの arc 被覆（[BM18, Def 1.2]）：R^♭ → V（階数 1 の付値環、完全としてよい）で d が可逆なら
   R^♭[1/d] → V、そうでなければ V を d 進完備化し、R^♭ → V は R → V^♯（p 完備な階数 1 の付値環、untilt）に対応、仮定（R → S が arc 被覆）で
   S → W（V^♯ の p 完備な階数 1 の付値環の拡大、perfectoid に取り替えてよい、G-A6-3）に持ち上がり、S^♭ → W^♭。G-A6-6（階数 1 の付値環の
   tilt と untilt：V 完全 d 進完備 ⇒ V^♯ = W(V)/d は p 完備階数 1 付値環で (V^♯)^♭ = V；W perfectoid 階数 1 付値環 ⇒ W^♭ も）。
3. **黒箱 G-A6-1**：完全 F_p 代数の arc 被覆 A → B について 0 → A → B → B ⊗_A B → ⋯ は完全（[BS17, Thm 4.1] の v 降下、[BM18, Thm 1.6] の
   arc 降下の判定、[BS17, Lemma 6.3] の付値環の性質）。A = R^♭、B = S^♭ × R^♭[1/d] に適用。
4. 導来 d 進完備化：完備化は完全関手で R^♭[1/d] を含む項の完備化は零。よって 0 → R^♭ → S^♭ → S^♭ ⊗̂ S^♭ → ⋯ が完全（G-A6-7：
   Čech 複体の完備化と、B ⊗_A B の各項の分解で R^♭[1/d] が混じる項の消え方。紙 2）。

### 3.2 Cor 8.12

原典 p.69 を affPerfd_κ の上で追う。S′ は与えられたもの、S″ := S′ × S/I。
1. S → S″ は arc 被覆（S → V が I を殺せば S/I を通り、殺さなければ `ArcOutside` で S′ → V に延びる。W = V でよい）。
2. perfd は有限積を保つ（G-A6-2）：Prop 8.5 の極限の形で Perfd_{(S′ × S/I)/} ≅ Perfd_{S′/} × Perfd_{(S/I)/}（冪等元で分解、perfectoid の
   因子は perfectoid）、積圏上の T′ × T″ の極限は極限の積。よって S″ の四角形（S → S″、I）が引き戻しなら S′ の四角形も引き戻し
   （S″/IS″ = S′/IS′ × S/I で、S″ の四角形は S′ の四角形と恒等の四角形 (S/I)_perfd = (S/I)_perfd の積）。以下 S′ := S″。
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
   （Prop 8.5、Type u 版と κ 版の一致）。引き戻しの射が perfd の関手性の射に一致することは紙 4。
6. CAlg_R の引き戻し：U は極限を保ち反映する（G-A5-16）。界面の `IsPullbackSquare` の形へ。

## 4. 必要な一般論（G-A6）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A6-1 | **黒箱**：完全 F_p 代数の arc 被覆の Čech 複体の完全性（[BS17, Thm 4.1]＋[BM18, Thm 1.6]＋[BS17, Lemma 6.3]） | なし | Prop 8.10 |
| G-A6-2 | perfd は有限積を保つ（Prop 8.5 の極限の形、Perfd_{(S′×S″)/} ≅ Perfd_{S′/} × Perfd_{S″/}、perfectoid の因子は perfectoid） | なし | Cor 8.12 の 2 |
| G-A6-3 | p 完備な階数 1 の付値環は perfectoid な p 完備階数 1 付値環に忠実平坦に埋まる（絶対整閉包の p 完備化、付値の延長） | なし（Mathlib の付値の延長、要確認） | Lemma 8.8、§3.1 の 2 |
| G-A6-4 | perfectoid の完備テンソルの tilt：(S ⊗̂_R S′)^♭ = S^♭ ⊗̂_{R^♭} S′^♭（d 進） | `CompletedTensor`、`WittQuotientTilt`（部分） | §3.1 の 1 |
| G-A6-5 | W は完全 F_p 代数の完全列を保つ；mod d は d 正則な項で完全性を保つ | Mathlib `WittVector`（部分） | §3.1 の 1 |
| G-A6-6 | 階数 1 の付値環の tilt・untilt（V 完全 d 進完備 ⇒ W(V)/d は p 完備階数 1 付値環、(V^♯)^♭ = V；perfectoid 付値環の tilt は付値環） | `WittQuotientTilt`（環の部分）、付値は なし | §3.1 の 2 |
| G-A6-7 | 導来 d 進完備化は完全列を保ち、d が可逆な項を殺す；Čech 複体の各項の分解 | HA/DerivedCompletion（2b 後の名前） | §3.1 の 4 |
| G-A6-8 | 基底上の集合の層の延長 F(T) := lim_{Perfd_{T/}} F は arc 被覆で層条件を満たす（1 圏） | Mathlib `Sheaf`（比較補題は要確認） | §3.2 の 3 |
| G-A6-9 | 完備テンソルの arc 被覆（§3.2 の 3 の二つ）と `ArcOutside` からの arc 被覆性 | なし | §3.2 |
| G-A6-10 | S/I・T/IT の導来 p 完備性（I 完備な商） | HA/DerivedCompletion（要確認） | E3 の欄 |
| S8 | §2.4 の 1〜6 | なし（Sheaves/ の続き、∞ トポス） | Cor 8.12 の 4・5 |

## 5. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D53 | arc 位相は p 進形式スキーム fSch の上、Perfd ⊂ fSch | affine（κ-small の perfectoid 環）の上にだけ定義する。原典も Cor 8.11・8.12 で affPerfd（基底）で計算する | fSch は定義しない。E3 の経路は affine で閉じる |
| D54 | arc 被覆は qcqs な一つの射、位相は arc 被覆と開被覆で生成 | [BM18, Def 1.2] の有限族の形で定義（affine では開被覆は有限族に含まれる） | 同じ位相（affine 上） |
| D55 | Cor 8.11：S_perfd = RΓ_arc(Spf S, O)（fSch 上の層コホモロジー）と arc 降下 | 述べない。E3 で使う等式 T_perfd = Γ(F_T, O) = lim_{Perfd_{T/}} O は Prop 8.5。Lemma 8.8 は記録 | 使わない主張を省く |
| D56 | Prop 8.10 の証明は [BS17, Thm 4.1]・[BM18, Thm 1.6]・[BS17, Lemma 6.3] を引用 | 三つを合わせた一つの黒箱 G-A6-1（完全 F_p 代数の arc 被覆の Čech 完全性）。tilt への帰着は証明する | 結晶の黒箱と同列（決定項目 2） |
| D57 | Cor 8.12 の証明は Perfd 上の空間の層 | S8（空間値の層と E 値の層の局所性）を一般論として立てる。集合の層の等式は 1 圏（Mathlib）で | 同じ証明。∞ 側の一般論が一つ増える（決定項目 3） |
| D58 | 「S′ を S′ × S/I に替える」 | perfd が有限積を保つこと（G-A6-2）を Prop 8.5 から示して戻す | 原典が省く一歩を補う |

## 6. 単位と順序

| 単位 | 内容 | 依存 |
| --- | --- | --- |
| A6-1 | arc site（定義、coverage、Lemma 8.8 の affine 版） | 既存の perfectoid、`CompletedTensor`、S1 |
| A6-2 | Prop 8.10（tilt への帰着、黒箱 G-A6-1、Hom の層性） | A6-1、G-A6-4〜7 |
| A6-3 | 集合の層の等式（§3.2 の 1〜4、1 圏）、G-A6-2、G-A6-9 | A6-1、A5 |
| A6-4 | Cor 8.12（S8 を入力に）と E3 の `excision` | A6-2、A6-3、S8、A4-3、A5-1 |

骨組みは A6-1 → A6-3 → A6-2 → A6-4。S8 は Sheaves/ の続きとして drafts/Sheaves/SpaceValued.lean に主張だけ置く（置き場所は調整役）。

## 7. 決定事項（相談）

1. arc site の範囲：affine（κ-small の perfectoid 環）の上にだけ定義し、有限族の形で（D53・D54、推奨）／p 進形式スキームを定義する（範囲外）。
2. Prop 8.10 の外部入力：三つの引用を合わせた一つの黒箱 G-A6-1（完全 F_p 代数の arc 被覆の Čech 完全性）として置き、tilt への帰着は証明する
   （D56、推奨。結晶の黒箱と同列、独立の作業単位）／[BS17, Thm 4.1]・[BM18, Thm 1.6] を証明する（長い。別計画）。
3. Cor 8.12 の層の議論：S8（空間値の層の層化・0 切り捨て・E 値の層の局所性）を ∞ 側の一般論として立て（D57、推奨）、集合の層の等式は Mathlib の
   1 圏の層で証明する／S8 を避けて E 値の Tot で直接「ほどく」— 検討したが見通しが立たない（arc 被覆に沿う Tot の各項をさらに被覆で分解する必要）。
4. Lemma 8.8・Cor 8.11：記録のみ（Lemma 8.8 の affine 版は A5-4 の S̃ から一行、Cor 8.11 は述べない、D55、推奨）／Cor 8.11 も affine の形で述べる。
5. G-A6-3・G-A6-6（付値環の tilt・untilt、絶対整閉包への埋め込み）：A6 の中で主張を置く（推奨）／既存の CLMST の付値の道具（`Prop247*Valuation`）を
   先に確認する。

## 8. 紙で確かめる項目

1. arc 被覆の底変換・合成の安定性（W の取り方）、有限族と単射 R → ∏ R_i の同値。
2. §3.1 の 4：R^♭[1/d] を含む項の完備化が消えること、Čech 複体の項の分解と完備化の交換。
3. §3.1 の 2：V を完全にとってよいこと、d 進完備化しても付値環であること、untilt の付値環性（G-A6-6）。
4. §3.2 の 5：引き戻しの射が perfd の関手性の射（S → S′ など）の像に一致すること。
5. §3.2 の 3：延長 F(T) の層条件（G-A6-8）と、二つの arc 被覆の確認。
6. G-A6-2：perfectoid の因子 eT が perfectoid であること、Perfd_{(S′×S″)/} の分解。
