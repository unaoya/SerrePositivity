# ∞ 層の一般論の設計（BS 発、2026-11-02）

概要：BS の A0（prismatic site、原典 §4）・A5（完全 prismatic site、Prop 8.5）・A6（arc 位相、Prop 8.10〜Cor 8.12）で、原典の
「RΓ(site, O)」を定義のまま形式化するために要る、D(A) 値前層の ∞ 層の理論の**最小範囲**を定める。層条件、層化、大域切断 Γ、
RΓ、弱終対象の Čech 脈体による計算（原典 §4.3 脚注 10）、基数による切り落とし。
方針：HTT §6.2.2（site 上の層）と §5.5.4（presentable 圏の局所化）の定義をそのまま使う。値の圏は安定で presentable な ∞ 圏 E
（使うのは D(A)）に限り、E の安定性で済む議論（左完全性）は HTT の空間値の議論を繰り返さない。既存の ∞ 基盤（F2/Presentable の
accessible・反射、Core/Limit の錐、HomotopyLimits）の上に載せ、1 圏の位相データ（篩・被覆）は Mathlib の `GrothendieckTopology` を使う。
規約：本書は BS セッションが書く設計書で、置き場所（InfinityCategories のどの層か）と実装の時期は調整役が決める
（infinity-foundation-plan.md 段 G の M12、coordination.md §1）。Lean の骨組みは `drafts/` に置き、ビルドしない。
決定は [[D-S 番号]] で記す。原典は BS 著者版（`paper/refs/BS-prisms-author.pdf`）、HTT は Lurie, *Higher Topos Theory*、
HA は *Higher Algebra*、SAG は *Spectral Algebraic Geometry*。
使われ方：A0 の設計書（`a0-design.md`、Not 4.16・Constr 4.18）、A5・A6 の設計書が本書の定義を前提にする。
調整役は §9 の置き場所の案と §4 の前提の表を見て窓を決める。

## 0. なぜ要るか（決定の記録）

- 2026-11-02 ユーザー決定：BS の形式化は**定義を原典のまま**入れ、定理だけ特別な場合に絞る（memory `bs-faithful-definitions`）。
  原典 Not 4.16 は Δ_{R/A} := RΓ((R/A)_Δ, O_Δ) で、RΓ は site 上の層係数コホモロジー。Construction 7.6・Def 8.2 はこれを
  「(p,I) 完備な D(A) の可換代数対象」として使うので、RΓ は ∞ 圏的（D(A) に値をとり、乗法構造が載る形）でなければならない。
- 同日決定（U2 の β 案）：D(A) 値前層の**層化**を作り、すべての前層に RΓ(J, F) := Γ(F^♯) を定義する。
  「層である前層にだけ RΓ := lim F と定義する」γ 案は採らない。
- 同日決定（II-a）：大きい site は基数 κ で切り落とした小さい site に取り替える。宇宙は上げない（§5）。
- 1 圏的な層係数コホモロジー（Mathlib の `Sheaf.H`、Ext による定義）は、乗法構造が載らず、値が基盤の D(A) でなく、
  Čech–Alexander 複体との比較に Cartan–Leray が要る（Mathlib にない）ので採らない。

## 1. 数学の定義（HTT との対応）

以下、𝒞 は小さい圏、J は 𝒞 上の Grothendieck 位相、E は安定で presentable な ∞ 圏（小極限・小余極限をもつ）。

| 記号 | 定義 | HTT |
| --- | --- | --- |
| PSh_E(𝒞) | 関手 ∞ 圏 Fun(N(𝒞)^op, E) | 1.2.7.3 |
| 層条件 | F ∈ PSh_E(𝒞) が J 層 ⇔ すべての U ∈ 𝒞 と U の被覆篩 S について、錐 F(U) → (F の S 上の制限) が極限錐。S 上の制限とは、S の射 (V → U) を対象とする圏（Over U の充満部分圏）上の図式 (V → U) ↦ F(V) | 6.2.2.6（空間値）。E 値は SAG 1.3.1.? の形 |
| Shv_E(𝒞, J) | 層のなす充満部分 ∞ 圏 | 6.2.2.6 |
| 層化 (−)^♯ | 包含 Shv_E ↪ PSh_E の左随伴 | 6.2.2.7、5.5.4.15 |
| Γ | Γ(F) := lim_{N(𝒞)^op} F（E の対象。必要なら Map_E(M, Γ F) ≃ Map_PSh(const M, F) と読む。「終対象への Map」とは言わない：安定圏値では終対象は零、W9-I-07） | 6.3.4.? の大域切断 |
| RΓ(J, F) | Γ(F^♯) | — |

層化の存在（HTT の議論を E 値に書き直したもの）：
1. PSh_E(𝒞) は presentable（HTT 5.5.3.6：𝒞 が小さく E が presentable なら Fun(N(𝒞)^op, E) は presentable）。
2. E の生成元の小さい集合 G（D(A) なら A の shift {A[n] | n ∈ ℤ}）をとる。前層 X ∈ PSh_{Spaces}(𝒞)（特に表現可能 h_U と篩 S ⊆ h_U）と
   M ∈ E に対し X ⊗ M ∈ PSh_E(𝒞) を V ↦ (X(V) 個の M の余積) で定める。Yoneda と随伴から
   Map(X ⊗ M, F) ≃ Map_E(M, lim_{el(X)} F)（el(X) は X の元の圏）。
3. W := { S ⊗ M → h_U ⊗ M | U ∈ 𝒞、S は U の被覆篩、M ∈ G } は小さい集合。E が安定で G が生成系なので、
   F が W 局所 ⇔ すべての (U, S) で F(U) → lim_S F が同値 ⇔ F は J 層。
4. HTT 5.5.4.15：presentable ∞ 圏の、小さい集合 W に関する局所対象の充満部分圏は accessible な反射的部分圏。反射が層化。
5. 左完全性（HTT 6.2.2.7）は、E が安定なら別に示す必要がない：Shv_E は極限と shift で閉じた安定充満部分圏で、
   層化は左随伴なので余極限を保ち、安定 ∞ 圏の間の有限余極限を保つ関手は完全（HA 1.1.4.1）。

弱終対象による計算（原典 §4.3 脚注 10 の前層版）：
𝒟 を圏、U を弱終対象（任意の V から U へ射がある）とし、**単体的対象 U_• と、各 n について U_n を U の (n+1) 個の積として示す錐のデータ**
（prism の圏では余積。𝒟 に一般の有限積があることは仮定しない：(R/A)_Δ の一般の余積は一般の Prop 3.13 を要するので存在が保証されない。
2026-11-02 決定）が与えられたとする。E に小極限があれば、任意の F ∈ PSh_E(𝒟) について
lim_{N(𝒟)^op} F ≃ Tot F(U_•)（右辺は余単体的対象 [n] ↦ F(U_n) の Δ 上の極限）。複体で計算するときは Tot を Mathlib の
`alternatingCofaceMapComplex`（非正規化）で表し、D(A) の Δ 上の極限との一致は G10（11-02 決定）。
証明の筋：PSh_{Spaces}(𝒟) で h_U → 1 は効果的エピ（各点で π₀ 全射）なので 1 ≃ |h_U^{×(•+1)}|（HTT 6.2.3.5 の系。空間では
π₀ 全射の Čech 脈体の幾何学的実現）。h_U^{×n} = h_{U^n}。F との対（X ↦ lim_{el(X)} F）は余極限を極限に送り（§1 の 2 の
Map(X ⊗ M, F) の形から）、Yoneda で ⟨h_V, F⟩ = F(V)。よって lim F = ⟨1, F⟩ = Tot ⟨h_{U^{•+1}}, F⟩ = Tot F(U^{•+1})。
別経路：E の対象を複体で表し、Bousfield–Kan の余単体的置換と双余単体的対象の extra degeneracy で鎖ホモトピー同値を直接作る
（Stacks 07JM の前層の場合の証明）。どちらを採るかは実装の設計で決める（§8）。

原典の Construction 4.18・Prop 8.5 はこの補題に Cor 3.12（O_Δ が層で、Čech 脈体の各項で高次コホモロジーが消える）を合わせて
RΓ を計算している。β では RΓ(J, O_Δ) = Γ(O_Δ^♯) = Γ(O_Δ)（層なので）= Tot O_Δ(C^•)（補題）となる。Cor 3.12 は β でも要る。

## 2. Čech 層と hypersheaf（[[D-S1]]、2026-11-02 決定：案 1。ずれは §2.1 に記録）

HTT 6.2.2.6 の層（被覆篩に沿う降下）と、hypercomplete な層（HTT 6.5.2、hypercover に沿う降下）は一般に異なる。
古典的な導来関手としての層係数コホモロジーは hypercomplete 版に対応する（SAG 2.1.2.3：アーベル層の導来圏 ≃ hypercomplete な
D(Ab) 値層。1 圏の層 F を D 値前層とみなして hypersheaf 化すると F^{hyp}(U) = RΓ(U, F)）。原典 Def 4.1 は 1 topos の Shv と
古典的な RΓ で書かれている。

- 案 1（**採用**）：HTT 6.2.2.6 の層（Čech 層）で定義する。理由：(a) §8 の arc 位相の議論（Prop 8.10・Cor 8.11）は ∞ 圏的な層の
  言葉で書かれていて、そこで使う「層」はこの意味。(b) hypercompletion は hypercover と ∞ 連結射（層の homotopy 対象と t 構造）の
  理論を別に要する。(c) E3 までに RΓ を当てる前層（O_Δ、Ō_Δ、完全 site の O、arc 位相の O）はすべて離散で、離散な Čech 層は
  hypersheaf である（§2.1）。
- 案 2（不採用）：hypersheafification で定義する。原典の RΓ と文字どおり一致するが、hypercover（Mathlib の `Hypercover` は 1 圏の
  零次・一次まで）と ∞ 連結射による局所化（HTT 6.5.2.8）が追加で要る。将来、非有界な前層に RΓ を当てる必要が出たら再検討する。

### 2.1 ずれの記録（案 1 で原典の RΓ と一致しない範囲）

- **一致する範囲**：Čech 層 F が t 構造の意味で有界（特に各対象で離散）なら、F は hypersheaf である。理由：n 切断された対象は常に
  hypercomplete（HTT 6.5.1 の補題）で、有界な対象は切断の有限回の拡大だから。したがって離散な Čech 層 F については
  Γ(F^♯) = Γ(F) = Γ(F^{hyp}) で、古典的 RΓ と一致する。E3 までに RΓ を当てる前層はすべてこの範囲にある。
- **一致しない範囲**：非有界な前層 F で、site の Postnikov 塔が収束しない場合（無限コホモロジー次元の空間など。Dugger–Hollander–Isaksen
  2004 の、すべての被覆で Čech 降下を満たすが hyperdescent を満たさない前層）。このとき Γ(F^♯) と古典的 RΓ = Γ(F^{hyp}) は異なりうる。
  原典はこの範囲の RΓ を使わない。
- **記録する場所**：(1) 本書 §2・§6 の D-S1。(2) 勉強ノート第 4 章（`exposition/ja/bs/04-site.html`）の「原典との差の評価」に D 番号で。
  (3) Lean の `derivedGlobalSections` の docstring（規約の欄に「Čech 層の大域切断。離散な層では古典的 RΓ と一致（定理名）」）。
  (4) O_Δ について「Čech 層かつ離散 ⇒ hypersheaf、Γ は古典的 RΓ」を定理として A0 に置く（Cor 3.12 の系）。
  (5) 解説（exposition-ja.tex 付録 A）の BS の段落に一文。

## 3. Lean での形（型の案）

名前は仮。宇宙は基盤の約束（小さい形状は `SSet.{u}`、大きい ∞ 圏は `SSet.{u+1}`、`IsPresentable (C : SSet.{u+1})`、
小さい形状は `SSet.uliftFunctor.{u+1, u}` で持ち上げて図式にする）に合わせる。

```lean
-- 位相データは Mathlib。𝒞 : Type u, [SmallCategory 𝒞], J : GrothendieckTopology 𝒞
-- 値の圏 E : SSet.{u+1}, [Quasicategory E], IsStable E, IsPresentable E（D(A) では別に証明）

-- 前層：小さい nerve を持ち上げた図式
abbrev PSh (𝒞) (E) := (SSet.uliftFunctor.{u+1,u}).obj (nerve 𝒞ᵒᵖ) ⟶ E     -- 関手 ∞ 圏としては ihom

-- 篩 S : Sieve U の上の制限図式と、F(U) を頂点とする錐
def sieveDiagram (F : PSh 𝒞 E) (S : Sieve U) : (uliftFunctor.obj (nerve (S の射の圏)ᵒᵖ)) ⟶ E
def sieveCone    (F : PSh 𝒞 E) (S : Sieve U) : JoinCone (sieveDiagram F S)      -- 頂点 F(U)

-- 層条件
def IsInfinitySheaf (J) (F : PSh 𝒞 E) : Prop :=
  ∀ U (S : Sieve U), S ∈ J U → IsLimitCone (sieveCone F S)

-- 層化：W 局所対象の反射（F2/Presentable の IsLocalObject・IsReflectiveSubcategory を使う）
def sheafLocalizingEdges (J) (G : Set (E _⦋0⦌)) : Set ((ihom … E) _⦋1⦌)     -- S ⊗ M → h_U ⊗ M
theorem isInfinitySheaf_iff_isLocalObject : IsInfinitySheaf J F ↔ IsLocalObject (sheafLocalizingEdges J G) F
theorem sheafification_exists : IsReflectiveSubcategory (PSh 𝒞 E) (IsInfinitySheaf J)   -- HTT 5.5.4.15
-- 反射で与えられる F ↦ F^♯ と単位 F → F^♯

-- 大域切断と RΓ
def globalSectionsCone (F : PSh 𝒞 E) : ∃ c : JoinCone F, IsLimitCone c          -- E の小極限から
def derivedGlobalSections (J) (F) : E _⦋0⦌ := (globalSectionsCone (F^♯)).vertex   -- 選んだ極限錐の頂点
-- 普遍性は IsLimitCone で述べ、頂点の等号は主張しない（基盤の規約）

-- 弱終対象の Čech 脈体（§1 の補題）
theorem isLimitCone_of_cechConerve (U : 𝒟) (hU : ∀ V, Nonempty (V ⟶ U)) (hprod : 有限冪の存在)
    (F : PSh 𝒟 E) : IsLimitCone (Tot F(U^{•+1}) から F への錐)
```

- `IsInfinitySheaf` は Mathlib の `Presheaf.IsSheaf`（1 圏）と別物。E 値の離散な前層（環の前層を D(A) に埋めたもの）については、
  1 圏の層条件 ＋「Čech 脈体に沿う導来降下」と同値になることを、Cor 3.12 の形（原典の「層で、高次コホモロジーが消える」）として
  別に示す。
- `derivedGlobalSections` は選択を含む（極限錐を選ぶ）。使う側は頂点の等号でなく `IsLimitCone` の普遍性で扱う。E3 の
  `BSLimitConeData` と同じ規約。
- 乗法構造：E = D(A) では RΓ に代数構造は載らない。A2・A4 の設計で、同じ構成を CAlg_R（EInfinity）値で行い、忘却 U が極限錐を
  保つこと（`FreeProbeDerivedLimits`、証明済み）で D(A) 版と結ぶ。E3 が D(R) 版と CAlg 版の両方を持つのと同じ形。CAlg_R が
  presentable かは未確認（§4）。

## 4. 必要な一般論と現状（2026-11-02 に読んだ範囲）

| # | 項目 | HTT／HA | 現状（InfinityCategories） | 要る段 |
| --- | --- | --- | --- | --- |
| G1 | 関手 ∞ 圏 Fun(K, E) が quasicategory、頂点・辺の評価 | 1.2.7.3 | あり（Core：`ihom`、`functorVertex`、FunctorIso） | 層条件 |
| G2 | presentable 圏の小さい形状の極限 | 5.5.2.4 | あり（`IsPresentable.hasLimit`、F2/Presentable/PresentableSmallLimits） | Γ、層条件 |
| G3 | D(A) が presentable | HA 1.3.5.21 系 | **未**。StablePresentable は空の骨組み。Derived に κ-compact な余積・コンパクト生成の部品あり | すべて |
| G4 | 𝒞 小、E presentable ⇒ Fun(N(𝒞)^op, E) presentable | 5.5.3.6 | **未**（F2/Presentable の FunctorPresheafModel・SmallShapePresentable を確認） | 層化 |
| G5 | 局所置換から反射を作る | 5.5.4.15 後半 | あり（`isReflectiveSubcategory_of_localReplacements`、LocalReplacementReflection） | 層化 |
| G6 | presentable ＋ 小さい W ⇒ 各対象に局所置換がある | 5.5.4.15 前半 | **未**（同ファイルの docstring に「presentable 性からの置換の存在は別工程」） | 層化 |
| G7 | 安定 ∞ 圏の間の左随伴は完全 | HA 1.1.4.1 | Stable に完全関手の定義あり。この形の補題は要確認 | 左完全性（§1 の 5） |
| G8 | X ⊗ M の構成と Map(X ⊗ M, F) ≃ Map_E(M, lim_{el X} F) | 5.1.5、4.2.4 | **未**。F1 に Yoneda・表現可能関手・随伴の Hom 表示はある | 層化（§1 の 2・3） |
| G9 | 空間の π₀ 全射の Čech 脈体の幾何学的実現、または Bousfield–Kan の置換との比較 | 6.2.3.5／Kerodon 7.5 | **未**。HomotopyLimits に Bousfield–Kan の重みと標準比較、Derived に CofinalLimitTransfer・WeaklyContractibleConstantLimit | 脚注 10 |
| G10 | D(A) の Δ 上の極限（Tot）が余鎖複体の全複体で計算される | Dold–Kan の双対 | DoldKanComparison 層（単体的）。余単体的の双対は要確認 | 脚注 10 の応用 |
| G11 | 1 圏の位相データ（篩、被覆、生成される位相、篩の射の圏） | — | Mathlib：`GrothendieckTopology`（完備束）、`Sieve`、`Cover`、`Over` | 層条件 |
| G12 | CAlg_R が presentable、忘却が極限を保つ | HA 3.2.3.1、3.2.2.5 | 忘却の極限保存はあり（`FreeProbeDerivedLimits`）。presentable 性は未確認 | A4 以降 |

G3・G4・G6 が主な不足で、いずれも BS の数学ではなく ∞ 基盤の一般論。G8・G9 は脚注 10 と層化の両方で使う。

## 5. 小ささ：基数による切り落とし（[[D-S2]]、決定済み II-a）

- 原典の site は大きい圏。大きい平坦 site（fpqc 型）では一般の前層の層化が存在しないことがある（Waterhouse 1975）。β はすべての
  前層を層化するので、小さい site で定義する必要がある。
- 処置：A・R : Type u に対し λ := #A + #R + ℵ₀、**κ := λ^{ℵ₀}** とし、site の対象を「台集合の濃度 ≤ κ の prism（Type u）」に限る。
  κ^{ℵ₀} = κ なので、証明で作る対象（R の台集合上の多項式環の完備化、prism の押し出し（完備テンソル）、André 拡大の ω₁ 反復、
  Cor 7.3 の perfectoid 化、§8 の p 冪根の添加）はすべて濃度 ≤ κ で閉じる。各構成でこれを確かめる。
- 濃度 ≤ κ の prism の圏は本質的に小さい（濃度 κ の固定した集合の部分集合を台とする prism の圏と同値）。層化・Γ はこの小さい圏で行う。
- κ はパラメータとして定義に残し、Not 4.16 ではこの既定値を使う。**κ 不変性**（κ₀ ≤ κ ≤ κ′ で RΓ(𝒞_κ, O_Δ) ≃ RΓ(𝒞_{κ′}, O_Δ)）は
  定理：C^0 はどの 𝒞_κ でも弱終対象で、C^• ⊂ 𝒞_{κ₀} なので、§1 の補題と Cor 3.12 から両辺とも Tot O_Δ(C^•)。一般の前層には主張しない。
- E3 の `limitCone` は Type u の perfectoid 標的**全体**を添字にする。A5 では 𝒞_κ で Prop 8.5 を示したうえで、弱終対象 S̃_perfd
  （濃度 ≤ κ）が Type u 全体でも弱終対象であることから、§1 の補題を大きい添字で適用して E3 の形に移す。補題は添字圏の大きさを
  仮定しない形（錐の普遍性）で述べる。
- 宇宙を上げる案（Mathlib の ℓ 進コホモロジーの方式）は採らない：基盤の `derivedInfinityCategory (S : Type u) : SSet.{u+1}` と
  E3 の界面が Type u の加群で閉じているため。

## 6. 原典・HTT との差

| 番号 | 原典・HTT | 本書 | 評価 |
| --- | --- | --- | --- |
| D-S1 | 1 topos の Shv と古典的な RΓ（＝hypercomplete 版） | Čech 層（HTT 6.2.2.6）の層化と Γ（案 1、11-02 決定） | 離散（有界）な Čech 層は hypersheaf なので O_Δ・O・arc の O では一致。非有界な前層では一致しないことがある（§2.1）。原典は使わない |
| D-S2 | 大きい site | 濃度 ≤ κ で切り落とし、κ 不変性は定理 | 原典が省く集合論の処置を補う。内容は変わらない（Waterhouse の例のため β では必須） |
| D-S3 | 値は E∞ 代数（原典 Construction 7.6、Def 8.2） | まず D(A) 値。CAlg 値は A2・A4 で同じ構成を繰り返し、忘却で結ぶ | E3 が二つの版を持つのと同じ |
| D-S4 | 左完全性は空間値の議論（HTT 6.2.2.7） | E の安定性と HA 1.1.4.1 で済ませる | E 値では HTT の議論は不要 |
| D-S5 | 位相は ∞ 圏の site（HTT 6.2.2.1） | 1 圏 𝒞 の Mathlib の位相。nerve で ∞ 圏に | 𝒞 が 1 圏なので同じ |

## 7. A0・A5・A6 での使い方

- **A0 Not 4.16**：(R/A)_Δ^{≤κ} を Def 4.1 の圏（scheme の向き、prism の圏の opposite）に平坦被覆が生成する位相を入れたものとし、
  O_Δ を環の前層、それを D(A) に埋めた前層 F_Δ に対し Δ_{R/A} := derivedGlobalSections(J_flat, F_Δ)、Ō := Δ ⊗^L_A A/I。
- **A0 Cor 3.12**：F_Δ が `IsInfinitySheaf`（1 圏の層条件 ＋ 忠実平坦な Čech 脈体に沿う導来降下から）。
- **A0 Constr 4.18**：C^0 が弱終対象、C^• がその Čech 脈体（余積）、§1 の補題で Δ_{R/A} ≃ Tot O_Δ(C^•)。Rem 4.19 も同じ補題で同じ対象。
- **A5 Prop 8.5**：完全 site (S/A)^perf_Δ（Rem 4.6）上の O について RΓ ≃ lim_{S→R′} R′。弱終対象 S̃_perfd と同じ補題。E3 の
  `limitCone`・`limit_isLimit` へ §5 の手順で移す。
- **A6 Prop 8.10・Cor 8.11・8.12**：Perfd 上の arc 位相の層 O、RΓ_arc、層の引き戻し四角形。層化の完全性（§1 の 5）を使う見込み。

## 8. 単位と順序

| 単位 | 内容 | 前提 |
| --- | --- | --- |
| S1 | 層条件 `IsInfinitySheaf`、篩の制限図式、1 圏の層条件との関係 | G1・G2・G11 |
| S2 | Γ と `derivedGlobalSections` の型（層化は入力として仮定） | G2 |
| S3 | 弱終対象の Čech 脈体の補題（§1）。証明経路（効果的エピ／Bousfield–Kan）の選択 | G8 または G9、G10 |
| S4 | 層化の存在：W の構成、W 局所 ⇔ 層、HTT 5.5.4.15 | G4・G5・G6・G8 |
| S5 | 層化の完全性（E 安定） | G7 |
| S6 | 切り落とし：濃度 ≤ κ の圏の本質的小ささ、κ 不変性の形 | — |
| S7 | D(A) への適用：G3、D(A) の shift が生成系であること | G3 |

S1・S2・S6 は既存の基盤だけで骨組みが書ける。S3・S4 は G6・G8・G9 が要るので、∞ 側の窓との調整が要る。
BS の A0 の Def 4.1・Constr 4.17・4.18（余単体的対象として）、Prop 3.13 の特別な場合、Cor 3.12 は S1〜S3 と並行して進められる。
Not 4.16 の定義は S2 の型が決まれば書け、「Čech–Alexander が Δ を計算する」定理は S3・S4 の後。

## 9. 置き場所（調整役の決定、2026-11-02、main d9254e8b0。infinity-foundation-plan.md の M12 と §3）

- 一般論 S1〜S6：新層 `InfinityCategories/Sheaves/`。層の順序は StablePresentable < Sheaves < ModelBridge（モデル圏・dg を要しないため）。
  最初のファイルを置くときに layers.json に登録する。
- 前提の置き場所：G4・G6 は `F2/Presentable/`、G8 は `F2/` か `HomotopyLimits/`、G9 は `HomotopyLimits/`、G7 は `Stable/`、
  G3 と S7 は `Derived/`（`Derived/Sheaves/`）。BS 固有の site（prism の圏、平坦位相、κ の既定値）は `BhattScholze/`。
  A5 の E3 への接続は `BhattScholze/Perfectoidization/Derived/` の隣。
- 窓：G3・G4・G6 は新しい数学なので段 G（W2b・W2c の外）。開始は W2b が main に入った後（11-05〜06 見込み）、W2c と並行可。
  新しいファイルだけを足し、ビルドは閉包だけ、全ビルドは暦に載せる。担当は W2b の後に決める。
- BS 側：S1・S2・S6 の骨組みを `drafts/` で先に進めてよい。W2b・W2c の改名表は調整役から回る。

## 10. 決定待ち

1. ~~[[D-S1]] Čech 層（案 1）か hypersheaf（案 2）か~~ → 案 1（2026-11-02）。ずれは §2.1 の五か所に記録する。
2. S3 の証明経路（効果的エピの Čech 脈体 ＝ HTT 流、または Bousfield–Kan ＝ Stacks 07JM 流）。基盤の現状では G9 の Bousfield–Kan の
   部品が多いので後者が近いかもしれない。実装の設計で決める。
3. ~~一般論 S1〜S5 の置き場所と、∞ レーンのどの窓に入れるか（調整役）~~ → §9（2026-11-02 決定）。

## 11. 紙で確かめる項目

1. §1 の 3：E が安定で G が生成系のとき「W 局所 ⇔ 層」。生成系の意味（Map(A[n], −) が同値を検出する）を明示する。
2. §1 の 5：Shv_E が PSh_E の安定充満部分圏であること（極限と shift で閉じる）、HA 1.1.4.1 の適用。
3. §1 の補題：⟨X, F⟩ := lim_{el(X)} F が X の余極限を極限に送ること（E 値で）。Yoneda で ⟨h_V, F⟩ = F(V)。
4. §5：各構成（Čech–Alexander、押し出し、André、perfectoid 化、p 冪根）の濃度評価が κ = λ^{ℵ₀} で閉じること。
5. D-S1：O_Δ について Čech 層の RΓ と hypercomplete 版が一致する議論（Čech 脈体の各項での降下 ＋ 弱終対象）。

## 12. Codex レビュー W9（第 1 部、2026-11-02）の反映

- W9-I-02：S3 の形状の射 `cechShape` の始域は持ち上げた N(Δ)（N(Δᵒᵖ) ではない）。骨組みを訂正。
- W9-I-03：`derivedGlobalSections_of_le` は二つの RΓ の頂点の等号ではなく可逆な辺で述べる。骨組みを訂正。
- W9-I-04：S3 は E3 の添字圏 `PerfUnder_u p S`（対象が Type (u+1)）に使うので、「添字圏は大きくてよく Čech 側は小さい」形の版が要る。
  宇宙を対象・射・値で分けて述べる（中身の段階）。κ-small のモデルだけでは A5-4 の `limit_perfUnder_eq_tot` に足りない。
- W9-I-05：CAlg 値の層化と U の両立（単位の U 像が局所同値）は S4 の非安定版の一部として別の主張 `forget_sheafify` に。O_Δ のように既に層の前層は極限保存だけでよい。
- W9-I-07：Γ の説明を訂正（上の表）。
- 紙で確かめた項目：§11 の 1・2・3・5 は W9 で確認済み（○）、4（κ の全構成の評価）は A0 の分だけ確認済み、André の各段と A5 の S̃ は未。

## 13. BS-D1（Codex の下書き作業、2026-11-03）からの追加

- D1-01：S3 の `CechNerveData` を global な site（A6 の affCompl_κ）で使うときは、全 site ではなく被覆 f の生成 sieve の圏 `sieveCategory Q` の中で取る（U = f.op が弱終、
  U の冪は基底上のファイバー積）。S1 の `restriction F Q` がその前層。A0・A5 の site は最初から相対なので区別は不要。
- D1-02：有限族の coverage と一点族の coverage は同じ位相を生成しない（有限積の射影の族が反例）。**S1-E（新しい一般補題、基盤待ち）**：extensive coverage（有限余積の
  射影の族、空族を含む）の層 ⇔ 有限積を保つ（Mathlib `isSheaf_iff_preservesFiniteProducts`、**`FinitaryExtensive`** の ∞ 版、HTT 6.2.2 の系。D5-06（11-03）：`FinitaryPreExtensive`（余積の引き戻し安定性だけ）では偽——二元順序圏 0 < 1 の被覆 {1→1, 1→1} の層条件から F(1) ≃ F(1)² は出ない。余積の非交叉性（`FinitaryExtensive`）が要る。A6 の affine な site では余積＝環の直積で、非交叉性は二つの射影の引き戻しが零環であること（零環は site に含める、D1-03 と同じ扱い））。
  また「位相の ⊔ の層 ⇔ 両方の層」を S1 に明示する。A6 の `isSheaf_arc_iff_cech` はこの二つで一点被覆の Čech 条件に帰着する。
- D3-02（BS-D3、11-03）：S3 の大きい添字圏の版（W9-I-04 で予告）を drafts/Sheaves/CechConerveLimit.lean に `CechNerveDataLarge`・`IsWeaklyTerminalLarge`・
  `isLimitCone_iff_restrict_cech_large` として置いた（𝒟 : Type (u+1)、`[Category.{u} 𝒟]`、四欄は小さい版と同じ）。A5 の `PerfUnder_u p S` はこれを使う。補題の形は大きい圏の
  前層の形状の名前が決まってから。

