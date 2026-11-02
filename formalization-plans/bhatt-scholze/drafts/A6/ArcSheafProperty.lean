-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSheafProperty（仮。原典 Prop 8.10 の affine 版と三つの引用）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.2・§3.1、単位 A6-2。基準コミット 972bb7f53。ビルドしない。
-- 引用 3 件の `sorry` 定理（G-A6-1a・1b・1c）は drafts/ の間は問題なし。SerrePositivity/ に入れるときは scripts/make_area_audits.py の許可一覧の更新を調整役に依頼する（main 7b8b96286）。
module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTilt
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
-- 本ファイルは drafts/A6/ArcSite.lean、drafts/Sheaves/{SheafCondition,CAlgValued}.lean、drafts/A0/PrismaticSite.lean（`ringPresheafToCAlg`）を import する。

/-!
# 構造層の arc 層性（BS 著者版 Prop 8.10 の affine 版）と三つの引用

## 概要
O : R ↦ R（**CAlg_ℤ 値**。W9-II-22：global な affPerfd_κ の対象には固定 R からの射がないので CAlg_R 値にはできない。F_U の元の圏 Perfd_{U/} の上で
R → U → T により CAlg_R 値に持ち上げ、極限・引き戻しは忘却 CAlg_R → CAlg_ℤ が作る）は affPerfd_κ 上の arc 層（Čech 層、D-S1）。affine T について Hom(T, −) は集合の arc 層。
原典の証明を追う：単射 arc 被覆 R → S の完備 Čech 複体の完全性に帰着し、tilt で完全 F_p 代数の d 進完備 Čech 複体に移し、
完全 F_p 代数の arc 被覆の Čech 完全性（G-A6-1）を使う。G-A6-1 は三つの引用 [BS17, Thm 4.1 (i)]・[BM18, Thm 1.7]・[BS17, Lemma 6.2/6.3] から
導く。三つは原典が引用している形で述べ、`sorry`（決定 2）。1c は初等的なので後で証明する。

## 方針
tilt の段：R = W(R^♭)/d、S ⊗̂_R S = W(S^♭ ⊗̂_{R^♭} S^♭)/d（G-A6-4）。余単体的な完全環に levelwise の W_n を当て、V の短完全列で Čech 複体の完全性を帰納、
Rlim で W へ、各 Witt 環で正則な d の cofiber で mod d へ（G-A6-5。W9-II-20：正則なのは W(B) 上の d で、tilt 上の a := d mod p は零になり得る）。
{R^♭ → S^♭, R^♭ → R^♭[1/a]} は完全 F_p 代数の arc 被覆族（付値環の tilt・untilt、G-A6-6。階数 0・a = 0 の分岐込み、W9-II-21）。導来 a 進完備化で R^♭[1/a] の項を消す（G-A6-7）。

## 規約
v 被覆は [BS17, Def 2.1]（任意の付値環）、arc 被覆は [BM18, Def 1.2]（階数 ≤ 1 の付値環）の affine・有限族の形。引用は affine 版（D59）。

## 使われ方
Cor 8.11 の affine 版（記録）、Cor 8.12（A6-4：O と F_T の層性）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

variable (p : ℕ) [Fact p.Prime] (κ : Cardinal.{u})

/-! ## 三つの引用（`sorry`） -/

/-- 概要：[BS17, Def 2.1] の affine 版：F_p 代数の有限族 {A → B_i} が v 被覆 ⇔ 任意の付値環 V と A → V に対し、或る i と付値環の拡大 V ↪ W と B_i → W。
方針：定義。
規約：V は任意の階数。
使われ方：G-A6-1a・1b。 -/
def IsVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) : Prop := sorry

/-- 概要：[BM18, Def 1.2] の affine 版（標数 p、p 完備性なし）：階数 ≤ 1 の付値環で同様。
方針：定義。`IsArcCoverFamily`（p 完備版）とは試験対象が違う。
規約：—
使われ方：G-A6-1b・G-A6-1。 -/
def IsArcCoverFamilyCharP {A : Type u} [CommRing A] {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) : Prop := sorry

/-- 概要：**G-A6-1a**［引用、`sorry`］[BS17, Thm 4.1 (i)]（n = 1、E = O）：完全 F_p 代数 A と**完全** F_p 代数 B_i への v 被覆族 {A → B_i} について
A = RΓ_v(Spec A, O)、すなわち 0 → A → ∏B_i → ∏B_i ⊗_A B_j → ⋯ が完全（W9-II-18：被覆と Čech の各項は完全スキームの圏で取る。適用先
B = S^♭ × R^♭[1/d] は完全）。
方針：引用（v 降下、完全スキーム）。
規約：affine・有限族（D59）。
使われ方：G-A6-1。 -/
theorem cech_exact_of_vCover_perfect {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i) (hf : IsVCoverFamily B f) : True := by
  sorry -- [BS17, Thm 4.1 (i)]

/-- 概要：**G-A6-1b**［引用、`sorry`］[BM18, Thm 1.7]（BS の引用では Thm 1.6）の affine 版：finitary（filtered 余極限と可換）な**共変**関手
F : Ring_{F_p} → D(ℤ)^{≥0}（W9-II-17：環の圏の上では共変、値は cohomological に coconnective：H^i = 0 for i < 0。適用する A ↦ A_perf は環に共変）
について、F が arc 層 ⇔ F が v 層かつ、分数体が代数閉な任意の付値環 V と素イデアル 𝔭 ⊂ V について
F(V) → F(V/𝔭)、F(V_𝔭) → F(κ(𝔭)) の四角形が cartesian。使うのは ⇐。
方針：引用。
規約：D(ℤ)^{≥0} は `derivedInfinityCategory ℤ` の coconnective 部分（`IsCoconnectiveAt 0`）。層条件は有限族の Čech（D-S1）。
affine 版（D59）の根拠：v 層は有限 affine 開被覆の降下を満たすので affine の値から qcqs へ延長でき、finitary 性は有限段の降下と一様に coconnective な
Tot の filtered 余極限との交換（BM18 v4 p.4 Thm 1.7、p.17 Ex 3.6(1)、p.25 Thm 4.1）。
使われ方：G-A6-1。 -/
theorem arcSheaf_of_vSheaf_of_valuationSquares : True := by
  sorry -- [BM18, Thm 1.7]

/-- 概要：初等補題（引用ではない、W9-II-18）：任意の付値環 V と素イデアル 𝔭 について 0 → V → V_𝔭 ⊕ V/𝔭 → κ(𝔭) → 0 が完全、すなわち
V → V_𝔭、V → V/𝔭、→ κ(𝔭) の四角形は環の圏で cartesian（V = V_𝔭 ×_{κ(𝔭)} V/𝔭）かつ cocartesian。
方針：𝔭V_𝔭 = 𝔭（a ∈ 𝔭、s ∉ 𝔭 で a/s ∉ V なら付値環性で s/a ∈ V、s = a·(s/a) ∈ 𝔭 で矛盾；a/s ∈ V なら素性で a/s ∈ 𝔭）。よって V_𝔭/𝔭V_𝔭 = κ(𝔭) で
V → V_𝔭 と V → V/𝔭 の核が一致し短完全列、右の射は差で V_𝔭 → κ(𝔭) は全射。cocartesian は局所化と商の可換性。加群の導来圏でも cartesian。
規約：—
使われ方：`valuationRing_milnorSquare_perfect`。 -/
theorem valuationRing_milnorSquare {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (𝔭 : Ideal V) [𝔭.IsPrime] : True := by
  sorry -- 初等的。中身の段階で証明

/-- 概要：**G-A6-1c**［引用、`sorry`、上の初等補題の特殊化として後で証明］[BS17, Lemma 6.3]（Lemma 6.2 は付値環による v 被覆の主張で、この四角形
ではない。W9-II-18）：**完全**付値環 V（標数 p）と素イデアル 𝔭 について 0 → V → V_𝔭 ⊕ V/𝔭 → κ(𝔭) → 0 が完全。
方針：原典の形で引用。適用先（分数体が代数閉な標数 p の付値環）は完全なのでこの特殊化で足りる。
規約：「完全」の仮定を落とした一般版を引用そのものとは記さない。
使われ方：G-A6-1（F = O_perf の四角形）。 -/
theorem valuationRing_milnorSquare_perfect {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CharP V p] [PerfectRing V p]
    (𝔭 : Ideal V) [𝔭.IsPrime] : True := by
  sorry -- [BS17, Lemma 6.3]

/-- 概要：G-A6-1：完全 F_p 代数の有限族の arc 被覆 {A → B_i} について 0 → A → ∏B_i → ∏B_i ⊗_A B_j → ⋯ が完全。
方針：F := (A ↦ A_perf) は F_p 代数上の finitary な関手。1a を完全化に当てて v 層（完全化は v 被覆を保つ）。分数体が代数閉な付値環は完全なので
四角形は 1c の Milnor 四角形（`valuationRing_milnorSquare_perfect`）で cartesian。1b（共変、D(ℤ)^{≥0} 値）で arc 層。arc 層で F(A) 離散なら Tot = Čech 複体の完全性。
規約：—
使われ方：Prop 8.10。 -/
theorem cech_exact_of_arcCover_perfect {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p] : True := by trivial

/-! ## tilt への帰着 -/

/-- 概要：G-A6-4：perfectoid の完備テンソルの tilt：(S ⊗̂_R S′)^♭ ≅ S^♭ ⊗̂_{R^♭} S′^♭（d 進完備）。
方針：既存の `CompletedTensor`・`WittQuotientTilt`。
規約：—
使われ方：Čech 複体の tilt。 -/
theorem completedTensor_tilt : True := by trivial

/-- 概要：G-A6-5（W9-II-20 で訂正）：augmented 余単体的な完全 F_p 代数 B^• の Čech 複体が完全なら、W(B^•) の Čech 複体も完全で、W(B^•)/d（d は各 W(B^k) で
正則な distinguished 元）の Čech 複体も完全。正則なのは Witt 環上の d であって tilt 上の d mod p ではない（R が標数 p なら d = p、像は 0）。
方針：levelwise に W_n、加法群の短完全列 0 → W_{n−1}(B^•) → W_n(B^•) → B^• → 0（V）で帰納、遷移 W_n → W_{n−1} は項ごとに全射なので Rlim = lim（Mittag-Leffler）、
d の cofiber は d 正則なので通常の商の複体。Mathlib `WittVector` の `verschiebung`・`truncate` の API。「W を交代和微分に直接当てる」のではない。
規約：—
使われ方：Čech 複体の tilt。 -/
theorem witt_exact_of_perfect : True := by trivial
theorem modD_exact_of_regular : True := by trivial

/-- 概要：G-A6-6：階数 1 の付値環の tilt・untilt：V が完全で a 進完備（a := d mod p）な階数 1 の付値環（R^♭ 上）なら V^♯ := W(V)/d は p 完備な階数 1 の付値環で
(V^♯)^♭ = V（a = 0 なら d は W(V) で p の単元倍、V^♯ = V）；W が perfectoid な p 完備階数 1 の付値環なら W^♭ は完全な階数 1 の付値環。
方針：既存 `WittQuotientTilt`（環の部分）＋付値の対応。付値環性（W9 続き 6）：U = W(V)/d は局所・被約・p ねじれなし、非零元を p 冪で割って mod p 非零にし、
Teichmüller の像で x = b^♯ + ϖc、V の可除性の全順序で x = b^♯(1 + (ϖ^♭/b)^♯c) と単元倍の sharp に書ける。[Česnavičius–Scholze, Purity for flat cohomology,
Prop 2.1.9] の証明と同じ（証明の参照。第四の黒箱ではない）。
規約：—
使われ方：§3.1 の 2。 -/
theorem untilt_rankOneValuationRing : True := by trivial
theorem tilt_rankOneValuationRing : True := by trivial

/-- 概要：{R^♭ → S^♭, R^♭ → R^♭[1/a]}（a := d mod p）は完全 F_p 代数の arc 被覆族（`IsArcCoverFamilyCharP`、階数 ≤ 1 で試す。R → S が perfectoid の arc 被覆のとき）。
方針（W9-II-21 で分岐を補記）：R^♭ → V。V → V_perf は整・局所・単射で忠実平坦なので V は完全としてよい。(i) a が単元なら第二成分。(ii) V 階数 1、a 非零非単元なら
a 進完備化 V̂（階数 1・完全、V → V̂ 忠実平坦）、untilt V̂^♯ へ R → V̂^♯。(iii) V 階数 1、a = 0 なら V^♯ = V。(iv) V 階数 0（完全体 k）、a 非単元なら a = 0、
V₁ := k[t^{1/p^∞}]_{(t^{1/p^∞})} の t 進完備化（完全・階数 1、k → V₁ 忠実平坦）へ移って (iii)。R → V̂^♯ に仮定を当て、perfectoid な W に拡大（G-A6-3）、
S → W、V̂ → W^♭ は局所単射で忠実平坦、S^♭ → W^♭。
規約：—
使われ方：Prop 8.10。 -/
theorem tilt_arcCoverFamily : True := by trivial

/-- 概要：G-A6-7：導来 a 進完備化（a := d mod p）は完全列を保ち、a が可逆な項を殺す；Čech 複体 of {R^♭ → S^♭, R^♭ → R^♭[1/a]} の各項の分解で R^♭[1/a] が混じる項の完備化は零。
方針：HA/DerivedCompletion（2b 後の名前）。
規約：—
使われ方：Prop 8.10。 -/
theorem cech_completion_kills_inverted : True := by trivial

/-! ## Prop 8.10 -/

/-- 概要：Prop 8.10 前半（affine）：単射 arc 被覆 R → S（perfectoid）の完備 Čech 複体 0 → R → S → S ⊗̂_R S → ⋯ は完全。
方針：tilt（G-A6-4・5）、`tilt_arcCoverFamily`、`cech_exact_of_arcCover_perfect`、`cech_completion_kills_inverted`。
規約：—
使われ方：`structurePresheaf_isArcSheaf`。 -/
theorem cech_exact_of_arcCover_perfectoid : True := by trivial

/-- 概要：Prop 8.10 前半：O（CAlg_ℤ 値、R ↦ R。W9-II-22）は affPerfd_κ 上の arc 層（Čech 層、D-S1）。
方針：S1 の生成系の補題と `isSheaf_arc_iff_cech`、有限族を R → ∏R_i に置き換え、`cech_exact_of_arcCover_perfectoid`（離散な余単体的環の Tot は Čech 複体）。
規約：`IsSheaf (arcTopologyPerfd p κ) (structurePresheaf …)`。
使われ方：Cor 8.11 の affine 版、Cor 8.12。 -/
theorem structurePresheaf_isArcSheaf : True := by trivial

/-- 概要：Prop 8.10 後半（affine T）：R ↦ Hom(T, R) は affPerfd_κ 上の集合の arc 層。
方針：H⁰ の等化子 R = eq(S ⇉ S ⊗̂_R S) に Hom(T, −) を当てる。
規約：Mathlib の `Presheaf.IsSheaf`（集合値）。
使われ方：Cor 8.12 の F_T。 -/
theorem homPresheaf_isArcSheaf (T : Type u) [CommRing T] : True := by trivial

/-- 概要：Cor 8.11 の affine 版（記録、D55）：S_perfd ≃ RΓ_arc(affPerfd_κ/S, O)（slice site の上の β の RΓ）。
方針：O は層なので RΓ = lim（S2）、lim_{Perfd_{S/}} O = S_perfd（Prop 8.5、A5）。
規約：fSch・affCompl_κ 上の RΓ との比較はしない。
使われ方：記録。 -/
theorem perfectoidization_eq_arcCohomology : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
