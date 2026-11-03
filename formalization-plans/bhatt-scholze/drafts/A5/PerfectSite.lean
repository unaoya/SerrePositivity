-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectSite（仮。原典 Rem 4.6、Lemma 4.8、比較写像）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.1・§2.2、単位 A5-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.PerfectPrismHomLift
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/A0/PrismaticSite.lean（`PerfectPrismaticSite`、`flatTopology`、`structurePresheafDerived`）、drafts/Sheaves/{SheafCondition,GlobalSections,CechConerveLimit,CAlgValued}.lean、
-- drafts/A3/DiscreteCase.lean（`prismMapOfDiscrete`）、drafts/A4/Perfectoidization.lean、drafts/A7/AnimatedDomain.lean を import する。
-- W9-III-09：Prop 8.5 の証明・系（PerfectSiteComparison）は A5-2〜A5-4 の後。本ファイルは A5-2（SemiperfectoidCase）より先に置く定義だけ。

/-!
# 完全 prismatic site と比較写像（BS 著者版 Rem 4.6、Lemma 4.8、Lemma 7.7(3) からの比較写像）

## 概要
完全 prism (A,(d))（R = A/d perfectoid）と導来 p 完備な animated R 代数 S（D45 改訂。本ファイルの `S : Type u` は離散の特別な場合）に対し、
完全 prismatic site (S/A)^perf_Δ = (π_0 S/A)^perf_Δ（A0 の `PerfectPrismaticSite` に flat 位相）、Lemma 4.8 の系（site ≃ perfectoid 環への写像 S → T の圏、
濃度 ≤ κ）、比較写像 Δ_{S/A,perf} → lim_{(S/A)^perf} O_Δ（脚 f_n = φ_B^{-n} ∘ f、W9-II-07）。

## 方針
A5/PerfectSiteComparison.lean から W9-III-09 で切り出した。SemiperfectoidCase（A5-2）が比較写像の脚を使い、Prop 8.5 の証明は A5-2〜A5-4 を使うので、
定義を先行ファイルに分ける。

## 規約
位相の順序は ⊥ ≤ J ≤ flat（D46）。κ = `cutoff`（A0）。値は CAlg_A・CAlg_R。

## 使われ方
A5-2（`perfectoidizationToUniversal`）、A5-3・A5-4、A5-1 の Prop 8.5（PerfectSiteComparison）、E3 の `limitCone`（InterfaceLimitCone）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## Rem 4.6：完全 prismatic site -/

/-- 概要：(S/A)^perf_Δ：A0 の `PerfectPrismaticSite (perfectPrism p R) S κ`（完全 prism の充満部分圏の opposite）。
方針：A0 の定義をそのまま使う（要確認：A0 の `PrismOver` の R は A/d 代数として与える。ここでは R = A/d で S は R 代数）。
規約：κ = `cutoff`。
使われ方：以下すべて。 -/
abbrev perfectSite : Type u := PerfectPrismaticSite (perfectPrism p R) S (cutoff (perfectPrismRing p R) S)

/-- 概要：完全 site の flat 位相：完全 prism の間の忠実平坦な単射の生成 sieve を含む位相の sInf（A0 の `flatTopology` と同じ形）。
方針：`IsFaithfullyFlat` を完全な対象に制限して sInf。
規約：包含関手による引き戻し位相との一致は述べない。
使われ方：Prop 8.5 の位相の上限。 -/
def perfectFlatTopology : GrothendieckTopology (perfectSite p R S) := sorry

/-- 概要：完全 site の各対象に Čech 余脈体がある：**Perfd_{S/} の余積 (T₁ ⊗̂_S T₂)_perfd**（Cor 7.3 の普遍 perfectoid 環の普遍性、A5-4 `perfUnder_cechNerveData`）を
Lemma 4.8 の圏同値 `perfectSiteEquivPerfectoidUnder` で完全 site に運ぶ。
方針：W9-II-06 で訂正：A 上の完備テンソル B ⊗̂_A B′ では S の二つの構造射が一致せず（S = F_p[t]、T = F_p[t^{1/p^∞}] で反例）、S3 に渡すと極限が変わる。
flat 被覆の相対 Čech 項 B₁ ⊗̂_{B₀} B₁（G-A5-5 の層性に使う）とは別物。
規約：S3 の `CechNerveData`。
使われ方：弱始対象から極限（`perfectoidization_isLimit`）。 -/
def perfectSite_cechNerveData (U : perfectSite p R S) : True := trivial

/-- 概要：構造前層 O_Δ の完全 site への制限（D(A) 値、CAlg_A 値）。
方針：A0 の `structurePresheafDerived` を包含関手で引き戻す。
規約：—
使われ方：比較写像の終域。 -/
def perfectStructurePresheaf : True := trivial

/-- 概要：G-A5-5：O_Δ は完全 site で flat 層（Čech 層）。
方針：A0-3d（Cor 3.12 の層性）の制限。完全 site の Čech 余脈体は大きい site のものと同じ。
規約：D-S1（Čech 層）。
使われ方：位相非依存（`perfectionComparison_isIso_topology`）。 -/
theorem perfectStructurePresheaf_isSheaf : True := by trivial

/-! ## Lemma 4.8 と site の記述 -/

/-- 概要：Lemma 4.8：完全 prism (A,I) と任意の prism (B,J) で、環の射 A/I → B/J は prism の射 (A,I) → (B,J) に一意に持ち上がる。
方針：既存 `Prism/PerfectPrismHomLift` を確認して使う（要確認：名前と形）。
規約：—
使われ方：`perfectSiteEquivPerfectoidUnder` の Hom の全単射。 -/
theorem perfectPrism_hom_lift_unique : True := by trivial

/-- 概要：Lemma 4.8 の系：関手 (B,J) ↦ B/J は (S/A)^perf_Δ（の opposite）から「S → T、T perfectoid、濃度 ≤ κ」の圏への圏同値。
方針：Hom は Lemma 4.8 を (A,I) := (B,J) に、本質的全射は Thm 3.10（`exists_perfectoidTrialPrism`）。
規約：濃度 ≤ κ の `PerfUnder_u p S` の充満部分圏を `PerfUnderSmall` と書く（要確認：`SmallModel` の使い方）。
使われ方：系 1・系 2、E3 の錐の添字の移送。 -/
def perfectSiteEquivPerfectoidUnder : True := trivial

/-! ## 比較写像 -/

/-- 概要：完全 (B,J) ∈ (S/A)^perf に対する Δ_{S/A,perf} → B：Lemma 7.7(3) の A 線形・Frobenius 両立の f : Δ_{S/A} → B（A3 `prismMapOfDiscrete`）から、
塔（φ_{A*}^n、A4）の第 n 項への脚 f_n := φ_B^{-n} ∘ f : Res_{φ_A}^n Δ_S → B（W9-II-07）、余極限から colim → B、B が (p,d) 完備なので完備化から。
方針：f_n(φ_A^n(a) x) = a f_n(x) で A 線形、f_{n+1} ∘ φ = f_n で塔と整合、B について自然（B 間の射は φ_B とその逆に可換）。
規約：CAlg_A の射。
使われ方：錐。 -/
def perfectionLeg (B : perfectSite p R S) : True := trivial

/-- 概要：比較写像 Δ_{S/A,perf} → lim_{(S/A)^perf} O_Δ（CAlg_A）。
方針：`perfectionLeg` の自然性で O 上の錐、極限の普遍性。
規約：終域は chaotic の RΓ = lim（S2 の `globalSections`）。
使われ方：Prop 8.5。 -/
def perfectionComparison : True := trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
