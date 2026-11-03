-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectSiteComparison（仮。原典 Prop 8.5 の主張と系。site・Lemma 4.8・比較写像は PerfectSite.lean、W9-III-09）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.1・§2.2・§2.4、単位 A5-1（Lemma 8.6 の主張は A5-3 の予告）。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.PerfectPrismHomLift
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/A5/{PerfectSite,SemiperfectoidCase,WeaklyInitialAndDescent,StrongDescent}.lean（Prop 8.5 の証明 A5-2〜A5-4）、drafts/Sheaves/{GlobalSections,CechConerveLimit}.lean を import する。
-- W9-III-09：site・Lemma 4.8・比較写像（SemiperfectoidCase が使う）は drafts/A5/PerfectSite.lean に切り出し、本ファイルは Prop 8.5 とその系だけ（A5 の最後）。Lemma 8.6 の主張は StrongDescent の `prismaticPerfection_rootMap_descendable'` に一本化。
-- animated 版の定義域 `CompleteAnimatedAlgebra` は drafts/A7/AnimatedDomain.lean（W9-II-24：A5 より先に置く独立ファイル）を import する。

/-!
# 完全 prismatic site と Prop 8.5 の主張（BS 著者版 Rem 4.6、Lemma 4.8、Prop 8.5）

## 概要
完全 prism (A,(d))（R = A/d perfectoid）と導来 p 完備な animated R 代数 S（D45 改訂。本ファイルの `S : Type u` は離散の特別な場合）に対し、
完全 prismatic site (S/A)^perf_Δ = (π_0 S/A)^perf_Δ（A0 の `PerfectPrismaticSite` に flat 位相）、
Lemma 4.8 の系（site ≃ perfectoid 環への写像 S → T の圏、濃度 ≤ κ）、Lemma 7.7(3) の関手的写像からの比較写像
Δ_{S/A,perf} → lim_{(S/A)^perf} O_Δ、Prop 8.5（flat と chaotic の間の任意の位相で同値）とその系（S_perfd ≃ lim_{S→R′} R′ — κ-small の
site でも Type u の `PerfUnder_u` でも、A によらない、semiperfectoid なら Cor 7.3 の perfectoid 化）。

## 方針
位相非依存は O が完全 site で flat 層（G-A5-5、Cor 3.12 の制限）なことと S2（層なら RΓ = lim）で形式的。Type u の添字圏との一致は
弱始対象 S̃_perfd の Čech 余脈体（S3）で、A5-4 の `perfectoidTargetWeaklyInitial` を入力にする。Prop 8.5 本体の証明は A5-2〜A5-4。

## 規約
S は導来 p 完備な animated（D45 改訂、系 4 を含む）。本ファイルの `S : Type u` は離散版で、animated 版は末尾の `perfectionComparison_isIso_animated`・
`perfectoidization_piZero`（定義域の書き換えは中身の段階、W9-II-08）。位相の順序は Grothendieck 位相の ⊥ ≤ J ≤ flat（D46）。κ = `cutoff`（A0）。値は CAlg_A・CAlg_R。

## 使われ方
E3 の `limitCone`・`limit_isLimit`（drafts/A5/InterfaceLimitCone）、Cor 8.11（A6）、Cor 8.14（A7）。
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
-- D45 改訂（2026-11-02、決定 6）：Prop 8.5 の定義域は導来 p 完備な animated R 代数（A7-1 `CompleteAnimatedAlgebra`）。完全 site・Perfd_{S/} は π_0 S で定義する
-- （原典 p.64）。本ファイルの `S : Type u` は離散の特別な場合で、中身の段階で定義域を animated に書き換える（design-status §5）。animated 版の主張は末尾に置く。

/-! ## Prop 8.5 -/

/-- 概要：Prop 8.5（実体）：比較写像は同値。
方針：A5-2（semiperfectoid の場合）、A5-4（弱始対象・filtered 余極限・Lemma 8.6 による降下）。
規約：S 離散。
使われ方：以下の系、E3。 -/
theorem perfectionComparison_isIso : True := by sorry -- A5-2〜A5-4 を待つ

/-- 概要：Prop 8.5（原典の形）：⊥ ≤ J ≤ flat の任意の位相 J で Δ_{S/A,perf} ≃ RΓ_J((S/A)^perf, O_Δ)。
方針：O は flat 層（`perfectStructurePresheaf_isSheaf`）なので J 層（S1 `IsSheaf.of_le`）、S2 で RΓ_J = lim、`perfectionComparison_isIso`。
規約：D46。
使われ方：原典との対応（Cor 8.11 は Prop 8.10 と合わせる）。 -/
theorem perfectionComparison_isIso_topology (J : GrothendieckTopology (perfectSite p R S))
    (hJ : J ≤ perfectFlatTopology p R S) : True := by trivial

/-- 概要：系 1（κ 版）：S_perfd ≃ lim_{(S/A)^perf} Ō_Δ ≃ lim_{S→T, T perfectoid, #T ≤ κ} T（CAlg_R）。
方針：⊗^L_A A/d は cofib(d) で極限と可換（G-A5-9）、完全 prism で B ⊗^L A/d = B/J（d 正則）、`perfectSiteEquivPerfectoidUnder` で添字を移す。
規約：`IsLimitCone`。
使われ方：系 2、Type u 版。 -/
theorem perfectoidization_isLimit : True := by trivial

/-- 概要：系 1（Type u 版）：S_perfd は `PerfUnder_u p S` 上の図式 T ↦ T の極限（CAlg_R、D(R)）。
方針：A5-4 の弱始対象 S̃_perfd（濃度 ≤ κ）の Čech 余脈体で、κ 版と Type u 版の極限がどちらも同じ Tot に等しい（S3、D47）。
規約：錐の形は InterfaceLimitCone で E3 の欄に合わせる。
使われ方：E3 の `limit_isLimit`。 -/
theorem perfectoidization_isLimit_u : True := by trivial

/-- 概要：系 2：S_perfd は A によらない。二つの完全 prism (A,(d))、(A′,(d′))（A/d ≅ R ≅ A′/d′）で CAlg_R の同型。
方針：系 1 の右辺は A を含まない。
規約：`perfectPrism p R` は Not 8.1 で一つ固定しているので、主張は「別の選択」との比較として述べる。
使われ方：記録（E3 では使わない）。 -/
theorem perfectoidization_indep : True := by trivial

/-- 概要：系 3：S が semiperfectoid なら S_perfd は離散で、Cor 7.3 の普遍 perfectoid 環 R′ と S の下で同型。
方針：A5-2（証明 (4) そのもの）。
規約：R′ は既存の `Semiperfectoid/Perfectoidization`（要確認）。
使われ方：A5-4 の弱始対象、Cor 8.14。 -/
theorem perfectoidization_semiperfectoid : True := by sorry -- A5-2

/-! ## animated 版（D45 改訂）と系 4 -/

/-- 概要：Prop 8.5（animated 版）：導来 p 完備な animated R 代数 S（`CompleteAnimatedAlgebra`）について、site を π_0 S で取った比較写像
Δ_{S/A,perf} → lim_{(π_0 S/A)^perf} O は同値。
方針：§3 の四段を animated S で（T → S は π_0 で全射、semiperfectoid の段は π_0 S）。離散 S は `discreteToAnimated` 経由の特別な場合。
規約：π_0 S は離散環（要確認：`animatedPiZero : AnimatedAlgebra R → CommRing`）。
使われ方：系 4、A8（Thm 10.11 は animated LΛ_p S について）。 -/
theorem perfectionComparison_isIso_animated : True := by sorry -- A5-2〜A5-4（animated）

/-- 概要：系 4（決定 6）：Δ_{S,perf} と S_perfd は π_0 S のみによる：S → π_0 S が Δ_{S,perf} ≃ Δ_{π_0 S,perf}、S_perfd ≃ (π_0 S)_perfd を誘導する。
方針：perfectoid 環は離散なので Perfd_{S/} = Perfd_{π_0 S/}、両辺とも同じ極限（animated 版の Prop 8.5）。
規約：—
使われ方：E3 の非完備な離散 S（perfd S := (completionRing S)_perfd、completionRing S = π_0(LΛ_p S)）と直接の式 (LΛ_p S)_perfd の一致（A4-3 `e3Perfd_eq_direct`）、
A8 の `integral`（Thm 10.11 の LΛ_p S から H⁰ 完備化へ）。 -/
theorem perfectoidization_piZero : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
