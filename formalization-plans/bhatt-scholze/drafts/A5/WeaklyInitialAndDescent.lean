-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.WeaklyInitialAndDescent（仮。原典 Prop 8.5 の証明 (1)〜(3)）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §3.1〜§3.3、単位 A5-4。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/A5/{PerfectSiteComparison,SemiperfectoidCase}.lean、drafts/Sheaves/CechConerveLimit.lean、drafts/Shared/Descendable.lean、
-- drafts/A2/BaseChangeAndTensor.lean を import する。

/-!
# 弱始対象・filtered 余極限・Lemma 8.6 による降下（BS 著者版 Prop 8.5 の証明 (1)〜(3)）

## 概要
(1) S に p 乗根を mod p で添加する ω 段の帰納で semiperfectoid な S̃ を作り、S̃_perfd が perfectoid 標的の圏（Type u の `PerfUnder_u` でも κ 側の
完全 site でも）の弱始対象になること。S3 で両方の極限が Tot((S̃^{⊗_S •+1})_perfd) に等しい（D47）。(2) 両辺が filtered 余極限と可換で
π_0 S が位相的有限生成の場合に帰着。(3) T = R⟨X_1..X_r⟩ → S 全射、S̃ = S ⊗̂_T T_∞ への降下：左辺は Lemma 8.6 の底変換で、右辺は左随伴の始性と
極限の交換で、semiperfectoid の場合（A5-2）に帰着。

## 方針
原典の四段のうち形式的な三段。Lemma 8.6 は A5-3 の主張（`prismaticPerfection_rootMap_descendable`）を入力にする。

## 規約
S 離散。S̃ は全元を一度に添加する ω 段（D51）。Perfd_{S/} の余積は (T₁ ⊗̂_S T₂)_perfd（G-A5-14）。

## 使われ方
A5-1 の `perfectionComparison_isIso`・`perfectoidization_isLimit_u`。
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

/-! ## (1) 弱始対象 -/

/-- 概要：一段：S_1 = (S⟨X_s, Y_s : s ∈ S⟩/(s − X_s^p − pY_s))^∧（全元に p 乗根を mod p で添加）。
方針：`MvPolynomial (S ⊕ S) S` の商の p 進完備化（H⁰、U4）。
規約：関手的（S の射で変数を送る）。
使われ方：`rootClosure`。 -/
def rootAdjunctionStep : Type u := sorry

/-- 概要：S̃ := (colim_k S_k)^∧（ω 段、D51）。
方針：段の余極限の p 進完備化。
規約：R 代数、S → S̃。
使われ方：弱始対象。 -/
def rootClosure : Type u := sorry
def rootClosureUnit : S →+* rootClosure p R S := sorry

/-- 概要：(i) 延長性：任意の perfectoid T と S → T は S̃ → T に延びる（各段：s ↦ t、y^p ≡ t mod p の y、X_s ↦ y、Y_s ↦ (t − y^p)/p の原像）。
方針：Frobenius 全射（perfectoid）と p 完備性で段ごとに延長し余極限へ。
規約：延長は一意でない（存在だけ）。
使われ方：弱始性。 -/
theorem rootClosure_extends : True := by trivial

/-- 概要：(ii) S̃ は semiperfectoid：S̃/p は semiperfect（各元が次の段で p 乗根をもつ）、p 完備な R 代数で mod p semiperfect なら perfectoid の商
（G-A5-14、[BMS19, Rem 4.22]：θ : W(S̃^♭) → S̃ 全射、R ⊗̂ W(S̃^♭) は perfectoid）。
方針：既存の θ（`fontaineTheta`）と完備テンソル。
規約：A5-2 の `IsSemiperfectoid`。
使われ方：S̃_perfd の存在（Cor 7.3）、A5-2 の適用。 -/
theorem rootClosure_isSemiperfectoid : IsSemiperfectoid p R (rootClosure p R S) := by sorry

/-- 概要：(iii) #S̃ ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ。
方針：各段の濃度評価と完備化の濃度（A0 `cardinal_envelope_le` と同型の議論）。
規約：κ = `cutoff`。
使われ方：κ 側の site の対象になること（D47）。 -/
theorem rootClosure_cardinal_le : True := by trivial

/-- 概要：(iv) S ↦ S̃ は関手的で filtered 余極限と可換（各段が有限型の構成＋完備化）。
方針：段ごとの関手性。
規約：完備化した余極限。
使われ方：§3.2。 -/
theorem rootClosure_filteredColimit : True := by trivial

/-- 概要：弱始対象 S̃_perfd ∈ `PerfUnder_u p S`（A5-2 の普遍 perfectoid 環 R′(S̃)、Prop 8.5 の系 3 で Δ_{S̃,perf}/d）。
方針：`universalPerfectoidRing` を S の上の環として。
規約：`PerfUnder_u p S` の対象。
使われ方：S3。 -/
def perfectoidTargetWeaklyInitial : True := trivial

/-- 概要：弱始性：任意の T ∈ `PerfUnder_u p S` に S の下で S̃_perfd → T がある（延長性と R′ の普遍性）。κ 側の site でも同様。
方針：`rootClosure_extends`、`universalPerfectoidUnit_isPerfectoidization`。
規約：S3 の `IsWeaklyTerminal`（site は opposite）。
使われ方：`limit_perfUnder_eq_tot`。 -/
theorem perfectoidTargetWeaklyInitial_isWeaklyInitial : True := by trivial

/-- 概要：G-A5-14：Perfd_{S/} の余積は (T₁ ⊗̂_S T₂)_perfd（T₁ ⊗̂_S T₂ は perfectoid T₁ ⊗̂_R T₂ の商で semiperfectoid、Cor 7.3 の普遍性）。
Čech 余脈体 (S̃^{⊗_S n+1})_perfd。
方針：A5-2 の `universalPerfectoidRing` と普遍性。
規約：S3 の `CechNerveData`（`PerfUnder_u p S` の opposite）。
使われ方：`limit_perfUnder_eq_tot`。 -/
def perfUnder_cechNerveData : True := trivial

/-- 概要：lim_{PerfUnder_u p S} T ≃ Tot((S̃^•)_perfd)（S3 `exists_limitCone_of_cech`）。κ 側の完全 site でも同じ Tot（弱始対象は濃度 ≤ κ）。
よって Type u の極限と κ-small の site の極限は一致（D47）。
方針：S3 を二回。
規約：—
使われ方：A5-1 の `perfectoidization_isLimit_u`。 -/
theorem limit_perfUnder_eq_tot : True := by trivial
theorem limit_perfectSite_eq_tot : True := by trivial
theorem limit_perfUnder_eq_limit_perfectSite : True := by trivial

/-! ## (2) filtered 余極限 -/

/-- 概要：左辺：S ↦ Δ_{S/A,perf} は（完備化した）filtered 余極限と可換（Δ は sifted 余極限を保つ、colim_φ と完備化も）。
方針：A2-4 `derivedPrismaticCohomology_siftedColimit`、G-A4-2、G-A2-3。
規約：D_comp(A) の余極限。
使われ方：有限生成への帰着、A5-2 (δ)。 -/
theorem prismaticPerfection_filteredColimit : True := by trivial

/-- 概要：G-A5-2：一様に coconnective な余単体的対象の Tot は filtered 余極限と可換（H^k(Tot X) = H^k(Tot_{≤k+1} X)、部分 Tot は有限極限）。
方針：Tot の塔と coconnectivity。
規約：D(A) の cohomological な添字。
使われ方：右辺の可換性。 -/
theorem tot_coconnective_filteredColimit : True := by trivial

/-- 概要：右辺：S ↦ lim_{Perfd_{S/}} T = Tot((S̃_S^•)_perfd) は filtered 余極限と可換（(iv)、semiperfectoid の (−)_perfd の可換性、G-A5-2、完備化）。
方針：上の三つ。紙 3（完備化と Tot の順序）。
規約：—
使われ方：有限生成への帰着。 -/
theorem limit_perfectSite_filteredColimit : True := by trivial

/-- 概要：π_0 S が位相的有限生成の S で比較写像が同値なら、すべての離散 S で同値。
方針：S = (colim S_i)^∧、両辺の可換性。
規約：—
使われ方：A5-1 の `perfectionComparison_isIso`。 -/
theorem perfectionComparison_isIso_of_finiteType_cases : True := by trivial

/-! ## (3) Lemma 8.6 による降下 -/

/-- 概要：T_∞ = R⟨X_1^{1/p^∞},…,X_r^{1/p^∞}⟩（p 完備化）と T = R⟨X_1,…,X_r⟩ → T_∞。
方針：`MvPolynomial (Fin r × ℕ)` の商の p 進完備化、既存の `CompatibleRootCompletion` の多変数版（要確認）。
規約：—
使われ方：S̃ = S ⊗̂_T T_∞。 -/
def polyRootAlgebra (r : ℕ) : Type u := sorry

/-- 概要：S̃ = S ⊗̂_T T_∞（T → S 全射）と S̃^n = (S̃^{⊗_S n+1})^∧。各 S̃^n は semiperfectoid（S/p の元は R/p 係数の x_i の多項式）。
方針：完備テンソル。
規約：`IsSemiperfectoid`。
使われ方：降下。 -/
def rootCover (r : ℕ) (f : Fin r → S) : Type u := sorry
theorem rootCover_isSemiperfectoid (r : ℕ) (f : Fin r → S) (hf : True) : True := by trivial

/-- 概要：左辺の降下：Δ_{S,perf} → Δ_{S̃,perf} は Δ_{T,perf} → Δ_{T_∞,perf} の底変換（(5) と G-A5-3）で descendable（Lemma 8.6、(a)）、
よって Δ_{S,perf} ≃ Tot Δ_{S̃^•,perf}（(e)）。
方針：Shared/Descendable の `isDescendable_baseChange`・`isDescendable_tot_equiv`、A5-1 の `prismaticPerfection_rootMap_descendable`。
規約：D_comp(A)。
使われ方：`perfectionComparison_isIso_of_finiteType`。 -/
theorem prismaticPerfection_rootCover_descent (r : ℕ) (f : Fin r → S) : True := by trivial

/-- 概要：G-A5-7：L_n : Perfd_{S/} → Perfd_{S̃^n/}、R′ ↦ (R′ ⊗̂_S S̃^n)_perfd は忘却の左随伴、よって始的で lim_{Perfd_{S̃^n/}} O = lim_{Perfd_{S/}} O ∘ L_n。
方針：随伴の単位・余単位（Cor 7.3 の普遍性）、HTT 4.1.1.8 の系。
規約：—
使われ方：右辺の降下。 -/
theorem perfUnder_leftAdjoint_initial : True := by trivial

/-- 概要：右辺の降下：各 R′ で B_{R′} ≃ Tot_n Δ_{R′ ⊗̂_S S̃^n,perf}（Lemma 8.6 の底変換）、極限の交換（G-A5-8）で
lim_{Perfd_{S/}} B_{R′} ≃ Tot_n lim_{Perfd_{S̃^n/}} O。
方針：上と `prismaticPerfection_rootCover_descent` を R′ に適用。紙 4。
規約：—
使われ方：`perfectionComparison_isIso_of_finiteType`。 -/
theorem limit_perfectSite_rootCover_descent (r : ℕ) (f : Fin r → S) : True := by trivial

/-- 概要：π_0 S が位相的有限生成なら比較写像は同値：両辺の Tot の各項は semiperfectoid の場合（A5-2 `perfectoidization_semiperfectoid_iso` の
prism 版 Δ_{S̃^n,perf} ≃ B_{(S̃^n)_perfd}）で同値。
方針：上の二つと A5-2。
規約：—
使われ方：A5-1 の `perfectionComparison_isIso`（`perfectionComparison_isIso_of_finiteType_cases` と合わせる）。 -/
theorem perfectionComparison_isIso_of_finiteType (r : ℕ) (f : Fin r → S) (hf : Function.Surjective (fun _ : Unit => (0 : S))) : True := by
  trivial -- 要確認：仮定は「T = R⟨X_1..X_r⟩ → S が π_0 で全射」の形に

end SerrePositivity.BhattScholze.Perfectoidization.Derived
