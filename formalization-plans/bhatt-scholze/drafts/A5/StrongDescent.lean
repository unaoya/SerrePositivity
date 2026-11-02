-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.StrongDescent（仮。原典 Lemma 8.6）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.4・§3.5、単位 A5-3。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/Shared/Descendable.lean、drafts/Shared/DeRhamPolynomial.lean、drafts/A5/{PerfectSiteComparison,WeaklyInitialAndDescent}.lean、
-- drafts/A2/BaseChangeAndTensor.lean、drafts/DerivedGeneral/Truncation.lean、drafts/A1/（A1-5：Thm 6.4 の多項式・mod p）を import する。

/-!
# 完全化への移行の強い降下（BS 著者版 Lemma 8.6）

## 概要
T = R⟨X_1,…,X_n⟩ → T_∞ = R⟨X_i^{1/p^∞}⟩ について、Δ_{T/A} → Δ_{T_∞/A} と Δ_{T/A,perf} → Δ_{T_∞/A,perf} は D_comp(A) の可換代数の射として
descendable。

## 方針
perf 版は非 perf 版と [BS17, Lemma 11.22]（Descendable の (g)）。非 perf 版は n = 1 に帰着（(5) とテンソル (c)）。n = 1：F = fib(Δ_T → Δ_{T_∞})
について RHom_{Δ_T}(F^{⊗2}, Δ_T) ∈ D^{<0} を示す（(f)）。完備性で A → A/(p, φ^{-1}(d)) の底変換後に確かめればよく（G-A5-6）、
Δ_T ⊗_A A/φ^{-1}(d) = φ_A^*Δ_T ⊗_A A/d は de Rham 比較（A1-5：Thm 6.4 の多項式・mod p）で Ω^•_{(T/p)/(R/p)}、T_∞ では L = 0 で T_∞/p。
一変数の Cartier で Ω^• は分裂二乗零拡大 Ω = T ⊕ Ω^1[−1] と cdga として擬同型（G-A5-12）、(∗) の dg 加群の計算（G-A5-13）。

## 規約
descendable は Shared/Descendable（Mat16 の定義）。de Rham 入力は A1-5 の定理（黒箱にしない、決定 3）。

## 使われ方
A5-4 の降下（`prismaticPerfection_rootCover_descent`）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- 概要：Lemma 8.6（非 perf 版）：Δ_{T/A} → Δ_{T_∞/A} は D_comp(A) で descendable。
方針：`rootMap_descendable_one` と n への帰着。
規約：`IsDescendable`（完備版 (h)）。
使われ方：perf 版。 -/
theorem prismaticCohomology_rootMap_descendable (n : ℕ) : True := by trivial

/-- 概要：Lemma 8.6（perf 版）：Δ_{T/A,perf} → Δ_{T_∞/A,perf} は descendable（(g)：非 perf 版の index の上界 m から perf 版は ≤ 2m。n は変数の個数で index ではない、
W9 §8.7。結論は `IsDescendable` でよく数値は公開しない）。A5-1 の主張の証明。
方針：非 perf 版と `hasDescentIndexLE_frobeniusColimit`、完備化。
規約：—
使われ方：A5-4。 -/
theorem prismaticPerfection_rootMap_descendable' (n : ℕ) : True := by trivial

/-! ## n = 1 への帰着 -/

/-- 概要：Δ_{T_n/A} = Δ_{T_1/A}^{⊗̂_A n}、Δ_{T_{n,∞}} も同様（(5)）。descendable のテンソル (c) で n = 1 に帰着。
方針：A2-4 `derivedPrismaticCohomology_tensor`。
規約：—
使われ方：上。 -/
theorem rootMap_descendable_of_one : True := by trivial

/-! ## n = 1 -/

/-- 概要：F := fib(Δ_T → Δ_{T_∞}) ∈ D(Δ_T)。RHom_{Δ_T}(F^{⊗2}, Δ_T) ∈ D^{<0} なら index ≤ 2（(f)）。
方針：Shared/Descendable の `hasDescentIndexLE_two_of_rhom`。
規約：テンソルは D(Δ_T)。
使われ方：`rootMap_descendable_one`。 -/
theorem rootMap_fiber_rhom_coconnective : True := by trivial

/-- 概要：G-A5-6：導来 (p,d) 完備な M で M ⊗^L_A A/(p, φ^{-1}(d)) ∈ D^{<0} ⇒ M ∈ D^{<0}（最高次の H は完備で Nakayama）。
(p, φ^{-1}(d)) と (p,d) は同じ根基。
方針：DerivedGeneral/Truncation の `derived_nakayama` の上界版。
規約：—
使われ方：底変換後に確かめる。 -/
theorem coconnective_of_modBaseChange : True := by trivial

/-- 概要：G-A5-6′（W9-II-12、要確認）：M := RHom_{Δ_T}(F^{⊗2}, Δ_T) は第二引数の完備性から導来 (p,d) 完備。F^{⊗2} は perfect でないので
RHom_{Δ_T ⊗ C}((F ⊗ C)^{⊗2}, Δ_T ⊗ C)（C = A/(p, φ^{-1}(d))）を M ⊗ C と無条件に同一視できない。有限 Koszul 複体 K_m（双対可能）では
RHom(F^{⊗2}, Δ_T ⊗ K_m) = M ⊗ K_m と交換できるので、完備性の判定を K_m で述べ、通常の商 C 上の (∗) の計算へ渡す接続を専用補題にする。
方針：原典 "By completeness" の一文の形式化。
規約：—
使われ方：`rootMap_fiber_rhom_coconnective`。 -/
theorem rhom_baseChange_koszul_connection : True := by trivial

/-- 概要：A/(p, φ^{-1}(d)) ≅ R/p（φ_A が自己同型で A/φ^{-1}(d) ≅_φ A/d = R）。Δ_T ⊗_A A/φ^{-1}(d) = φ_A^*Δ_T ⊗_A A/d。
方針：完全 prism の φ_A。
規約：—
使われ方：de Rham 比較を当てる。 -/
theorem baseChange_phiInv_eq_frobeniusTwist : True := by trivial

/-- 概要：de Rham 入力（A1-5、G-A5-15）：φ_A^*Δ_{T/A} ⊗^L_A A/(p,d) ≃ Ω^•_{(T/p)/(R/p)}（T = R⟨X⟩、E∞ 代数として）、T → T_∞ と両立し、
T_∞ 側は L_{T_∞/R}^∧ = 0 で T_∞/p。
方針：A1-5 の定理（Thm 6.4 の多項式・mod p の特別な場合）を引く。
規約：—
使われ方：(∗) への帰着。 -/
theorem rootMap_modP_eq_deRham : True := by trivial

/-- 概要：G-A5-12：一変数 de Rham 複体の Cartier・形式性：任意の F_p 代数 R_0 で Ω^•_{R_0[X]/R_0} ≃ R_0[X^p] ⊕ R_0[X^p]·X^{p−1}dX[−1]
（零微分の分裂二乗零拡大）は cdga の擬同型（X^a R_0[X^p]、0 < a < p、の成分で d が同型）。
方針：Shared/DeRhamPolynomial の `deRhamComplex` の一変数版と直和分解。
規約：T := R_0[X^p] ≅ T^{(1)}。
使われ方：(∗)。 -/
theorem deRhamOneVariable_formal : True := by trivial

/-- 概要：G-A5-13 (∗)：Ω = T ⊕ Ω^1[−1] 上、F = fib(Ω → T → T_∞) ≅ T^{⊕J}[−1]（T_∞ は T 上自由で 1 を基底に含む）、
RHom_Ω((T[−1])^{⊗2}, Ω) ∈ D^{<0}（分解 (⋯ → Ω[−2] → Ω[−1]) ≃ T[−1] の計算）。
方針：dg 加群の明示計算。
規約：D(Ω)。
使われ方：`rootMap_fiber_rhom_coconnective`。 -/
theorem squareZero_rhom_coconnective : True := by trivial

/-- 概要：n = 1 の Lemma 8.6：上の五つを合わせる。
方針：—
規約：—
使われ方：`prismaticCohomology_rootMap_descendable`。 -/
theorem rootMap_descendable_one : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
