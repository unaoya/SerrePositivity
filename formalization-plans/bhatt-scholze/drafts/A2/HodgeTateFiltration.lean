-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.HodgeTateFiltration（仮。原典 Construction 7.6 の HT filtration）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.3、単位 A2-3。基準コミット 972bb7f53。ビルドしない。
module

-- 本ファイルは drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology}.lean、drafts/DerivedGeneral/Truncation.lean、
-- drafts/A1/HodgeTateComparison.lean（Thm 6.3）、drafts/Shared/DeRhamPolynomial.lean を import する。

/-!
# Hodge–Tate filtration と導来外冪つき余接複体（BS 著者版 Construction 7.6 の第二段落）

## 概要
Δ̄_R := Δ_R ⊗^L_A A/d（D(A) 値、E∞ 構造は忘れる）に、exhaustive な増大 ℕ 添字の filtration Fil_i Δ̄_R を、多項式代数上の Postnikov 切り捨て
τ^{≤i} Δ̄_P の左 Kan 延長として定める。次数商 gr^i は Ω^i_{P/k}[−i] の左 Kan 延長で、これを (∧^i L_{R/k})^∧[−i]（導来外冪つき余接複体の
p 完備化の −i shift）の**定義**とする（D33。Illusie の単体的分解による定義と一致）。原典の「HT 比較 for Δ̄_R」は、この gr の同一視
（多項式代数上の Thm 6.3）。

## 方針
Kan 延長（sifted 余極限保存な延長、HTT 5.5.8.15）は cofiber と余極限と交換するので、filtration・gr・exhaustive 性は Poly 上の性質から従う。
D(A) 値で述べる（E∞ 構造つきの filtration は A4 以降で要れば足す）。

## 規約
捻り {−i} は向き付きなので落とす（D28）。多項式代数上では Δ̄_P ∈ D^{[0,n]}（Thm 6.3）なので Fil_n = Δ̄_P。

## 使われ方
A2-4（完備化不変性・テンソルの gr による証明）、A4（Lemma 8.4：P⁰ の議論は別だが、Example 8.3 で gr を使う）、A5（Prop 8.5：S 半完全 perfectoid なら
L_{S/Z_p}[−1] 連結 ⇒ Δ_S 連結）、A7（Prop 8.13：gr の Künneth）、A8（Thm 10.11 の Lemma 10.12）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## 多項式代数上の切り捨て -/

/-- 概要：Δ̄_0(P) := Δ_0(P) ⊗^L_A A/d（D(A) 値）。
方針：`derivedPrismaticCohomologyDerived` と D(A) の ⊗^L A/d（A0 の `hodgeTateCohomology` と同じ）。
規約：D(A) の頂点。
使われ方：Postnikov 切り捨ての入力。 -/
def hodgeTatePoly : (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ derivedInfinityCategory A := sorry

/-- 概要：Poly 上の τ^{≤i} Δ̄_0（i : ℕ）、関手的。
方針：DerivedGeneral/Truncation の `truncationLE A i` を後合成。
規約：i について増大（τ^{≤i} → τ^{≤i+1}）。
使われ方：Fil_i の Kan 延長の入力。 -/
def hodgeTatePolyTruncated (i : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ derivedInfinityCategory A :=
  hodgeTatePoly P ≫ Derived.truncationLE A i

/-- 概要：Thm 6.3 による gr^i の同一視（Poly 上）：τ^{≤i}/τ^{≤i−1} Δ̄_P ≃ H^i(Δ̄_P)[−i] ≃ Ω^i_{P/k}[−i]。
方針：`truncation_cofiber`（DerivedGeneral）と A1 の `hodgeTate_iso`（η^i : Ω^i ≅ H^i）。自然性は η^* の関手性。
規約：Ω^i は Shared/DeRhamPolynomial の `completedForms`（p 完備化した多項式代数の微分形式）を A 加群として D(A) に埋めたもの。
使われ方：gr の同一視の Kan 延長。 -/
theorem hodgeTatePoly_gr (i : ℕ) : True := by trivial

/-- 概要：Poly 上で Δ̄_P ∈ D^{[0,n]}（n = 変数の個数）なので τ^{≤n} Δ̄_P ≃ Δ̄_P。
方針：Thm 6.3（H^i = 0 for i > n）と `truncationLE_of_isCoconnective`。
規約：—
使われ方：exhaustive 性。 -/
theorem hodgeTatePoly_bounded (n : ℕ) : True := by trivial

/-! ## Kan 延長 -/

/-- 概要：HT filtration Fil_i Δ̄ : P_Σ(N(Poly k)) → D(A)、τ^{≤i} Δ̄_0 の sifted 余極限保存な延長。
方針：A2-1 の `exists_siftedExtension`（D(A) は sifted 余極限をもつ）。
規約：D(A) 値。
使われ方：以下。 -/
def hodgeTateFiltration (i : ℕ) : AnimatedAlgebra (A ⧸ P.ideal) ⟶ derivedInfinityCategory A := sorry

/-- 概要：Fil_i → Fil_{i+1} と Fil_i → Δ̄（Poly 上の τ^{≤i} → τ^{≤i+1} → Δ̄ の延長）。
方針：自然変換の Kan 延長。
規約：—
使われ方：filtration の構造。 -/
def hodgeTateFiltration_step (i : ℕ) : True := trivial

/-- 概要：導来外冪つき余接複体の p 完備化の定義（D33）：(∧^i L_{R/k})^∧ := (P ↦ Ω^i_{P/k}) の sifted 余極限保存な延長。
方針：Shared/DeRhamPolynomial の `completedForms` を A 加群として D(A) に埋め、Kan 延長。
規約：i = 1 が余接複体 L^∧_{R/k}。Illusie の定義（単体的分解による Kan 延長）と同じ。
使われ方：gr の同一視、A5（L_{S/Z_p} の連結性）。 -/
def cotangentWedge (i : ℕ) : AnimatedAlgebra (A ⧸ P.ideal) ⟶ derivedInfinityCategory A := sorry

/-- 概要：gr^i Fil Δ̄_R ≃ cotangentWedge i (R)[−i]（原典の「Hodge–Tate comparison for Δ̄_R」）。
方針：Kan 延長は cofiber と交換（余極限と shift と交換）、Poly 上で `hodgeTatePoly_gr`。
規約：同値は D(A) の可逆な辺、R について自然。
使われ方：A2-4、A5、A7、A8。 -/
theorem hodgeTateFiltration_gr (i : ℕ) : True := by trivial

/-- 概要：filtration は exhaustive：colim_i Fil_i Δ̄_R ≃ Δ̄_R。
方針：Kan 延長は ℕ 添字の余極限と交換、Poly 上は有限段で止まる（`hodgeTatePoly_bounded`）。
規約：完備化との両立は A2-4 の完備化不変性で扱う（Δ̄ は Δ ⊗ A/d で、Δ は完備。Δ̄ の完備性は p についてのみ）。
使われ方：連結性・離散性の議論（A3・A5）。 -/
theorem hodgeTateFiltration_exhaustive : True := by trivial

/-- 概要：Fil_0 Δ̄_R ≃ (L^∧ の 0 次 =) R^∧ の p 完備化、すなわち単位 R → Δ̄_R の H⁰ への射（E3 の `unit` の材料）。
方針：Poly 上で τ^{≤0} Δ̄_P = H⁰ = P^∧（Thm 6.3 の η⁰）、Kan 延長。
規約：—
使われ方：A4（単位）、E3 の `unit`・`h0`。 -/
theorem hodgeTateFiltration_zero : True := by trivial

end SerrePositivity.BhattScholze.Prismatic
