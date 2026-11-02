-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.BaseChange（仮。原典 Construction 7.6 の (4)(5) と D32）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.4、単位 A2-4。基準コミット 972bb7f53。ビルドしない。
module

-- 本ファイルは drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology,HodgeTateFiltration}.lean、drafts/DerivedGeneral/CompletionFunctor.lean、
-- drafts/A1/HodgeTateComparison.lean（Cor 4.12）を import する。

/-!
# 導来 prismatic コホモロジーの底変換・テンソル・導来 p 完備化不変性（BS 著者版 Construction 7.6 の (4)(5)）

## 概要
(4) 有界 prism の射 (A,(d)) → (A′,(d′)) について Δ_{R_{A′}/A′} ≃ Δ_{R/A} ⊗̂^L_A A′（完備底変換）。(5) Δ は sifted 余極限を保ち（構成）、
有限余積（テンソル）を完備テンソルへ送る：Δ_{R ⊗^L_k R′} ≃ Δ_R ⊗̂ Δ_{R′}（E∞ 代数の余積）。これが「対称モノイダル」の内容。
D32：Δ_R は R の導来 p 完備化で不変。

## 方針
いずれも Poly 上で示して Kan 延長（両辺が sifted 余極限を保つ）で一般へ。(4) の Poly 上は Cor 4.12（A1）。(5) の Poly 上は多項式代数の
Künneth：HT filtration つきの比較射 Δ_{P⊗P′} ← Δ_P ⊗̂ Δ_{P′} が gr で Ω^•_{P⊗P′} = Ω^•_P ⊗ Ω^•_{P′} の同型を誘導し、filtration が
exhaustive・完備なので同型。D32 も gr（余接複体の p 完備化の不変性）と導来 Nakayama。

## 規約
完備テンソル・完備底変換は DerivedGeneral/CompletionFunctor の `completedBaseChange`。E∞ 代数の余積 ＝ テンソル（HA 3.2.4.7、G-A2-4）。

## 使われ方
A5（Prop 8.5 の底変換）、A7（Prop 8.13：S ↦ S_perfd の対称モノイダル性は (5) の Frobenius 余極限と完備化への移送）、A8（Thm 10.11）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## (4) 底変換 -/

/-- 概要：prism の射 f : (A,(d)) → (A′,(d′)) に沿う始域の底変換 R ↦ R ⊗^L_k k′（P_Σ の関手。Poly 上は多項式代数の底変換で、sifted 余極限保存な延長）。
方針：Poly k → Poly k′（同じ添字 n）の nerve を P_Σ へ延長。
規約：k′ = A′/d′。
使われ方：(4) の主張。 -/
def animatedBaseChange {A' : Type u} [CommRing A'] (P' : OrientedPrism p A') (f : OrientedPrism.Hom P P') :
    AnimatedAlgebra (A ⧸ P.ideal) ⟶ AnimatedAlgebra (A' ⧸ P'.ideal) := sorry

/-- 概要：(4)：Δ_{R_{A′}/A′} ≃ Δ_{R/A} ⊗̂^L_A A′（完備底変換、E∞ 代数として）。
方針：Poly 上は Cor 4.12（`prismaticCohomology_baseChange'`、Tor 振幅の仮定なし）。両辺とも sifted 余極限保存（完備底変換は左随伴の合成）。
規約：同値は 𝒱 の可逆な辺、R について自然。
使われ方：A5、A7、A8。 -/
theorem derivedPrismaticCohomology_baseChange {A' : Type u} [CommRing A'] (P' : OrientedPrism p A')
    (hP' : IsBoundedPrism P') (f : OrientedPrism.Hom P P') : True := by trivial

/-! ## (5) sifted 余極限とテンソル -/

/-- 概要：Δ は sifted 余極限を保つ（構成から）。
方針：`derivedPrismaticCohomology_preservesSifted`。
規約：𝒱 の sifted 余極限 ＝ CAlg_A の sifted 余極限の完備化。
使われ方：(5)。 -/
theorem derivedPrismaticCohomology_siftedColimit : True := by trivial

/-- 概要：多項式代数の Künneth（Poly 上の (5)）：Δ_{P ⊗ P′} ≃ Δ_P ⊗̂ Δ_{P′}。
方針：比較射は E∞ 代数の余積の普遍性（Δ_P → Δ_{P⊗P′} ← Δ_{P′}、関手性）。gr で Ω^•_{P⊗P′} = Ω^•_P ⊗ Ω^•_{P′}（Shared/DeRhamPolynomial）、
filtration は exhaustive・有限段、完備性。または Čech–Alexander 模型と Eilenberg–Zilber。
規約：—
使われ方：(5) の一般へ。 -/
theorem prismaticCohomologyPoly_tensor (n m : ℕ) : True := by trivial

/-- 概要：(5)：Δ_{R ⊗^L_k R′} ≃ Δ_R ⊗̂ Δ_{R′}（𝒱 の余積）。すなわち Δ は対称モノイダル。
方針：両辺が各変数で sifted 余極限を保つ（P_Σ のテンソルは各変数で sifted 余極限を保つ、HTT 5.5.8.？）ので、Poly 上の Künneth から。
規約：対称性・結合性の coherence は E∞ 代数の余積のもの。
使われ方：Prop 8.13（A7）、Thm 10.11。 -/
theorem derivedPrismaticCohomology_tensor : True := by trivial

/-! ## D32：導来 p 完備化不変性 -/

/-- 概要：P_Σ 上の導来 p 完備化 R ↦ R^∧（要確認：定義。E3 の経路では離散 R の完備化 R^∧ = `completionRing` との比較だけが要る）。
方針：ここでは離散 R について：単位 R → R^∧（E3 の `completionUnit`）が Δ の同値を誘導することを述べる。
規約：一般の P_Σ 上の完備化は定義しない（E3 に不要）。
使われ方：E3 の `perfd` が非完備な始域に延びること（界面の規約 (v)）。 -/
theorem derivedPrismaticCohomology_completion_discrete : True := by trivial
-- Δ_R ≃ Δ_{R^∧}：gr（cotangentWedge）の不変性（L_{R^∧/R} の p 完備化が零）と exhaustive 性、導来 Nakayama

end SerrePositivity.BhattScholze.Prismatic
