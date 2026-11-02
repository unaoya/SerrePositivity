-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.InterfaceFields（仮。E3 の CAlg 版界面の欄 perfd・unit・h0）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md §2.3、単位 A4-3。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.EInfinity.Perfectoidization.Interface
public import SerrePositivity.EInfinity.Perfectoidization.Comparison
-- 本ファイルは drafts/A4/Perfectoidization.lean、drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology,HodgeTateFiltration,BaseChangeAndTensor}.lean を import する。

/-!
# E3 の界面の欄 `perfd`・`unit`・`h0` の構成（BS 著者版 Def 8.2 を関手にしたもの）

## 概要
`PerfectoidizationInterfaceCAlg` の最初の三欄を、A4-1 の S_perfd から作る。`e3Perfd : algebraNerve R ⟶ CAlg_R R` は
S ↦ (S^∧)_perfd（S^∧ は界面の `completionRing`、導来 p 完備化の H⁰）、`e3Unit` は S → S^∧ = Fil_0 Δ̄_{S^∧} → Δ̄_{S^∧} → Δ̄_{S^∧,perf} = (S^∧)_perfd
の合成の coherent な単位、`e3H0RingData` は H⁰(S_perfd) の環の関手と加群構造・射・単位との整合。

## 方針
Def 8.2 は導来 p 完備な S にだけ定義されている（D41）ので、界面の欄は S^∧ = completionRing S = π_0(LΛ_p S) を経由して定める。直接の式
(colim_φ Δ_S)^∧ ⊗ A/d を非完備な離散 S に当てたものと一致することは二段（W9-II-03）：Δ_S ≃ Δ_{LΛ_p S}（A2-4 `derivedPrismaticCohomology_completion_animated`）と
(LΛ_p S)_perfd ≃ (π_0 LΛ_p S)_perfd（A5-1 `perfectoidization_piZero`、Prop 8.5 系 4）。
関手性は A2 の Δ（`derivedPrismaticCohomologyDiscrete`、nerve の射）から：Frobenius の塔・余極限・完備化・⊗ A/d をすべて関手の段で取る。

## 規約
欄の型は Interface.lean / EInfinity/Perfectoidization/Interface.lean の現行の型に合わせる（`FunctorHom`、`H0RingData`、`underlyingUnit`）。
2b の改名表が来たら名前を追従する（`completionRing` など）。

## 使われ方
`PerfectoidizationInterfaceCAlg` の構成（A9）。残りの欄 universal（A7 Cor 8.14）、limitCone・limit_isLimit（A5 Prop 8.5）、integral（A8 Thm 10.11）、
excision（A6 Cor 8.12）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-! ## 関手の段の Def 8.2 -/

/-- 概要：Def 8.2 (1) を関手として：algebraNerve R（離散 R 代数）→ CAlg_A、S ↦ Δ_{S/A,perf}。
方針：`derivedPrismaticCohomologyDiscrete`（A2-2、k = R = A/d）の Frobenius の塔（`frobeniusTower` の関手版）の CAlg_A での
sequential 余極限（G-A4-2、関手の圏で点ごと）と完備化の関手（G-A2-3）の合成。
規約：定義域は離散 R 代数全体（Δ は A2 で全 animated 代数に定義済み）。Def 8.2 の意味をもつのは導来 p 完備な S だけ（D41）。
使われ方：`perfectoidizationFunctor`。 -/
def prismaticPerfectionFunctor : algebraNerve R ⟶ CAlg_R (perfectPrismRing p R) := sorry

/-- 概要：Def 8.2 (2) を関手として：S ↦ Δ_perf ⊗^L_A A/d。
方針：`prismaticPerfectionFunctor` と底変換 CAlg_A → CAlg_R（G-A4-4、`perfectPrism_quotientEquiv` で A/d ≅ R）の合成。
規約：—
使われ方：`e3Perfd`。 -/
def perfectoidizationFunctor : algebraNerve R ⟶ CAlg_R R := sorry

/-- 概要：点ごとの値は A4-1 の `perfectoidization` に一致する。
方針：定義の展開（余極限・完備化・底変換は点ごと）。
規約：`VertexIso`（CAlg_R R の頂点の同型）。
使われ方：Lemma 8.4 を欄に移す。 -/
theorem perfectoidizationFunctor_vertex (S : Type u) [CommRing S] [Algebra R S] : True := by trivial

/-! ## 完備化の関手 -/

/-- 概要：S ↦ S^∧（`completionRing`、導来 p 完備化の H⁰）の A_R R 上の関手。
方針：`completionRing` の普遍性（Interface.lean の ∃! g, completionUnit ≫ g = f）で射を定め、関手性も普遍性から。
規約：R 代数の構造は `completionUnit` の合成。
使われ方：`e3Perfd`。要確認：既存に関手版があるか（`completionRing` は対象だけ）。 -/
def completionFunctor : A_R R ⥤ A_R R := sorry

/-- 概要：単位 S → S^∧ の自然変換。
方針：`completionUnit`。
規約：—
使われ方：`e3Unit` の最初の段。 -/
def completionFunctorUnit : 𝟭 (A_R R) ⟶ completionFunctor p R := sorry

/-! ## 欄 perfd -/

/-- 概要：E3 の `perfd`：S ↦ (S^∧)_perfd（D41、界面の規約）。
方針：`nerveMap (completionFunctor p R) ≫ perfectoidizationFunctor p R`。
規約：`algebraNerve R` は nerve (A_R R) の持ち上げ（要確認：`nerveMap` の宇宙）。
使われ方：`PerfectoidizationInterfaceCAlg.perfd`。 -/
def e3Perfd : algebraNerve R ⟶ CAlg_R R := sorry

/-- 概要：導来 p 完備な S では `e3Perfd` の値は Def 8.2 の S_perfd そのもの（S^∧ ≅ S）。
方針：`completionUnit` が同型（`IsModuleComplete` のもとで H⁰ の完備化単位は同型）と `perfectoidizationFunctor_vertex`。
規約：`VertexIso`。
使われ方：Lemma 8.4 (c)・Cor 8.14 を欄に移す。 -/
theorem e3Perfd_of_complete (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) : True := by trivial

/-- 概要：任意の離散 S で、`e3Perfd` の値は直接の式 (colim_φ Δ_S)^∧ ⊗^L_A A/d（S を完備化せずに A2 の Δ_S に当てたもの）に一致する。
方針：D32 の animated 版（Δ_S ≃ Δ_{LΛ_p S}、A2-4 `derivedPrismaticCohomology_completion_animated`）で直接の式は (LΛ_p S)_perfd、
Prop 8.5 の系 4（A5-1 `perfectoidization_piZero`）で (LΛ_p S)_perfd ≃ (π_0 LΛ_p S)_perfd = (completionRing S)_perfd（W9-I-29、決定 6）。
規約：これが D41 の「直接の式との一致は定理」。
使われ方：A6（Prop 8.10：任意の離散 S に対する arc 層としての記述）、A8。 -/
theorem e3Perfd_eq_direct (S : Type u) [CommRing S] [Algebra R S] : True := by trivial

/-- 概要：D(R) 版の `perfd`（忘却 U との合成）。
方針：`e3Perfd ≫ cAlgForgetDerived R`。
規約：`nonempty_e3_of_cAlg` がこの形で D(R) 版を作るので、別に定義は要らない（記録のみ）。
使われ方：—（`nonempty_e3_of_cAlg`）。 -/
theorem e3Perfd_derived : True := by trivial

/-! ## 欄 unit -/

/-- 概要：S^∧ → Δ̄_{S^∧} = Δ_{S^∧} ⊗^L_A A/d の自然変換（Fil_0 Δ̄ = S^∧、A2-3 の `hodgeTateFiltration_zero`）。
方針：`algebraEmbedding R ≫ (⋯)` から `derivedPrismaticCohomologyDiscrete ≫ 底変換` への `FunctorHom`。HT filtration の Fil_0 → 全体の
自然変換（Kan 延長の自然変換）に、Fil_0 ≅ 完備化の同型を前置する。
規約：`FunctorHom`（CAlg_R R の関手の圏の射）。
使われ方：`e3Unit` の第二段。 -/
def hodgeTateUnit : True := trivial

/-- 概要：Δ̄_S → Δ̄_{S,perf} = S_perfd の自然変換（Frobenius の余極限の 0 番目の脚の mod d、完備化の単位との合成）。
方針：余極限の脚（関手の圏で点ごと）と完備化の単位（G-A2-3 の反射の単位）の合成、底変換で ⊗ A/d。
規約：—
使われ方：`e3Unit` の第三段。 -/
def perfectionLeg : True := trivial

/-- 概要：E3 の `unit`：S → S^∧ → Δ̄_{S^∧} → (S^∧)_perfd の coherent な単位。
方針：`nerveMap completionFunctorUnit`（離散の段、`algebraEmbedding` を通す）、`hodgeTateUnit`、`perfectionLeg` の合成。
各段が関手の圏の射なので合成も射。
規約：`FunctorHom (algebraEmbedding R) (e3Perfd p R)`。
使われ方：`PerfectoidizationInterfaceCAlg.unit`。 -/
def e3Unit : FunctorHom (algebraEmbedding R) (e3Perfd p R) := sorry

/-- 概要：導来 p 完備な S では、`e3Unit` の S 成分は Def 8.2 の S → S_perfd（Fil_0 → 余極限の脚）に `e3Perfd_of_complete` を通して一致する。
方針：定義の展開。
規約：—
使われ方：Cor 8.14（universal の欄）の証明で単位を原典の射に読み替える。 -/
theorem e3Unit_of_complete : True := by trivial

/-! ## 欄 h0 -/

/-- 概要：H⁰((S^∧)_perfd) の通常の R 代数の関手 A_R R ⥤ A_R R。
方針：CAlg_R R の頂点の H⁰ は可換環で関手的（`derivedPrismaticCohomology_h0_ring` の perfd 版。要確認：CAlg_R の H⁰ の環の一般の構成が EInfinity にあるか）。
R 代数の構造は `e3Unit` の H⁰。
規約：`H0RingData.ringFunctor`。
使われ方：`e3H0RingData`。 -/
def e3H0RingFunctor : A_R R ⥤ A_R R := sorry

/-- 概要：E3 の `h0`：環の関手、加群構造との同型（`moduleIso`）、射との整合（`map_compat`）、環の単位（`unit`）、単位との整合（`unit_compat`）。
方針：`moduleIso` は「CAlg の H⁰ の底の加群 = D(R) の H⁰」（U と H⁰ の可換性）、`map_compat` は H⁰ の関手性、`unit` は `e3Unit` の H⁰、
`unit_compat` は `underlyingUnit` の構成（`functorHomHomotopy`）と H⁰ の可換性。
規約：`H0RingData R (e3Perfd ≫ cAlgForgetDerived R) (underlyingUnit R e3Unit)`。
使われ方：`PerfectoidizationInterfaceCAlg.h0`。 -/
def e3H0RingData : H0RingData R (e3Perfd p R ≫ cAlgForgetDerived R) (underlyingUnit R (e3Unit p R)) := sorry

/-- 概要：導来 p 完備な S では H⁰((S^∧)_perfd) = H⁰(S_perfd)、かつ S_perfd ∈ D^{≥0}（Lemma 8.4 (c)）なので
H⁰ は S_perfd の「最初の」コホモロジー。離散なら S_perfd 自身。
方針：`e3Perfd_of_complete`、`perfectoidization_coconnective`。
規約：—
使われ方：Cor 8.14（universal）、integral の欄（A8）。 -/
theorem e3H0_of_complete : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
