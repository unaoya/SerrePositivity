-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.Cohomology（仮。原典 Construction 7.6）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.2・§2.4 (1)、単位 A2-2。基準コミット 972bb7f53。ビルドしない。
module

-- 本ファイルは drafts/A2/AnimatedAlgebra.lean、drafts/A0/PrismaticSite.lean、drafts/Sheaves/CAlgValued.lean、
-- drafts/Shared/CosimplicialEInfinity.lean、drafts/DerivedGeneral/CompletionFunctor.lean を import する。

/-!
# 導来 prismatic コホモロジー（BS 著者版 Construction 7.6）

## 概要
向き付き有界 prism (A,(d))、k = A/d。多項式 k 代数 P に Δ_{P^∧/A}（A0 の Not 4.16 の CAlg 版）を対応させる関手 Δ_0 : N(Poly k) → 𝒱
（𝒱 = (p,d) 完備な E∞-A 代数の ∞ 圏）を、P_Σ(N(Poly k))（単体的可換 k 代数）へ sifted 余極限を保つように延長したものを
導来 prismatic コホモロジー R ↦ Δ_{R/A} とする（HTT 5.5.8.15）。φ_A 半線形な Frobenius も Poly 上の φ の延長。
(1) 多項式代数での値は元の Δ（充満忠実な包含に沿う Kan 延長の制限）。

## 方針
A0 の `prismaticCohomology`（D(A) 値）を Sheaves/CAlgValued の `derivedGlobalSectionsCAlg` で CAlg 値にし、Čech–Alexander 模型の
Tot_{E∞}（Shared/CosimplicialEInfinity）と一致させる。延長は A2-1 の `exists_siftedExtension`。値の (p,d) 完備化は
DerivedGeneral/CompletionFunctor の反射（CAlg 版は要確認）。

## 規約
値は CAlg_A を正（a2-design §6 の 1）。D(A) 値は忘却 U で。始域は P_Σ 全体（D32）。離散 R の Δ_R は `discreteToAnimated` で。

## 使われ方
A2-3（HT filtration）、A2-4、A3（Lemma 7.7：Δ_R 離散なら δ 環）、A4（Def 8.2：Frobenius 余極限）、A5・A7・A8、E3 の `perfd`。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## 値の圏 -/

/-- 概要：𝒱 := (p,d) 導来完備な E∞-A 代数の充満部分 ∞ 圏（CAlg_A の中）。
方針：DerivedGeneral/CompletionFunctor の `IsDerivedComplete` を U で引き戻した充満部分複体。
規約：sifted 余極限は CAlg_A で取って完備化（反射）。
使われ方：Δ の値。 -/
def CompleteCAlg : SSet.{u + 1} := sorry -- fullSubcomplex of CAlg_R A on (fun x => IsDerivedComplete A p P.generator (U x))

/-- 概要：𝒱 は sifted 余極限をもつ（CAlg_A の sifted 余極限の完備化）。
方針：G-A2-3（完備化は反射）、G-A2-4（CAlg_A の sifted 余極限、HA 3.2.3.1）。
規約：—
使われ方：HTT 5.5.8.15 の仮定。 -/
theorem completeCAlg_siftedColimits : True := by trivial

/-! ## 多項式代数上の Δ_0（CAlg 値） -/

/-- 概要：多項式 k 代数 P = k[X_1,…,X_n] の p 完備化 P^∧（A0 の `affineAlgebra`／`cechAlexanderAffine` の R）。
方針：design-status (B) の決定：一変数 p 進完備化の H⁰。
規約：Poly k の対象 ⟨n⟩ に対して。
使われ方：Δ_0。 -/
def polyCompletion (n : ℕ) : Type u := sorry

/-- 概要：Δ_0(P) := Δ_{P^∧/A}（Not 4.16、CAlg 値）：平坦位相の site (P^∧/A)_Δ 上の O_Δ の CAlg 値 RΓ。
方針：A0 の `structurePresheaf` を `ringPresheafToCAlg` で CAlg 値にし、`derivedGlobalSectionsCAlg`。(p,d) 完備（Čech–Alexander の各項が完備、
極限で閉じる）。
規約：層化と presentable 性は入力（S4・G12）。
使われ方：Kan 延長の始域の値。 -/
def prismaticCohomologyCAlg (n : ℕ) : True := trivial -- 要確認：(CompleteCAlg P) _⦋0⦌ の形に

/-- 概要：Δ_0 は Čech–Alexander 模型の Tot_{E∞}（E∞ 代数として）。
方針：Cor 3.12 の CAlg 版（`isSheaf_iff_forget`）、脚注 10 の CAlg 版（`derivedGlobalSectionsCAlg_eq_totEInfinity`）。
規約：Rem 4.19 の小さい模型でも大きい模型でもよい。
使われ方：A1 の模型の環構造との一致（D27）、Δ_0 の関手性の具体形。 -/
theorem prismaticCohomologyCAlg_eq_totEInfinity (n : ℕ) : True := by trivial

/-- 概要：Δ_0 : N(Poly k) → 𝒱（多項式代数の射 P → P′ についての関手性）。
方針：k 代数の射 P → P′ は P′^∧ 上の site から P^∧ 上の site への関手（prism B と R′ → B/dB から R → R′ → B/dB）を誘導し、RΓ の関手性
（S2 の `derivedGlobalSections_map` の CAlg 版）。∞ 関手としての coherent 性は、Čech–Alexander 模型の厳密な関手性（大きい模型、A0 の
Constr 4.18）から nerve で。
規約：持ち上げた形状 `uliftFunctor.obj (polyNerve k)` から。
使われ方：Kan 延長の入力。
要確認：site の関手性の coherent な形（1 圏の関手の nerve で足りる：Poly は 1 圏、𝒱 の値は模型の Tot_{E∞} の厳密な関手性）。 -/
def prismaticCohomologyPolyFunctor :
    (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ CompleteCAlg P := sorry

/-- 概要：Poly 上の Frobenius φ : Δ_0 → φ_{A*} ∘ Δ_0（φ_A 半線形）。
方針：A0 の `structurePresheafFrobenius` の CAlg 版と RΓ の関手性。
規約：φ_{A*} はスカラー制限（CAlg_A 上の関手、G-A2-5）。
使われ方：Frobenius の Kan 延長。 -/
def prismaticFrobeniusPoly : True := trivial

/-! ## 左 Kan 延長（Construction 7.6） -/

/-- 概要：導来 prismatic コホモロジー R ↦ Δ_{R/A}：Δ_0 の sifted 余極限保存な延長 P_Σ(N(Poly k)) → 𝒱（HTT 5.5.8.15）。
方針：A2-1 の `exists_siftedExtension` で選ぶ。
規約：選択を含む（sifted 余極限保存な延長は同値を除いて一意）。
使われ方：以下の全て。 -/
def derivedPrismaticCohomology : AnimatedAlgebra (A ⧸ P.ideal) ⟶ CompleteCAlg P :=
  sorry -- Classical.choose (exists_siftedExtension … (prismaticCohomologyPolyFunctor P))

theorem derivedPrismaticCohomology_preservesSifted : True := by trivial

/-- 概要：(1)：多項式代数 j(P) での値は Δ_0(P)（充満忠実な包含に沿う Kan 延長の制限）。
方針：HTT 4.3.2.17（充満忠実な関手に沿う左 Kan 延長は元の関手を復元）、`exists_siftedExtension` の仕様。
規約：同値（頂点の同型）。
使われ方：A0・A1 の結果を導来版へ。 -/
theorem derivedPrismaticCohomology_poly (n : ℕ) : True := by trivial

/-- 概要：Frobenius φ : Δ → φ_{A*} ∘ Δ（Poly 上の φ の Kan 延長）。
方針：φ_{A*} は CAlg_A の **sifted** 余極限を保つ（全余極限ではない：初期対象は保たれない、W9-I-27）ので、両辺とも sifted 余極限保存。
完備版では (p,d) と (p,φ(d)) が同じ位相なのでスカラー制限は完備対象を保つ。Poly 上の自然変換の延長（HTT 5.5.8.15 の関手 ∞ 圏の同値）。
規約：—
使われ方：A4（Def 8.2 の φ 余極限）。 -/
def derivedPrismaticFrobenius : True := trivial

/-- 概要：離散 k 代数 R の Δ_R := Δ ∘ discreteToAnimated。E3 の `perfd` の材料。
方針：A2-1 の `discreteToAnimated`。
規約：E3 の始域 `algebraNerve` と同じ添字。
使われ方：A4。 -/
def derivedPrismaticCohomologyDiscrete :
    nerve (Under (CommRingCat.of (A ⧸ P.ideal))) ⟶ CompleteCAlg P :=
  discreteToAnimated (A ⧸ P.ideal) ≫ derivedPrismaticCohomology P

/-- 概要：D(A) 値の Δ（忘却）。A0 の `prismaticCohomology` と多項式代数で一致（`forget_derivedGlobalSections`）。
方針：U で後合成。
規約：—
使われ方：E3 の D(R) 版、HT filtration（D(A) で述べる）。 -/
def derivedPrismaticCohomologyDerived : True := trivial

/-- 概要：H⁰(Δ_R) の環構造（CAlg 値なので H⁰ は可換環）と、A3 の Lemma 7.7(1) の準備（離散なら δ 構造）。
方針：E∞ 代数の H⁰ は可換環（EInfinity の H⁰ の環構造、E3 の `H0RingData` と同じ）。
規約：—
使われ方：A3、E3 の `h0`。 -/
theorem derivedPrismaticCohomology_h0_ring : True := by trivial

end SerrePositivity.BhattScholze.Prismatic
