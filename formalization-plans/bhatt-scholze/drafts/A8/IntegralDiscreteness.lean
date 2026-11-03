-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralDiscreteness（仮。原典 Thm 10.11 と E3 の欄 integral）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.4・§3.3、単位 A8-4。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.Interface
public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
-- 本ファイルは drafts/A8/{AlmostConnectivity,AlmostPurityConnectivity,Stratification}.lean、drafts/A7/{AnimatedPerfectoidization,UniversalProperty}.lean、
-- drafts/A5/{PerfectSiteComparison,WeaklyInitialAndDescent}.lean、drafts/A4/InterfaceFields.lean を import する。

/-!
# 整代数の perfectoid 化の離散性（BS 著者版 Thm 10.11）と E3 の欄 `integral`

## 概要
R perfectoid（完全 prism (A,(d))）、R → S が整写像の p 完備化なら Δ_{S/A,perf} は離散な完全 p 完備 δ-A 代数で、S_perfd は離散な perfectoid 環。
E3 の欄：任意の整 R 代数 S（非完備も）について `IsDiscrete R (e3Perfd S) ∧ IsIntegralPerfectoid (H⁰) p`。

## 方針
filtered 余極限で有限表示有限に帰着（G-A8-9、perfd は filtered 余極限と可換、perfectoid の p 完備化した余極限は perfectoid G-A8-8）、Cor 8.14 で連結性に帰着、
Lemma 10.12 の層別の長さ n で帰納：n = 1 は S_red が有限エタールで perfectoid（G-A8-6）、Perfd_{S/} = Perfd_{S_red/}（D64）；n > 1 は Prop 8.13 と帰納法の仮定で
(S/g_1)_perfd 連結、Lemma 10.5 で g_1-almost 連結性に帰着し、整閉包 T の**完備化 T̂ = completionRing T** と Cor 8.12（W9-III-04：生の T は導来 p 完備とは
限らない）、T への写像を備えた有限表示有限 A_λ の filtered 系（W9-III-06）に Thm 10.9 の連結性（A8-2）、filtered 余極限。

## 規約
S 離散。E3 の欄は S^∧ 経由（D41）。

## 使われ方
`PerfectoidizationInterfaceCAlg.integral`（A9）。環の帰結は既存（`Perfectoidization/Derived/IntegralExistence`）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- 概要：G-A8-6：perfectoid R 上の有限エタール代数 T は perfectoid。
方針：T は p 完備（有限）、T/p は R/p 上エタールで相対 Frobenius が同型なので φ_T 全射、W(T^♭) は W(R^♭) のエタール持ち上げで ker θ_T = d·W(T^♭)。
規約：`IsIntegralPerfectoid`。
使われ方：n = 1。 -/
theorem isIntegralPerfectoid_of_finiteEtale (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T] :
    IsIntegralPerfectoid T p := by sorry -- G-A8-6（A8 の中で証明）

/-- 概要：D64：perfectoid 環は被約なので Perfd_{S/} = Perfd_{S_red/}、よって S_perfd ≃ (S_red)_perfd（Prop 8.5 の極限の形）。
方針：A5-1 `perfectoidization_isLimit_u` と添字圏の同一視。
規約：—
使われ方：n = 1。 -/
theorem perfectoidization_red : True := by trivial

/-- 概要：G-A8-9：整 R 代数は有限表示有限 R 代数の filtered 余極限（R[x]/I を I の有限生成部分イデアル（モニック関係を含む）で近似）。 -/
theorem integral_isFilteredColimit_finitePresentation : True := by trivial

/-- 概要：G-A8-8：perfectoid 環の p 完備化した filtered 余極限は perfectoid で、p^∞ ねじれが有界なので導来 p 完備化は離散。
方針：perfectoid の p ねじれ R[p^∞] = R[p]、Frobenius 全射と ker θ の主性は余極限で保たれる。
規約：—
使われ方：filtered 余極限での帰着。 -/
theorem isIntegralPerfectoid_completedFilteredColimit : True := by trivial

/-- 概要：有限表示有限 S で S_perfd 連結 ⇒ 整 S（p 完備化）で S_perfd 離散・perfectoid、Δ_perf 離散・完全 δ 環。
方針：Cor 8.14（A7-2）、A5-4 `prismaticPerfection_filteredColimit`、上の二つ。
規約：—
使われ方：Thm 10.11。 -/
theorem perfectoidization_discrete_of_finitePresentation_connective : True := by trivial

/-- 概要：n = 1：R → S_red 有限エタール（Lemma 10.12 (2) の普遍同相が同型：p = 0 なら R 完全（perfectoid・被約・Frobenius 全射）で G-A8-5、p 可逆なら構成）
⇒ S_red perfectoid（G-A8-6）⇒ S_perfd ≃ (S_red)_perfd = S_red 離散。
方針：`perfectoidization_red`、`perfectoidization_of_perfectoid`（A7-2）。 -/
theorem perfectoidization_connective_of_stratification_one : True := by trivial

/-- 概要：帰納の段：R_1 := (R/g_1)_perfd（perfectoid、Thm 7.4 で R/g_1 の商）、帰納法の仮定を R_1 → S ⊗_R R_1 に当てて (S ⊗̂_R R_1)_perfd 連結。
perfd の接続は二段（W9-III-03 と同じ）：Q := S ⊗̂^L_R R/g_1 は π_0 Q = S/g_1（有限表示加群なので完備）、Prop 8.5 系 4（`perfectoidization_piZero`）で
Q_perfd ≃ (S/g_1)_perfd、Prop 8.13 で Q_perfd ≃ S_perfd ⊗̂_R R_1；同様に S ⊗̂^L_R R_1 の π_0 = S ⊗_R R_1。離散商と導来テンソルを同一視しない。
層別の条件の底変換（紙 3、W9 で ○）：先に底変換し最後に被約化、p 反転後は同型条件が保たれる。
方針：A7-1 `perfectoidization_relativeTensor`、A5-1 `perfectoidization_piZero`。 -/
theorem perfectoidization_quotient_connective_of_ih : True := by trivial

/-! ## g_1-almost 連結性（W9-III-04〜06 で修復）：整閉包 T、その完備化 T̂、局所化を固定した近似 -/

/-- 概要：B := S_red[1/g_1]（R[1/g_1] 上有限エタール、Lemma 10.12 (2)）、T := R の B における代数的整閉包（原典の S′）。S → S_red → T ⊂ B で **S → T は整**
（T の元を零化する R 係数のモニック式は S 係数でもある）。T ⊂ B であって B ⊂ T ではない。
方針：Mathlib `integralClosure`。
規約：S → T の局所化は同型とは限らない（W9-III-05：S = V[ε]/(ε²)、g_1 = p で S[1/p] に ε が残る。原典が述べるのは arc 層の同型）。
使われ方：以下。 -/
def integralClosureInLocalization (g : R) : Type u := sorry
theorem integralClosureInLocalization_integral (g : R) : True := by trivial

/-- 概要：S → T は `ArcOutside`（g_1 を殺さない p 完備な階数 1 の付値環 W への射は T へ一意に延びる）。
方針：W は被約なので S → W は S_red を通り、局所化で B → Frac(W)、T に制限、T の整性と W の整閉性で像は W に入る。一意性は T[1/g_1] = B と W ⊂ Frac(W)。
G-A8-3″ を S に直接は当てない（局所化は同型でない）。
規約：界面の `ArcOutside`。
使われ方：`arcOutside_completionRing`。 -/
theorem integralClosureInLocalization_arcOutside (g : R) : True := by trivial

/-- 概要：**T は導来 p 完備とは限らない（W9-III-04、致命・修復済み）**。反例：V = ℤ_p[p^{1/p^∞}]^∧、R = V 値の p 進収束列の環（perfectoid、[BMS18, Lemma 3.10 (ii)]）、
g = (p^n)、S = R、T = R の R[1/g] での整閉包。b^(k) = (n mod p^k) ∈ T（有限個の値）は T の p 進 Cauchy 列で、極限 b = (n) は R 上整でない
（部分列 n_ℓ = m + p^ℓ で P_∞ が全ての正整数を零点にもつ）。T ⊂ ∏V で座標射は p 進連続なので T に極限はない。よって T は古典的にも導来的にも p 完備でない。
方針：記録（反例）。生の T の完備性を一般補題にしてはならない。
規約：—
使われ方：設計の根拠。 -/
theorem integralClosure_not_complete_counterexample : True := by trivial

/-- 概要：G-A8-10：T の p 冪ねじれは有界（B は R[1/g_1] 上有限エタールで平坦、perfectoid R の p 冪ねじれは p で殺される（Lemma 2.34 (2)）、部分環 T も）。
よって T の導来 p 完備化は離散で、古典的 p 完備化 T̂ := completionRing T に一致する。
方針：既存の `completionRing`（H⁰(LΛ_p)）と有界ねじれでの離散性（DerivedGeneral/Truncation）。
規約：—
使われ方：Cor 8.12 の前提（T̂ は離散で導来 p 完備）。 -/
def integralClosureCompletion (g : R) : Type u := sorry
theorem integralClosureCompletion_isModuleComplete (g : R) : True := by trivial

/-- 概要：S → T̂ も `ArcOutside`：W は p 完備なので T → W は T̂ → W に一意に延びる（`completion_existsUnique`）。T̂/S の整性は要らない。
方針：`integralClosureInLocalization_arcOutside` と `completionRing` の普遍性。
規約：—
使われ方：Cor 8.12 の適用。 -/
theorem arcOutside_completionRing (g : R) : True := by trivial

/-- 概要：Cor 8.12（A6-4）を **S → T̂** に当てる：S・g_1S は完備（有限表示有限、乗法写像の像）、T̂ は完備（上）、ArcOutside（上）。
fib(S_perfd → T̂_perfd) ≃ fib((S/g_1)_perfd → (T̂/g_1T̂)_perfd) は (R/g_1)_perfd 加群なので S_perfd → T̂_perfd = e3Perfd(T)（D41）は g_1-almost 同型。
商 T̂/g_1T̂ を含む比較は A6 §2.3 の自然同型 F_U ≃ F_{completionRing U}（`homPresheaf_completionRing_iso`）で。
方針：`perfectoidization_excision`、A8-2 `perfectoidization_almostIso_of_localization_iso` と同じ fibre の係数の議論。
規約：原典の暗黙の完備化を明示（D70）。Thm 10.11 の結論・E3 の引用は使わない。
使われ方：`perfectoidization_almostConnective_of_stratification`。 -/
theorem perfectoidization_almostIso_integralClosureCompletion (g : R) : True := by trivial

/-- 概要：G-A8-11（W9-III-06）：T への写像を備えた有限表示有限 R 代数 A_λ の filtered 系で、各 A_λ[1/g_1] ≅ B（R[1/g_1] 代数として）、colim A_λ = T。
方針：B は R[1/g_1] 上有限エタールなので有限表示；生成元の分母を払って T 内に取り、モニック式で A = R[X_1..X_r]/(モニック) → T、A[1/g_1] → B は全射で核は
有限生成、分母を払った関係を加えて A_0 → T、A_0[1/g_1] ≅ B；T の有限個の元 t_j はモニック式と g_1^{N_j} Y_j − a_j で加え、T で零になる有限個の関係も課す。
二対象は A_0 上のテンソルで受け、平行射は差を関係に加えて等化（局所化は常に B）。
規約：A_λ → T の単射性・部分代数であることは要求しない（「有限生成部分代数」では有限表示性が出ない）。
使われ方：各 A_λ に Thm 10.9（A8-2、J = (g_1)）。 -/
theorem exists_finitePresentation_approximation_fixedLocalization (g : R) : True := by trivial

/-- 概要：g_1-almost 連結性：S_perfd → T̂_perfd は g_1-almost 同型（上）、T̂_perfd は g_1-almost 連結：各 A_λ に Thm 10.9 の連結性（A8-2、A_λ[1/g_1] = B は
R[1/g_1] 上有限エタール）、perfd と almost 連結性を p 完備化した filtered 余極限で T̂ に移す（G-A8-8）。
方針：A8-2 `perfectoidization_almostConnective_of_finiteEtaleAway`、`perfectoidization_almostIso_integralClosureCompletion`、
`exists_finitePresentation_approximation_fixedLocalization`、filtered 余極限。
要確認：filtered 余極限で T̂_perfd の almost 連結性へ移す全接続（G-A8-8 と合わせて）は Codex 未確認（W9 第 3 部続き 1）。 -/
theorem perfectoidization_almostConnective_of_stratification : True := by trivial

/-- 概要：Thm 10.11 の連結性：有限表示有限 S で S_perfd 連結（Lemma 10.12 の層別の長さの帰納、Lemma 10.5 で合わせる）。
方針：`exists_finiteEtaleStratification`（A8-3）、上の三つ、A8-1 `connective_iff_almost`。 -/
theorem perfectoidization_connective_of_finitePresentation : True := by trivial

/-- 概要：Thm 10.11：S = (整 R 代数)^∧ で Δ_{S/A,perf} は離散な完全 p 完備 δ-A 代数、S_perfd は離散な perfectoid 環。
方針：上の二つ。
規約：原典の形（D67）。
使われ方：`e3Integral`。 -/
theorem prismaticPerfection_discrete_of_integral (h : Algebra.IsIntegral R S) : True := by trivial
theorem perfectoidization_isIntegralPerfectoid_of_integral (h : Algebra.IsIntegral R S) : True := by trivial

/-- 概要：E3 の `integral`：任意の整 R 代数 S（非完備も）について `IsDiscrete R (e3Perfd S) ∧ IsIntegralPerfectoid (H⁰(e3Perfd S)) p`。
方針：`e3Perfd S = (S^∧)_perfd`（D41、S^∧ = completionRing S = π_0(LΛ_p S)）。Thm 10.11 は原典どおり animated LΛ_p S（整写像の導来 p 完備化）について示し、
Prop 8.5 の系 4（`perfectoidization_piZero`、決定 6）で (LΛ_p S)_perfd ≃ (S^∧)_perfd、`e3H0_of_complete`（A4-3）。
規約：`PerfectoidizationInterfaceCAlg.integral` の型そのまま。
使われ方：A9。 -/
theorem e3Integral (S : A_R R)
    (h : letI : Algebra R S.right := S.hom.hom.toAlgebra; Algebra.IsIntegral R S.right) :
    IsDiscrete R ((e3Perfd p R).app _ (nerveVertex S)) ∧
      IsIntegralPerfectoid ((e3H0RingData p R).ringFunctor.obj S).right p := by
  sorry -- Thm 10.11（A8-1〜A8-4）を待つ

end SerrePositivity.BhattScholze.Perfectoidization.Derived
