-- 将来の置き場所：SerrePositivity.BhattScholze.Almost.AlmostPurityConnectivity（仮。原典 Thm 10.9 の J-almost 連結性の部分）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.2・§3.2、単位 A8-2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Etale
public import SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootPerfectoid
-- 本ファイルは drafts/A8/AlmostConnectivity.lean、drafts/A6/{Excision,SheafOfSetsExcision}.lean、drafts/A7/{AnimatedPerfectoidization,UniversalProperty}.lean を import する。

/-!
# almost purity の連結性の部分（BS 著者版 Thm 10.9 の J-almost 版のうち連結性、D63）

## 概要
R perfectoid、S **有限表示有限** R 代数（原典どおり。W9-III-01：有限だけでは導来 p 完備にならない）、f_1,…,f_r ∈ R、J = (f_1,…,f_r)、
各 i で S[1/f_i] が R[1/f_i] 上有限エタール ⇒ S_perfd は J-almost 連結。

## 方針
原典の証明の (1)(2)：一つの生成元 f に帰着（A8-1）；Thm 7.14 で基底を絶対整閉 R′ に（Prop 8.13 と A8-1 の反映）；絶対整閉環上の有限エタール代数は
主開集合で分裂（既存 `finiteEtaleAway_exists_finite_cover`）ので生成元を細分して S[1/g] ≅ R[1/g]^r；S′ := S と R^r の生成する R[1/g]^r の部分代数に
Cor 8.12 を二回当てて S_perfd ≈_g S′_perfd ≈_g (R^r)_perfd = R^r（離散）。(3)(4)（Σ_r Galois 閉包、Prop 10.8 [And18b]、次数の開閉分解）は使わない。

## 規約
S は有限表示有限なので R 加群として有限表示、導来 p 完備（既存 `isModuleComplete_of_finitePresentation`、脚注 19）。「有限なら導来 p 完備」は偽
（W9-III-01：R = ∏V、M = R/⊕V は巡回だが R[1/p] → M が非零）。J-almost は A8-1。比較環 S′ の完備性は構成固有の計算（G-A8-3′）。

## 使われ方
Thm 10.11 の g_1-almost 連結性（A8-4）。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.BhattScholze.Almost

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.FinitePresentation R S]

/-- 概要：G-A8-3（W9-III-01 で訂正）：有限表示有限 R 代数 S は R 加群として有限表示なので導来 p 完備（既存
`HomologicalAlgebra/DerivedCompletion/FinitePresentationComplete.lean` の `isModuleComplete_of_finitePresentation`）。
**「有限なら導来 p 完備」は偽**：V = ℤ_p[p^{1/p^∞}]^∧、R = ∏V（perfectoid）、I = ⊕V、M = R/I で x_k = [(0,…,0,1,p,p²,…)] は p x_{k+1} = x_k、x_0 ≠ 0、
R[1/p] → M が非零。S = R × M は有限 R 代数で D(e_0) 上は自明な有限エタールだが非完備。
方針：既存。
規約：—
使われ方：Cor 8.12 の前提（S）。 -/
theorem finitePresentation_isModuleComplete : True := by trivial

/-- 概要：主イデアル (g) ⊂ R、gS ⊂ S、gR^r は完備な加群上の乗法写像の像（= ker(標的 → coker)）なので導来 p 完備。
方針：既存 `ModuleClosure.lean` の `isModuleComplete_ker`・`isModuleComplete_coker`。
規約：—
使われ方：Cor 8.12 の前提（I = (g)）。 -/
theorem span_singleton_isModuleComplete (g : R) : True := by trivial

/-- 概要：§3.2 の 2：Thm 7.14（既存、絶対整閉 `IsAbsolutelyIntegrallyClosed` の p 完備忠実平坦な perfectoid 拡大 R → R′）で、主張を R′ 上に移してよい
（(S ⊗̂_R R′)_perfd = S_perfd ⊗̂_R R′、A8-1 の反映）。
方針：`CompatibleRootPerfectoid`（要確認：絶対整閉を結論する形の名前）、A7-1、A8-1。
規約：—
使われ方：`perfectoidization_almostConnective_of_finiteEtaleAway`。 -/
theorem almostConnective_of_aic_baseChange : True := by trivial

/-- 概要：§3.2 の 3：R 絶対整閉、S[1/f] が R[1/f] 上有限エタールなら、有限個の h_j で D(f) = ∪ D(f h_j)、各 j で S[1/(f h_j)] ≅ R[1/(f h_j)]^{r_j}。
方針：既存 `IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_cover`（要確認：形）。
規約：—
使われ方：生成元の細分。 -/
theorem exists_principal_splitting_cover (f : R) : True := by trivial

/-- 概要：§3.2 の 4：S[1/g] ≅ R[1/g]^r のとき、S′ := S と R^r の生成する R[1/g]^r の部分 R 代数。S → S′ と R^r → S′ は g の外で同型。
G-A8-3′（W9-III-01 の修復計算）：標準冪等元 e_j と S の有限個の R 加群生成元 s_a について S′ は R 加群として有限個の e_j s_a で生成される
（Σ_j e_j·image(S) は乗法で閉じ、両方の像を含む）ので有限 R 加群、S → S′・R^r → S′ は整。
方針：部分代数の生成元の計算、局所化の計算（紙 2）。
規約：S′ は有限表示とは限らない。
使われ方：Cor 8.12 の適用。 -/
def trivialCoverComparison (g : R) (r : ℕ) : Type u := sorry
theorem trivialCoverComparison_finite (g : R) (r : ℕ) : True := by trivial
theorem trivialCoverComparison_integral (g : R) (r : ℕ) : True := by trivial
theorem trivialCoverComparison_localization_iso (g : R) (r : ℕ) : True := by trivial

/-- 概要：G-A8-3′：S′ は導来 p 完備（有限表示性なしに、構成固有の計算で）。
方針：R は被約（perfectoid）なので ann(g^N) = ann(g)、R の R[1/g] での像 R̄ = R/ann(g) は導来 p 完備（乗法写像の核の余核、`isModuleComplete_ker`・`_coker`）。
生成元 e_j s_a の分母を払う N で g^N S′ ⊂ R̄^r（`isModuleComplete_pi`）。g は R[1/g]^r で単元なので S′ ≅ g^N S′（R 加群同型）、g^N S′ は有限自由 R 加群から R̄^r への
写像の像で導来 p 完備。
規約：—
使われ方：Cor 8.12 の前提（S′）。 -/
theorem trivialCoverComparison_isModuleComplete (g : R) (r : ℕ) : True := by trivial

/-- 概要：G-A8-3″（W9-III-02 で訂正）：**整**写像 S → S′ で局所化 S[1/g] → S′[1/g] が同型なら `ArcOutside`（g の像が**非零**（可逆とは限らない）な付値環 V への
射 S → V は S′ へ一意に延びる）。整性なしでは偽：S = V = F_p[t^{1/p^∞}] の t 進完備付値環、S′ = V[1/t]、g = t で id : S → V は S′ に延びない。
方針：g ↦ 非零なので S → V は S[1/g] = S′[1/g] → Frac(V) を与える。S′ の元は S 上整だから像は V 上整、付値環 V は Frac(V) で整閉なので像は V に入る。
一意性は Frac(V) への射の一意性と V ↪ Frac(V)。
規約：界面の `ArcOutside`（Derived/Interface.lean の条件は ¬(I ≤ ker k)、すなわち g の像が非零）。
使われ方：Cor 8.12 の前提（S → S′ と R^r → S′）。 -/
theorem arcOutside_of_integral_of_localization_iso : True := by trivial

/-- 概要：Cor 8.12（A6-4）から：S → S′ が整で g の外で同型、S・S′・(g) が導来 p 完備なら S_perfd → S′_perfd は (g)-almost 同型
（fib ≃ fib((S/g)_perfd → (S′/g)_perfd) は (R/g)_perfd 上の射の fibre なので (R/g)_perfd 加群、(g)_perfd がコホモロジーを零化）。
方針：`perfectoidization_excision`（前提は `finitePresentation_isModuleComplete`・`trivialCoverComparison_isModuleComplete`・`span_singleton_isModuleComplete`・
`arcOutside_of_integral_of_localization_iso`）、(S/g)_perfd が (R/g)_perfd 加群（関手性）、J_perfd は (R/J)_perfd を殺す。
規約：前提（整・完備）を明示する。局所化の同型だけでは足りない（W9-III-01・02）。
使われ方：比較。 -/
theorem perfectoidization_almostIso_of_localization_iso (g : R) : True := by trivial

/-- 概要：(R^r)_perfd = R^r（G-A6-2 の有限積と `perfectoidization_of_perfectoid`）、離散。 -/
theorem perfectoidization_pow_eq (r : ℕ) : True := by trivial

/-- 概要：Thm 10.9 の J-almost 連結性（D63）：S 有限表示有限 R 代数（原典どおり、W9-III-01）、各 i で S[1/f_i] が R[1/f_i] 上有限エタール ⇒ S_perfd は (f_1,…,f_r)-almost 連結。
方針：A8-1 で一つの f に、`almostConnective_of_aic_baseChange`、`exists_principal_splitting_cover` と √ 不変で g に、
`perfectoidization_almostIso_of_localization_iso` を S → S′ と R^r → S′ に、`perfectoidization_pow_eq`。
規約：—
使われ方：Thm 10.11（A8-4 の 5）。 -/
theorem perfectoidization_almostConnective_of_finiteEtaleAway {r : ℕ} (f : Fin r → R)
    (hf : ∀ i, True) : True := by trivial -- 要確認：仮定「S[1/f_i] は R[1/f_i] 上有限エタール」の述べ方（`Algebra.Etale` と `Module.Finite` の局所化）

end SerrePositivity.BhattScholze.Almost
