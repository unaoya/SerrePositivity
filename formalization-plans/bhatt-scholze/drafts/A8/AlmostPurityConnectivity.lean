-- 将来の置き場所：SerrePositivity.BhattScholze.Almost.AlmostPurityConnectivity（仮。原典 Thm 10.9 の J-almost 連結性の部分）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.2・§3.2、単位 A8-2。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.IntegralPerfectoidization.Completion.IntegralClosureCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates
public import SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison

public import SerrePositivity.EInfinity.Interface.Theory
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Etale
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberTriangle
public import SerrePositivity.BhattScholze.Andre.Transfinite.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation
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
open CategoryTheory SSet
open scoped Simplicial TensorProduct
attribute [local instance] HasDerivedCategory.standard

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Almost

open SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.BhattScholze.Perfectoidization.Derived

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

abbrev perfdModule (U : A_R R) : DVertex R :=
  (perfectoidizationFunctor (E := E) p R hR ≫ E.forget R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)

/-- 指定された離散代数の射の perfd の fibre。Cor 8.12 の比較を D(R) で読む。 -/
def perfdMapFiber {U V : A_R R} (f : U ⟶ V) : DVertex R := by
  let e := ((nerve.edgeMk f).map (perfectoidizationFunctor (E := E) p R hR ≫ E.forget R)).toTruncated
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (e.map ((SSet.truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))
  exact (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).inverse.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardFiberDerivedTriangle k).obj₁)).pt



include hR in
/-- 概要：G-A8-3（W9-III-01 で訂正）：有限表示有限 R 代数 S は R 加群として有限表示なので導来 p 完備（既存
`HomologicalAlgebra/DerivedCompletion/FinitePresentationComplete.lean` の `isModuleComplete_of_finitePresentation`）。
**「有限なら導来 p 完備」は偽**：V = ℤ_p[p^{1/p^∞}]^∧、R = ∏V（perfectoid）、I = ⊕V、M = R/I で x_k = [(0,…,0,1,p,p²,…)] は p x_{k+1} = x_k、x_0 ≠ 0、
R[1/p] → M が非零。S = R × M は有限 R 代数で D(e_0) 上は自明な有限エタールだが非完備。
方針：既存。
規約：—
使われ方：Cor 8.12 の前提（S）。 -/
theorem finitePresentation_isModuleComplete [Module.Finite R S] [Algebra.FinitePresentation R S] :
    IsModuleComplete R (p : R) (ModuleCat.of R S) := by
  letI := Module.FinitePresentation.of_finite_of_finitePresentation R S
  exact isModuleComplete_of_finitePresentation R (p : R) (hR.isModuleComplete R p) (ModuleCat.of R S)

/-- 概要：主イデアル (g) ⊂ R、gS ⊂ S、gR^r は完備な加群上の乗法写像の像（= ker(標的 → coker)）なので導来 p 完備。
方針：既存 `ModuleClosure.lean` の `isModuleComplete_ker`・`isModuleComplete_coker`。
規約：—
使われ方：Cor 8.12 の前提（I = (g)）。 -/
theorem span_singleton_isModuleComplete (g : R)
    (hS : IsModuleComplete R (p : R) (ModuleCat.of R S)) :
    IsModuleComplete R (p : R) (ModuleCat.of R (Ideal.span {algebraMap R S g})) := by
  sorry -- S 上の g 倍の像。完備加群の核・余核の閉性。S=R、R^r でも同じ

/-- 概要：§3.2 の 2：Thm 7.14（既存、絶対整閉 `IsAbsolutelyIntegrallyClosed` の p 完備忠実平坦な perfectoid 拡大 R → R′）で、主張を R′ 上に移してよい
（(S ⊗̂_R R′)_perfd = S_perfd ⊗̂_R R′、A8-1 の反映）。
方針：`Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`、A7-1、A8-1。
規約：—
使われ方：`perfectoidization_almostConnective_of_finiteEtaleAway`。 -/
theorem almostConnective_of_aic_baseChange [Module.Finite R S] [Algebra.FinitePresentation R S] (g : R)
    (h : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] (hR' : IsIntegralPerfectoid R' p),
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) R' → IsAbsolutelyIntegrallyClosed R' →
        IsAlmostConnective p R' hR' (Ideal.span {algebraMap R R' g})
          (perfdModule (E := E) p R' hR' (ofAlgebra R' (R' ⊗[R] S)))) :
    IsAlmostConnective p R hR (Ideal.span {g}) (perfdModule (E := E) p R hR (ofAlgebra R S)) := by
  sorry -- exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed と Prop 8.13、
        -- 完備平坦な底変換で K⊗̂M の連結性を反映する。π₀ の有限表示有限代数へは Prop 8.5 系4

/-- 概要：§3.2 の 3：R 絶対整閉、S[1/f] が R[1/f] 上有限エタールなら、有限個の h_j で D(f) = ∪ D(f h_j)、各 j で S[1/(f h_j)] ≅ R[1/(f h_j)]^{r_j}。
方針：既存 `IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_cover` の有限族の分子を使う。
規約：—
使われ方：生成元の細分。 -/
theorem exists_principal_splitting_cover [Module.Finite R S] (hA : IsAbsolutelyIntegrallyClosed R)
    (f : R) (hf : FiniteEtaleAway R S f) :
    ∃ (m : ℕ) (g : Fin m → R), (Ideal.span (Set.range (fun i => f * g i))).radical =
      (Ideal.span {f}).radical ∧ ∀ i, let a := f * g i
        letI := GenericEtale.awayAlgebra R S a
        ∃ r : ℕ, Nonempty (Localization.Away (algebraMap R S a) ≃ₐ[Localization.Away a]
          (Fin r → Localization.Away a)) := by
  sorry -- finiteEtaleAway_exists_finite_cover の有限族の分子を取る。f^N の所属から主開を被覆

/- G-A8-3′ の完備性は本体 Almost/FiniteEtaleComparison.lean の
trivialCoverComparison_isModuleComplete を直接使う。 -/
/-- 概要：G-A8-3″（W9-III-02 で訂正）：**整**写像 S → S′ で局所化 S[1/g] → S′[1/g] が同型なら `ArcOutside`（g の像が**非零**（可逆とは限らない）な付値環 V への
射 S → V は S′ へ一意に延びる）。整性なしでは偽：S = V = F_p[t^{1/p^∞}] の t 進完備付値環、S′ = V[1/t]、g = t で id : S → V は S′ に延びない。
方針：g ↦ 非零なので S → V は S[1/g] = S′[1/g] → Frac(V) を与える。S′ の元は S 上整だから像は V 上整、付値環 V は Frac(V) で整閉なので像は V に入る。
一意性は Frac(V) への射の一意性と V ↪ Frac(V)。
規約：界面の `ArcOutside`（Derived/Interface.lean の条件は ¬(I ≤ ker k)、すなわち g の像が非零）。
使われ方：Cor 8.12 の前提（S → S′ と R^r → S′）。 -/
theorem arcOutside_of_integral_of_localization_iso {U V : A_R R} (f : U ⟶ V) (g : U.right)
    (hint : f.right.hom.IsIntegral) (hloc : Function.Bijective (Localization.awayMap f.right.hom g)) :
    ArcOutside R p f (Ideal.span {g}) := by
  sorry -- existsUnique_valuation_extension_of_integral_away_bijective。g≠0 で Frac(W) へ送り整閉性で W に戻す

/-- 概要：Cor 8.12（A6-4）から：S → S′ が整で g の外で同型、S・S′・(g) が導来 p 完備なら S_perfd → S′_perfd は (g)-almost 同型
（fib ≃ fib((S/g)_perfd → (S′/g)_perfd) は (R/g)_perfd 上の射の fibre なので (R/g)_perfd 加群、(g)_perfd がコホモロジーを零化）。
方針：`perfectoidization_excision`（前提は `finitePresentation_isModuleComplete`・`trivialCoverComparison_isModuleComplete`・`span_singleton_isModuleComplete`・
`arcOutside_of_integral_of_localization_iso`）、(S/g)_perfd が (R/g)_perfd 加群（関手性）、J_perfd は (R/J)_perfd を殺す。
規約：前提（整・完備）を明示する。局所化の同型だけでは足りない（W9-III-01・02）。
使われ方：比較。 -/
theorem perfectoidization_almostIso_of_localization_iso {U V : A_R R} (f : U ⟶ V) (g : R)
    (hint : f.right.hom.IsIntegral) (hloc : Function.Bijective (Localization.awayMap f.right.hom (U.hom.hom g)))
    (hU : IsModuleComplete U.right (p : U.right) (ModuleCat.of U.right U.right))
    (hV : IsModuleComplete V.right (p : V.right) (ModuleCat.of V.right V.right))
    (hI : IsModuleComplete U.right (p : U.right) (ModuleCat.of U.right (Ideal.span {U.hom.hom g}))) :
    IsJAlmostZero p R hR (Ideal.span {g}) (perfdMapFiber (E := E) p R hR f) := by
  sorry -- ArcOutside を上で得て Cor 8.12。商の fibre は (R/g)_perfd 加群

/-- 概要：(R^r)_perfd = R^r（G-A6-12 の有限積と `perfectoidization_of_perfectoid`）、離散。 -/
def perfectoidization_pow_eq (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (perfdValue (E := E) p R hR (ofAlgebra R (Fin r → R)))
      ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R (Fin r → R)))) := by
  sorry -- G-A6-12 と perfectoidization_of_perfectoid。積環の単位同型の逆（r=0 も含む）

/-- 概要：Thm 10.9 の J-almost 連結性（D63）：S 有限表示有限 R 代数（原典どおり、W9-III-01）、各 i で S[1/f_i] が R[1/f_i] 上有限エタール ⇒ S_perfd は (f_1,…,f_r)-almost 連結。
方針：A8-1 で一つの f に、`almostConnective_of_aic_baseChange`、`exists_principal_splitting_cover` と √ 不変で g に、
`perfectoidization_almostIso_of_localization_iso` を S → S′ と R^r → S′ に、`perfectoidization_pow_eq`。
規約：—
使われ方：Thm 10.11（A8-4 の 5）。 -/
theorem perfectoidization_almostConnective_of_finiteEtaleAway [Module.Finite R S] [Algebra.FinitePresentation R S]
    {r : ℕ} (f : Fin r → R) (hf : ∀ i, FiniteEtaleAway R S (f i)) :
    IsAlmostConnective p R hR (Ideal.span (Set.range f)) (perfdModule (E := E) p R hR (ofAlgebra R S)) := by
  sorry -- 根基不変性・生成元判定で主開に帰着し、AIC 上で二つの Cor 8.12 と積の離散性を使う

end SerrePositivity.BhattScholze.Almost
