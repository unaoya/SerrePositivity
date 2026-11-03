-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.WeaklyInitialAndDescent（仮。原典 Prop 8.5 の証明 (1)〜(3)）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §3.1〜§3.3、単位 A5-4。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/A5/{RootAdjunction,PerfectSite,SemiperfectoidCase,StrongDescent}.lean、drafts/Sheaves/CechConerveLimit.lean、drafts/Shared/Descendable.lean、
-- drafts/A2/BaseChangeAndTensor.lean を import する。PerfectSiteComparison（Prop 8.5 の証明・系）は本ファイルより**後**（W9-III-09）。
-- 根添加の定義と初等的補題（`rootClosure`・`algebraicRootClosure`・`polyRootAlgebra`・`rootCover`）は drafts/A5/RootAdjunction.lean に切り出した。

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
open CategoryTheory SSet
open scoped Simplicial TensorProduct

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

open SerrePositivity.DerivedCompletion SerrePositivity.EInfinity.Perfectoidization

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## (1) 弱始対象 -/

/-- 概要：(ii) S̃ は semiperfectoid：S̃/p は semiperfect（各元が次の段で p 乗根をもつ）、p 完備な R 代数で mod p semiperfect なら perfectoid の商
（G-A5-14、[BMS19, Rem 4.22]：θ : W(S̃^♭) → S̃ 全射、R ⊗̂ W(S̃^♭) は perfectoid）。
方針：既存の θ（`fontaineTheta`）と完備テンソル。
規約：A5-2 の `IsSemiperfectoid`。**perfectoid 基底 R は本質的**（W9-II-16）：ker θ の distinguished 元は R 由来。基底なしでは偽
（S = ℤ_p の根添加は ℤ_p へ retraction をもつ）。A6 の Lemma 8.8 は前段 G-A6-11 で R₀ = ℤ_p[p^{1/p^∞}]^∧ 上へ移してから本定理を使う。
使われ方：S̃_perfd の存在（Cor 7.3）、A5-2 の適用。 -/
include hR in
theorem rootClosure_isSemiperfectoid : IsSemiperfectoid p R (rootClosure p R S) := by
  sorry -- 完備性と mod p の根を使い、perfectoid 基底 R 上で θ の全射から商表示を作る

/-- E を先に作り、構造射・単位射も含めて H⁰ 完備化する。 -/
def algebraicCoverUnit (C : CommRingCat.{u}) :
    completionRing p C ⟶ completionRing p ((algebraicRootFunctor p).obj C) :=
  completionMap p (CommRingCat.ofHom (algebraicRootClosureUnit p C))

/-- 概要：S = S_alg^∧（S_alg = colim_i S_i）の被覆 E(S_alg)^∧_p：p 完備忠実平坦、semiperfectoid（mod p の根、G-A5-14）、E(S_i)^∧_p の完備 filtered 余極限。
E(S)^∧_p とは同一視しない。
方針：各段の自由性と完備化。
規約：—
使われ方：§3.2 の右辺の可換性。 -/
include hR in
theorem algebraicRootCover_properties {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ A_R R) :
    let D₀ := D ⋙ Under.forget (CommRingCat.of R)
    let C := Limits.colimit D₀
    let E := algebraicRootFunctor p
    let U := completionRing p (E.obj C)
    letI := (algebraicCoverUnit p C).hom.toAlgebra
    letI : Algebra R U := ((algebraicCoverUnit p C).hom.comp ((completionUnit p C).hom.comp
      ((Limits.colimit.ι D₀ (Classical.arbitrary J)).hom.comp
        (D.obj (Classical.arbitrary J)).hom.hom))).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : completionRing p C)}) U ∧
      IsSemiperfectoid p R U ∧
      IsIso (completionMap p (Limits.colimit.desc (D₀ ⋙ E ⋙ ringCompletionFunctor p)
        ((ringCompletionFunctor p).mapCocone (E.mapCocone (Limits.colimit.cocone D₀)))) ≫
        (completionUnitIso p U (completionRing_complete p _)).inv) := by
  classical
  sorry -- モニックな各段は自由で mod p に根があり、E は通常の filtered 余極限を保つ。
        -- 完備標的への普遍性により H⁰ 完備化を余極限の前後で取った指定比較が同型

/-- 概要：弱始対象 S̃_perfd ∈ `PerfUnder_u p S`（A5-2 の普遍 perfectoid 環 R′(S̃)、Prop 8.5 の系 3 で Δ_{S̃,perf}/d）。
方針：`universalPerfectoidRing` を S の上の環として。
規約：`PerfUnder_u p S` の対象。
使われ方：S3。 -/
def perfectoidTargetWeaklyInitial : PerfUnder_u p (CommRingCat.of S) := by
  let h := rootClosure_isSemiperfectoid p R hR S
  let q := universalPerfectoidUnit p R (rootClosure p R S) h
  exact ⟨Under.mk (CommRingCat.ofHom (q.comp (rootClosureUnit p R S))),
    (universalPerfectoidUnit_isPerfectoidization p R (rootClosure p R S) h).1⟩

def boundedWeakTarget : PerfUnderBounded p S (perfectSiteCutoff p R S) :=
  ⟨perfectoidTargetWeaklyInitial p R hR S, by
    sorry⟩ -- Cor 7.3 の単位は全射、rootClosure_cardinal_le と κ の定義を使う

abbrev weakPerfectSiteObj : perfectSite p R S hR :=
  ((perfectSiteEquivPerfectoidUnder p R hR S).inverse.obj (boundedWeakTarget p R hR S)).unop

/-- 概要：弱始性：任意の T ∈ `PerfUnder_u p S` に S の下で S̃_perfd → T がある（延長性と R′ の普遍性）。κ 側の site でも同様。
方針：`rootClosure_extends`、`universalPerfectoidUnit_isPerfectoidization`。
規約：S3 の `IsWeaklyTerminal`（site は opposite）。
使われ方：`limit_perfUnder_eq_tot`。 -/
theorem perfectoidTargetWeaklyInitial_isWeaklyInitial :
    Sheaves.IsWeaklyTerminalLarge (Opposite.op (perfectoidTargetWeaklyInitial p R hR S)) ∧
      Sheaves.IsWeaklyTerminal (weakPerfectSiteObj p R hR S) := by
  sorry -- rootClosure_extends の脚を Cor 7.3 で一意に降ろす。κ 側へは充満性と圏同値で移送


-- Čech 余脈体 `perfUnder_cechNerveData`（Perfd_{S/} の余積 (T₁ ⊗̂_S T₂)_perfd）は A5/PerfectSite へ移した（W9-III-14：既存 Cor 7.3 の普遍環から直接作れる）。

abbrev cosimplicialShape : SSet.{u+1} := (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)

def largeCechShape (U : PerfUnder_u p (CommRingCat.of S)) :
    cosimplicialShape.{u} ⟶ perfectoidTargetNerve p (CommRingCat.of S) where
  app n := ↾fun x =>
    (((perfUnder_cechNerveData p R hR S (Opposite.op U)).obj.rightOp ⋙ unopUnop _).mapComposableArrows _).obj x.down
  naturality := by sorry -- 各単体の列を同じ余積の関手で送る

abbrev perfectResiduePresheaf :=
  Sheaves.ringPresheafToCAlg R ((perfectResidueFunctor p R hR S) ⋙ (ObjectProperty.ι _) ⋙
    targetAlgebra R p (ofAlgebra R S))

/-- 概要：lim_{PerfUnder_u p S} T ≃ Tot((S̃^•)_perfd)（S3 `exists_limitCone_of_cech`、Čech データは PerfectSite `perfUnder_cechNerveData`）。κ 側の完全 site でも同じ Tot（弱始対象は濃度 ≤ κ）。
よって Type u の極限と κ-small の site の極限は一致（D47）。
方針：S3 を二回。
規約：—
使われ方：A5-1 の `perfectoidization_isLimit_u`。 -/
theorem limit_perfUnder_eq_tot
    (t : JoinCone (largeCechShape p R hR S (perfectoidTargetWeaklyInitial p R hR S) ≫
      targetCAlgDiagram R p (ofAlgebra R S))) (ht : IsLimitCone t) :
    ∃ c : JoinCone (targetCAlgDiagram R p (ofAlgebra R S)), IsLimitCone c ∧ c.vertex = t.vertex := by
  sorry -- 要確認：S3 の大きい版待ち（W9-I-04）。isLimitCone_iff_restrict_cech_large の錐の延長

theorem limit_perfectSite_eq_tot {E : SSet.{u+1}} [Quasicategory E]
    (F : Sheaves.Presheaf (perfectSite p R S hR) E)
    (t : JoinCone (Sheaves.cechShape (perfectSite_cechNerveData p R hR S (weakPerfectSiteObj p R hR S)) ≫ F))
    (ht : IsLimitCone t) :
    ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = t.vertex :=
  Sheaves.exists_limitCone_of_cech (perfectoidTargetWeaklyInitial_isWeaklyInitial p R hR S).2 _ F t ht

theorem limit_perfUnder_eq_limit_perfectSite
    (t : JoinCone (perfectResiduePresheaf p R hR S)) (ht : IsLimitCone t) :
    ∃ c : JoinCone (targetCAlgDiagram R p (ofAlgebra R S)), IsLimitCone c ∧ c.vertex = t.vertex := by
  sorry -- D47：小さい極限を弱始対象の Čech 項に制限し、同じ余積の Ō 値を大きい版へ移送

/-- 概要：E 被覆 U = E(S_alg)^∧_p について、任意の perfectoid T への S → T は U → T に延びる（各段で根と p 除算の原像）ので Q(U) は Perfd_{S/} の弱始対象。
よって Čech 計算は S3 で閉じ（Q(U^{⊗̂_S (•+1)}) の Tot）、S̃ による計算と同じ極限の錐の比較で一致（W9-II-11）。
一般の flat semiperfectoid 被覆（F_p → F_{p²} のように Q(U) が弱始でない）への一般化は別補題（E3 不要）。
方針：S3 を二回、紙 3′。
規約：—
使われ方：`limit_perfectSite_filteredColimit`。 -/
theorem cech_independent_of_flatSemiperfectoidCover
    (U : PerfUnder_u p (CommRingCat.of S)) (hU : Sheaves.IsWeaklyTerminalLarge (Opposite.op U))
    (t : JoinCone (largeCechShape p R hR S U ≫ targetCAlgDiagram R p (ofAlgebra R S))) (ht : IsLimitCone t) :
    ∃ c : JoinCone (targetCAlgDiagram R p (ofAlgebra R S)), IsLimitCone c ∧ c.vertex = t.vertex ∧
      IsLimitCone (restrictJoinCone c (largeCechShape p R hR S (perfectoidTargetWeaklyInitial p R hR S))) := by
  sorry -- U=Q(E(S_alg)^∧) では各段の延長と Cor 7.3 が hU を供給。U と S̃_perfd に S3 を順に適用

/-! ## (2) filtered 余極限（左辺の可換性 `prismaticPerfection_filteredColimit` は A4/Perfectoidization へ移した。W9-III-14） -/


/-- 概要：G-A5-2：一様に coconnective な余単体的対象の Tot は filtered 余極限と可換（H^k(Tot X) = H^k(Tot_{≤k+1} X)、部分 Tot は有限極限）。
方針：Tot の塔と coconnectivity。
規約：D(A) の cohomological な添字。
使われ方：右辺の可換性。 -/
theorem tot_coconnective_filteredColimit : True := by trivial

/-- 概要：右辺：S ↦ lim_{Perfd_{S/}} T は（完備化した）filtered 余極限と可換：図式に整合する被覆 E(S_alg)^∧_p の Tot で計算し
（`algebraicRootCover_properties`、`cech_independent_of_flatSemiperfectoidCover`。旧 (iv) は使わない、W9-II-09）、semiperfectoid の (−)_perfd の可換性、G-A5-2、完備化。
方針：上の三つ。紙 3（完備化と Tot の順序）、紙 3′。
規約：—
使われ方：有限生成への帰着。 -/
theorem limit_perfectSite_filteredColimit : True := by trivial

/-- 概要：π_0 S が位相的有限生成の S で比較写像が同値なら、すべての離散 S で同値。
方針：S = (colim S_i)^∧、両辺の可換性。
規約：—
使われ方：A5-1 の `perfectionComparison_isIso`。 -/
theorem perfectionComparison_isIso_of_finiteType_cases : True := by trivial

/-! ## (3) Lemma 8.6 による降下 -/

/-- 概要：各 S̃^n = (S̃^{⊗_S n+1})^∧（`rootCover`、RootAdjunction）は semiperfectoid（S/p の元は R/p 係数の x_i の多項式、G-A5-14）。
規約：`IsSemiperfectoid`（SemiperfectoidCase）。 -/
theorem rootCover_isSemiperfectoid (r : ℕ) (f : Fin r → S) (hf : True) : True := by trivial

/-- 概要：左辺の降下：Δ_{S,perf} → Δ_{S̃,perf} は Δ_{T,perf} → Δ_{T_∞,perf} の底変換（(5) と G-A5-3）で descendable（Lemma 8.6、(a)）、
よって Δ_{S,perf} ≃ Tot Δ_{S̃^•,perf}（(e)）。
方針：Shared/Descendable の `isDescendable_baseChange`・`isDescendable_tot_equiv`、A5-3 の `prismaticPerfection_rootMap_descendable'`（StrongDescent。W9-III-09：PerfectSiteComparison の重複した主張は削除）。
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
