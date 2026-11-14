-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.WeaklyInitialAndDescent（仮。原典 Prop 8.5 の証明 (1)〜(3)）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §3.1〜§3.3、単位 A5-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import Mathlib.AlgebraicTopology.CechNerve
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
原典の四段のうち形式的な三段。Lemma 8.6 は A5-3 の主張（`prismaticPerfection_rootMap_descendable'`）を入力にする。

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

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

open SerrePositivity.DerivedCompletion SerrePositivity.EInfinity.Perfectoidization

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## (1) 弱始対象 -/

include hR in
/-- 概要：(ii) S̃ は semiperfectoid：S̃/p は semiperfect（各元が次の段で p 乗根をもつ）、p 完備な R 代数で mod p semiperfect なら perfectoid の商
（G-A5-14、[BMS19, Rem 4.22]：θ : W(S̃^♭) → S̃ 全射、R ⊗̂ W(S̃^♭) は perfectoid）。
方針：既存の θ（`fontaineTheta`）と完備テンソル。
規約：A5-2 の `IsSemiperfectoid`。**perfectoid 基底 R は本質的**（W9-II-16）：ker θ の distinguished 元は R 由来。基底なしでは偽
（S = ℤ_p の根添加は ℤ_p へ retraction をもつ）。A6 の Lemma 8.8 は前段 G-A6-11 で R₀ = ℤ_p[p^{1/p^∞}]^∧ 上へ移してから本定理を使う。
使われ方：S̃_perfd の存在（Cor 7.3）、A5-2 の適用。 -/
theorem rootClosure_isSemiperfectoid : IsSemiperfectoid p R (rootClosure p R S) := by
  sorry -- 完備性と mod p の根を使い、perfectoid 基底 R 上で θ の全射から商表示を作る

/-- E を先に作り、構造射・単位射も含めて H⁰ 完備化する。 -/
def algebraicCoverUnit (C : CommRingCat.{u}) :
    completionRing p C ⟶ completionRing p ((algebraicRootFunctor p).obj C) :=
  completionMap p (CommRingCat.ofHom (algebraicRootClosureUnit p C))

include hR in
/-- 概要：S = S_alg^∧（S_alg = colim_i S_i）の被覆 E(S_alg)^∧_p：p 完備忠実平坦、semiperfectoid（mod p の根、G-A5-14）、E(S_i)^∧_p の完備 filtered 余極限。
E(S)^∧_p とは同一視しない。
方針：各段の自由性と完備化。
規約：—
使われ方：§3.2 の右辺の可換性。 -/
theorem algebraicRootCover_properties {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ A_R R) :
    let D₀ := D ⋙ Under.forget (CommRingCat.of R)
    let C := Limits.colimit D₀
    let j₀ : J := Classical.choice IsFiltered.nonempty
    let E := algebraicRootFunctor p
    let U := completionRing p (E.obj C)
    letI : CommRing U := U.commRing
    letI := (algebraicCoverUnit p C).hom.toAlgebra
    letI : Algebra R U := ((algebraicCoverUnit p C).hom.comp ((completionUnit p C).hom.comp
      ((Limits.colimit.ι D₀ j₀).hom.comp
        (D.obj j₀).hom.hom))).toAlgebra
    let D₁ := (D₀ ⋙ E) ⋙ ringCompletionFunctor p
    let c₀ : Limits.Cocone (D₀ ⋙ E) := E.mapCocone (Limits.colimit.cocone D₀)
    let c : Limits.Cocone D₁ := (ringCompletionFunctor p).mapCocone c₀
    let f : Limits.colimit D₁ ⟶ U := Limits.colimit.desc D₁ c
    IsCompletelyFaithfullyFlat (Ideal.span {(p : completionRing p C)}) U ∧
      IsSemiperfectoid p R U ∧
      IsIso (completionMap p f ≫
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
    Sheaves.IsWeaklyTerminalLarge (Opposite.op (perfectoidTargetWeaklyInitial p R hR S)) := by
  sorry -- rootClosure_extends の脚を Cor 7.3 の指定単位に沿って一意に降ろす

theorem weakPerfectSiteObj_isWeaklyTerminal : Sheaves.IsWeaklyTerminal (weakPerfectSiteObj p R hR S) := by
  sorry -- 大きい圏での弱始性を cutoff 部分圏の充満性と Lemma 4.8 の同値で移送


-- Čech 余脈体 `perfUnder_cechNerveData`（Perfd_{S/} の余積 (T₁ ⊗̂_S T₂)_perfd）は A5/PerfectSite へ移した（W9-III-14：既存 Cor 7.3 の普遍環から直接作れる）。

abbrev cosimplicialShape : SSet.{u+1} := (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)

def largeCechShape (U : PerfUnder_u p (CommRingCat.of S)) :
    cosimplicialShape.{u} ⟶ perfectoidTargetNerve p (CommRingCat.of S) where
  app n := ↾fun x =>
    (((perfUnder_cechNerveData p R hR S (Opposite.op U)).obj.rightOp ⋙ unopUnop _).mapComposableArrows _).obj x.down
  naturality := by sorry -- 各単体の列を同じ余積の関手で送る

abbrev perfectResiduePresheaf :=
  Sheaves.ringPresheafToCAlg (E := E) R ((perfectResidueFunctor p R hR S) ⋙ (ObjectProperty.ι _) ⋙
    targetAlgebra R p (ofAlgebra R S))

/-- 概要：lim_{PerfUnder_u p S} T ≃ Tot((S̃^•)_perfd)（S3 `exists_limitCone_of_cech`、Čech データは PerfectSite `perfUnder_cechNerveData`）。κ 側の完全 site でも同じ Tot（弱始対象は濃度 ≤ κ）。
よって Type u の極限と κ-small の site の極限は一致（D47）。
方針：S3 を二回。
規約：—
使われ方：A5-1 の `perfectoidization_isLimit_u`。 -/
theorem limit_perfUnder_eq_tot
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (largeCechShape p R hR S (perfectoidTargetWeaklyInitial p R hR S) ≫
      theoryTargetDiagram (E := E) R p (ofAlgebra R S))) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (theoryTargetDiagram (E := E) R p (ofAlgebra R S)), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex := by
  sorry -- 要確認：S3 の大きい版待ち（W9-I-04）。isLimitCone_iff_restrict_cech_large の錐の延長

theorem limit_perfectSite_eq_tot {E : SSet.{u+1}} [Quasicategory E]
    (F : Sheaves.Presheaf (perfectSite p R S hR) E)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (Sheaves.cechShape (perfectSite_cechNerveData p R hR S (weakPerfectSiteObj p R hR S)) ≫ F))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex :=
  Sheaves.exists_limitCone_of_cech (weakPerfectSiteObj_isWeaklyTerminal p R hR S) _ F t ht

theorem limit_perfUnder_eq_limit_perfectSite
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (perfectResiduePresheaf (E := E) p R hR S)) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (theoryTargetDiagram (E := E) R p (ofAlgebra R S)), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex := by
  sorry -- D47：小さい極限を弱始対象の Čech 項に制限し、同じ余積の Ō 値を大きい版へ移送

include hR in
/-- 図式に整合する E 被覆の弱始対象。基底は完備化した C、Q(U) の構造射は
C^∧ → E(C)^∧ → Q(E(C)^∧) の合成。 -/
theorem algebraicCoverWeakTarget (C : A_R R) :
    let S₀ := completionRing p C.right
    let U := completionRing p ((algebraicRootFunctor p).obj C.right)
    letI : CommRing U := U.commRing
    let j := algebraicCoverUnit p C.right
    letI : Algebra R U := (j.hom.comp ((completionUnit p C.right).hom.comp C.hom.hom)).toAlgebra
    ∃ h : IsSemiperfectoid p R U,
      Sheaves.IsWeaklyTerminalLarge (Opposite.op (show PerfUnder_u p S₀ from
        ⟨Under.mk (Y := CommRingCat.of (universalPerfectoidRing p R U h))
          (j ≫ CommRingCat.ofHom (R := U) (universalPerfectoidUnit p R U h)),
         (universalPerfectoidUnit_isPerfectoidization p R U h).1⟩)) := by
  sorry -- E の各代数段へ mod p の根と p 除算の原像を選び、T の完備性で完備化を延長。
        -- E(C)^∧ は G-A5-14 で semiperfectoid、その Cor 7.3 の単位に沿って延長を降ろす

/-- 概要：E 被覆 U = E(S_alg)^∧_p について、任意の perfectoid T への S → T は U → T に延びる（各段で根と p 除算の原像）ので Q(U) は Perfd_{S/} の弱始対象。
よって Čech 計算は S3 で閉じ（Q(U^{⊗̂_S (•+1)}) の Tot）、S̃ による計算と同じ極限の錐の比較で一致（W9-II-11）。
一般の flat semiperfectoid 被覆（F_p → F_{p²} のように Q(U) が弱始でない）への一般化は別補題（E3 不要）。
方針：S3 を二回、紙 3′。
規約：—
使われ方：`limit_perfectSite_filteredColimit`。 -/
theorem cech_independent_of_flatSemiperfectoidCover
    (U : PerfUnder_u p (CommRingCat.of S)) (hU : Sheaves.IsWeaklyTerminalLarge (Opposite.op U))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (largeCechShape p R hR S U ≫ theoryTargetDiagram (E := E) R p (ofAlgebra R S))) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (theoryTargetDiagram (E := E) R p (ofAlgebra R S)), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (largeCechShape p R hR S (perfectoidTargetWeaklyInitial p R hR S))) := by
  sorry -- U=Q(E(S_alg)^∧) では各段の延長と Cor 7.3 が hU を供給。U と S̃_perfd に S3 を順に適用

/-! ## (2) filtered 余極限（左辺の可換性 `prismaticPerfection_filteredColimit` は A4/Perfectoidization へ移した。W9-III-14） -/


/-- 極限錐の族をその頂点の族へ送る。 -/
def cosimplicialTot {E : SSet.{u+1}} [Quasicategory E]
    (h : ∀ X : cosimplicialShape.{u} ⟶ E, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit X) :
    (ihom cosimplicialShape.{u}).obj E ⟶ E := by
  let sec : { G : (ihom cosimplicialShape).obj E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitCones cosimplicialShape E //
      G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection _ _ = 𝟙 _ } := by
    sorry -- 全図式が極限をもつので極限錐の射影は自明 Kan fibration、恒等射を持ち上げる
  exact sec.val ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeTerminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction _ _)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation _ _

/-- 概要：G-A5-2：一様に coconnective な余単体的対象の Tot は filtered 余極限と可換（H^k(Tot X) = H^k(Tot_{≤k+1} X)、部分 Tot は有限極限）。
方針：Tot の塔と coconnectivity。
規約：D(A) の cohomological な添字。
使われ方：右辺の可換性。 -/
theorem tot_coconnective_filteredColimit {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I]
    (D : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ (ihom cosimplicialShape).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (b : ℤ)
    (hb : ∀ i : I _⦋0⦌, ∀ n : SimplexCategory, Derived.IsCoconnectiveAt R b
      ((D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n))).app _ (ULift.up i)))
    (hlim : ∀ X : cosimplicialShape ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (cosimplicialTot hlim) c) := by
  sorry -- 各 H^k は下界 b に依存する有限の部分 Tot で安定し、有限極限は filtered 余極限と交換する

/-- 完全試験環 B 上の O は A_inf(B)。構造射・射は有界完全 prism への一意な持ち上げ。 -/
abbrev perfectTests := PerfUnder_u p (CommRingCat.of R)

def testPrisms : perfectTests p R ⥤ A_R (perfectPrismRing p R) where
  obj B := by
    letI := B.obj.hom.hom.toAlgebra
    exact Under.mk (CommRingCat.ofHom (perfectBaseHom p R hR B.obj.right B.property).toRingHom)
  map {B T} f := by
    letI := f.hom.right.hom.toAlgebra
    let lift := perfectBaseHom p B.obj.right B.property T.obj.right T.property
    exact Under.homMk (CommRingCat.ofHom lift.toRingHom) (by
      sorry) -- 商で二つの合成は R 上で一致し、有界標的での持ち上げは一意
  map_id := by sorry -- 商環で恒等射、持ち上げは一意
  map_comp := by sorry -- 商環で合成、持ち上げは一意

/-- O の極限を S に関して関手化する。右 Kan 拡張の S での添字は S → B、B perfectoid。 -/
def perfectSiteSections :
    algebraNerve R ⟶ CompleteCAlg (E := E) (perfectPrism p R hR) :=
  let i := nerveMap (perfectoidTargetInclusion p (CommRingCat.of R))
  let O := nerveMap (testPrisms p R hR) ≫ E.discrete _ ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.reflectCompleteCAlg (E := E) (p := p) (perfectPrism p R hR)
  Classical.choose (show ∃ F, ∃ α : SSet.Homotopy (i ≫ F) O, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension i O F α from by
    sorry) -- D47 の弱始対象の小さい Čech 図式で各大きい comma 圏に極限がある

/-- S を固定すると右 Kan 拡張は O の完全 site 上の極限を与える。 -/
def perfectSiteSectionsVertex :
    let F := perfectSiteSections (E := E) p R hR ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.completeCAlgInclusion (E := E) (p := p) (perfectPrism p R hR)
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S)))
      (Sheaves.globalSections (perfectStructurePresheaf (E := E) p R hR S) (perfectStructure_hasLimit (E := E) p R hR S)) := by
  sorry -- Ran の S での comma 圏は Perfd_{S/}。Lemma 4.8 と D47 の同じ Čech 項で O の極限を比較

/-- 概要：右辺：S ↦ lim_{Perfd_{S/}} T は（完備化した）filtered 余極限と可換：図式に整合する被覆 E(S_alg)^∧_p の Tot で計算し
（`algebraicRootCover_properties`、`cech_independent_of_flatSemiperfectoidCover`。旧 (iv) は使わない、W9-II-09）、semiperfectoid の (−)_perfd の可換性、G-A5-2、完備化。
方針：上の三つ。紙 3（完備化と Tot の順序）、紙 3′。
規約：—
使われ方：有限生成への帰着。 -/
theorem limit_perfectSite_filteredColimit {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I]
    (D : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ algebraNerve R) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (perfectSiteSections (E := E) p R hR) c) := by
  sorry -- E 被覆で各項の O は完全 prism、Ō はその mod d。G-A5-2 の後に Koszul 完備化を施す

/-- 概要：π_0 S が位相的有限生成の S で比較写像が同値なら、すべての離散 S で同値。
方針：S = (colim S_i)^∧、両辺の可換性。
規約：—
使われ方：A5-1 の `perfectionComparison_isIso`。 -/
theorem perfectionComparison_isIso_of_finiteType_cases
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B]
      (hB : IsModuleComplete B (p : B) (ModuleCat.of B B)) (r : ℕ) (x : Fin r → B),
      Function.Surjective (polyEvaluation p R B r x hB) → IsIso (perfectionComparison (E := E) p R hR B hB))
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    IsIso (perfectionComparison (E := E) p R hR S hS) := by
  sorry -- 通常の有限型部分代数の filtered 系に左右の完備余極限保存
        -- prismaticPerfection_filteredColimit と limit_perfectSite_filteredColimit を適用

/-! ## (3) Lemma 8.6 による降下 -/

def rootCoverArrow (r : ℕ) (x : Fin r → S) : Arrow (A_R R) :=
  let U := rootCoverAlgebra p R S r x
  Arrow.mk (Under.homMk U.hom rfl : ofAlgebra R S ⟶ Under.mk ((ofAlgebra R S).hom ≫ U.hom))

def rootCoverCech (r : ℕ) (x : Fin r → S) : CosimplicialObject (A_R R) :=
  (rootCoverArrow p R S r x).cechConerve ⋙ PerfectoidizationInterface.completionFunctor p R

def rootCoverShape (r : ℕ) (x : Fin r → S) : cosimplicialShape.{u} ⟶ algebraNerve R where
  app n := ↾fun a => ((rootCoverCech p R S r x).mapComposableArrows _).obj a.down
  naturality := by sorry -- cechConerve の構造射を nerve で送る

/-- S → S̃^• の増大を、全余単体写像とともに nerve の錐にする。 -/
def rootCoverAugmentedCone (r : ℕ) (f : Fin r → S) :
    { c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (rootCoverShape p R S r f) // ∃ hv : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S),
      ∀ n : SimplexCategory,
        let a := (rootCoverArrow p R S r f).augmentedCechConerve.hom.app n
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n))).edge =
          (nerve.edgeMk (a ≫ (completionAlgebraUnit p R).app _)).edge } := by
  sorry -- 増大の自然変換を N(Δ) の左錐に延長。頂点は S、全脚は広い押し出しへの射と完備化単位の合成

include hR in
/-- 概要：各 S̃^n = (S̃^{⊗_S n+1})^∧（`rootCover`、RootAdjunction）は semiperfectoid（S/p の元は R/p 係数の x_i の多項式、G-A5-14）。
規約：`IsSemiperfectoid`（SemiperfectoidCase）。 -/
theorem rootCover_isSemiperfectoid (r : ℕ) (f : Fin r → S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hf : Function.Surjective (polyEvaluation p R S r f hS)) (n : ℕ) :
    let U := (rootCoverCech p R S r f).obj ⦋n⦌
    letI := U.hom.hom.toAlgebra
    IsSemiperfectoid p R U.right := by
  sorry -- T → S が全射、各項の mod p は根変数と perfectoid 基底の係数で生成される

/-- 概要：左辺の降下：Δ_{S,perf} → Δ_{S̃,perf} は Δ_{T,perf} → Δ_{T_∞,perf} の底変換（(5) と G-A5-3）で descendable（Lemma 8.6、(a)）、
よって Δ_{S,perf} ≃ Tot Δ_{S̃^•,perf}（(e)）。
方針：Shared/Descendable の `isDescendable_baseChange`・`isDescendable_tot_equiv`、A5-3 の `prismaticPerfection_rootMap_descendable'`（StrongDescent。W9-III-09：PerfectSiteComparison の重複した主張は削除）。
規約：D_comp(A)。
使われ方：`perfectionComparison_isIso_of_finiteType`。 -/
theorem prismaticPerfection_rootCover_descent (r : ℕ) (f : Fin r → S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (directPerfectionFunctor (E := E) p R hR) (rootCoverAugmentedCone p R S r f).val
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (prismaticPerfection (E := E) p R hR S hS) c.vertex) := by
  sorry -- prismaticPerfection_rootMap_descendable' と (5) で完備押し出しに移す。
        -- Shared の isDescendableOver_pushout、isDescendableOver_tot_equiv

/-- 概要：G-A5-7：L_n : Perfd_{S/} → Perfd_{S̃^n/}、R′ ↦ (R′ ⊗̂_S S̃^n)_perfd は忘却の左随伴、よって始的で lim_{Perfd_{S̃^n/}} O = lim_{Perfd_{S/}} O ∘ L_n。
方針：随伴の単位・余単位（Cor 7.3 の普遍性）、HTT 4.1.1.8 の系。
規約：—
使われ方：右辺の降下。 -/
theorem perfUnder_leftAdjoint_initial (r : ℕ) (f : Fin r → S) (n : ℕ) :
    let a := (rootCoverArrow p R S r f).augmentedCechConerve.hom.app ⦋n⦌
    let Bn := ((rootCoverArrow p R S r f).cechConerve.obj ⦋n⦌).right
    let q := a.right ≫ completionUnit p Bn
    let forget : PerfUnder_u p (completionRing p Bn) ⥤ PerfUnder_u p (CommRingCat.of S) :=
      { obj := fun B => ⟨(Under.map q).obj B.obj, B.property⟩
        map := fun g => ObjectProperty.homMk ((Under.map q).map g.hom)
        map_id := by sorry -- 基底射の前合成は標的の射を保つ
        map_comp := by sorry } -- 同じ基底射への制限は合成を保つ
    ∃ L : PerfUnder_u p (CommRingCat.of S) ⥤ PerfUnder_u p (completionRing p Bn),
      Nonempty (L ⊣ forget) ∧ L.Initial := by
  sorry -- L(B)=Q(B ⊗̂_S S̃ⁿ)。Cor 7.3 は二つの脚を延長する唯一の射を与え、随伴から始性

/-- 概要：右辺の降下：各 R′ で B_{R′} ≃ Tot_n Δ_{R′ ⊗̂_S S̃^n,perf}（Lemma 8.6 の底変換）、極限の交換（G-A5-8）で
lim_{Perfd_{S/}} B_{R′} ≃ Tot_n lim_{Perfd_{S̃^n/}} O。
方針：上と `prismaticPerfection_rootCover_descent` を R′ に適用。紙 4。
規約：—
使われ方：`perfectionComparison_isIso_of_finiteType`。 -/
theorem limit_perfectSite_rootCover_descent (r : ℕ) (f : Fin r → S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let F := perfectSiteSections (E := E) p R hR ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.completeCAlgInclusion (E := E) (p := p) (perfectPrism p R hR)
    let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (rootCoverAugmentedCone p R S r f).val
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S)) := by
  sorry -- 各 perfectoid 標的で左辺の降下を使い、L_n の始性で二つの極限を交換

/-- 概要：π_0 S が位相的有限生成なら比較写像は同値：両辺の Tot の各項は semiperfectoid の場合（A5-2 `perfectoidization_semiperfectoid_iso` の
prism 版 Δ_{S̃^n,perf} ≃ B_{(S̃^n)_perfd}）で同値。
方針：上の二つと A5-2。
規約：—
使われ方：A5-1 の `perfectionComparison_isIso`（`perfectionComparison_isIso_of_finiteType_cases` と合わせる）。 -/
theorem perfectionComparison_isIso_of_finiteType (r : ℕ) (f : Fin r → S)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hf : Function.Surjective (polyEvaluation p R S r f hS)) :
    IsIso (perfectionComparison (E := E) p R hR S hS) := by
  sorry -- 両側の降下錐の項は semiperfectoid の場合に同値、指定比較射の Tot も同型

end SerrePositivity.BhattScholze.Perfectoidization.Derived
