-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectSiteComparison（仮。原典 Prop 8.5 の主張と系。site・Lemma 4.8・比較写像は PerfectSite.lean、W9-III-09）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.1・§2.2・§2.4、単位 A5-1（Lemma 8.6 の主張は A5-3 の予告）。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Prism.Basic.PerfectBounded

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
-- 本ファイルは drafts/A5/{PerfectSite,SemiperfectoidCase,WeaklyInitialAndDescent,StrongDescent}.lean（Prop 8.5 の証明 A5-2〜A5-4）、drafts/Sheaves/{GlobalSections,CechConerveLimit}.lean を import する。
-- W9-III-09：site・Lemma 4.8・比較写像（SemiperfectoidCase が使う）は drafts/A5/PerfectSite.lean に切り出し、本ファイルは Prop 8.5 とその系だけ（A5 の最後）。Lemma 8.6 の主張は StrongDescent の `prismaticPerfection_rootMap_descendable'` に一本化。
-- animated 版の定義域 `CompleteAnimatedAlgebra` は drafts/A7/AnimatedDomain.lean（W9-II-24：A5 より先に置く独立ファイル）を import する。

/-!
# 完全 prismatic site と Prop 8.5 の主張（BS 著者版 Rem 4.6、Lemma 4.8、Prop 8.5）

## 概要
完全 prism (A,(d))（R = A/d perfectoid）と導来 p 完備な animated R 代数 S（D45 改訂。本ファイルの `S : Type u` は離散の特別な場合）に対し、
完全 prismatic site (S/A)^perf_Δ = (π_0 S/A)^perf_Δ（A0 の `PerfectPrismaticSite` に flat 位相）、
Lemma 4.8 の系（site ≃ perfectoid 環への写像 S → T の圏、濃度 ≤ κ）、Lemma 7.7(3) の関手的写像からの比較写像
Δ_{S/A,perf} → lim_{(S/A)^perf} O_Δ、Prop 8.5（flat と chaotic の間の任意の位相で同値）とその系（S_perfd ≃ lim_{S→R′} R′ — κ-small の
site でも Type u の `PerfUnder_u` でも、A によらない、semiperfectoid なら Cor 7.3 の perfectoid 化）。

## 方針
位相非依存は O が完全 site で flat 層（G-A5-5、Cor 3.12 の制限）なことと S2（層なら RΓ = lim）で形式的。Type u の添字圏との一致は
弱始対象 S̃_perfd の Čech 余脈体（S3）で、A5-4 の `perfectoidTargetWeaklyInitial` を入力にする。Prop 8.5 本体の証明は A5-2〜A5-4。

## 規約
S は導来 p 完備な animated（D45 改訂、系 4 を含む）。本ファイルの `S : Type u` は離散版で、animated 版は末尾の `perfectionComparison_isIso_animated`・
`perfectoidization_piZero`（定義域の書き換えは中身の段階、W9-II-08）。位相の順序は Grothendieck 位相の ⊥ ≤ J ≤ flat（D46）。κ = `cutoff`（A0）。値は CAlg_A・CAlg_R。

## 使われ方
E3 の `limitCone`・`limit_isLimit`（drafts/A5/InterfaceLimitCone）、Cor 8.11（A6）、Cor 8.14（A7）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

open SerrePositivity.DerivedCompletion SerrePositivity.EInfinity.Perfectoidization

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]
-- D45 改訂（2026-11-02、決定 6）：Prop 8.5 の定義域は導来 p 完備な animated R 代数（A7-1 `CompleteAnimatedAlgebra`）。完全 site・Perfd_{S/} は π_0 S で定義する
-- （原典 p.64）。本ファイルの `S : Type u` は離散の特別な場合で、中身の段階で定義域を animated に書き換える（design-status §5）。animated 版の主張は末尾に置く。

/-! ## Prop 8.5 -/

/-- 概要：Prop 8.5（実体）：比較写像は同値。
方針：A5-2（semiperfectoid の場合）、A5-4（弱始対象・filtered 余極限・Lemma 8.6 による降下）。
規約：S 離散。
使われ方：以下の系、E3。 -/
theorem perfectionComparison_isIso (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    IsIso (perfectionComparison (E := E) p R hR S hS) := by
  sorry -- A5-4 の有限型への帰着と Lemma 8.6 による降下、各項は A5-2。flat 層 O の Γ はこの極限

/-- S2 の層化・大域切断に渡す係数圏の presentability（G12）。 -/
theorem perfectCoefficientPresentable : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg (perfectPrismRing p R)) := E.presentable (perfectPrismRing p R)

/-- 概要：Prop 8.5（原典の形）：⊥ ≤ J ≤ flat の任意の位相 J で Δ_{S/A,perf} ≃ RΓ_J((S/A)^perf, O_Δ)。
方針：O は flat 層（`perfectStructurePresheaf_isSheaf`）なので J 層（S1 `IsSheaf.of_le`）、S2 で RΓ_J = lim、`perfectionComparison_isIso`。
規約：D46。
使われ方：原典との対応（Cor 8.11 は Prop 8.10 と合わせる）。 -/
theorem perfectionComparison_isIso_topology (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (J : GrothendieckTopology (perfectSite p R S hR)) (hJ : J ≤ perfectFlatTopology p R S hR) :
    let A := perfectPrismRing p R
    let hA := perfectCoefficientPresentable (E := E) p R
    let L := Sheaves.sheafification_exists_cAlg (E := E) J A hA
    let F := perfectStructurePresheaf (E := E) p R hR S
    let Γ := Sheaves.globalSections F (perfectStructure_hasLimit (E := E) p R hR S)
    ∃ v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso Γ (Sheaves.derivedGlobalSectionsCAlg (E := E) J A L hA F),
      IsIso (perfectionComparison (E := E) p R hR S hS ≫ v.hom) := by
  sorry -- ⊥≤J は自動。G-A5-5 を J に制限し S2 の derivedGlobalSections_of_isSheaf で二つの極限を比較

/-- 概要：系 1（κ 版）：S_perfd ≃ lim_{(S/A)^perf} Ō_Δ ≃ lim_{S→T, T perfectoid, #T ≤ κ} T（CAlg_R）。
方針：⊗^L_A A/d は cofib(d) で極限と可換（G-A5-9）、完全 prism で B ⊗^L A/d = B/J（d 正則）、`perfectSiteEquivPerfectoidUnder` で添字を移す。
規約：`IsLimitCone`。
使われ方：系 2、Type u 版。 -/
theorem perfectoidization_isLimit (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (perfectResiduePresheaf (E := E) p R hR S), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧
      c.vertex = perfectoidization (E := E) p R hR S hS := by
  sorry -- Prop 8.5 の比較錐に modPrismFunctor を施す。d の cofiber は極限を保ち、
        -- testModDResidueIso の自然な同型で成分を Ō に移す

/-- 概要：系 1（Type u 版）：S_perfd は `PerfUnder_u p S` 上の図式 T ↦ T の極限（CAlg_R、D(R)）。
方針：A5-4 の弱始対象 S̃_perfd（濃度 ≤ κ）の Čech 余脈体で、κ 版と Type u 版の極限がどちらも同じ Tot に等しい（S3、D47）。
規約：錐の形は InterfaceLimitCone で E3 の欄に合わせる。
使われ方：E3 の `limit_isLimit`。 -/
theorem perfectoidization_isLimit_u (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (theoryTargetDiagram (E := E) R p (ofAlgebra R S)), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧
      c.vertex = perfectoidization (E := E) p R hR S hS := by
  obtain ⟨t, ht, hv⟩ := perfectoidization_isLimit (E := E) p R hR S hS
  obtain ⟨c, hc, hcv⟩ := limit_perfUnder_eq_limit_perfectSite (E := E) p R hR S t ht
  exact ⟨c, hc, hcv.trans hv⟩

/-- 別の完全 prism P 上で Def 8.2 を計算する。S の係数射は P/d ≃ R を経由する。 -/
def perfdOverPerfectPrism {B : Type u} [CommRing B] (P : OrientedPrism p B)
    (hP : P.deltaStructure.IsPerfect) (e : B ⧸ P.ideal ≃+* R) : (E.CAlg R) _⦋0⦌ := by
  let q := e.toRingHom.comp (Ideal.Quotient.mk P.ideal)
  let X := Under.mk (CommRingCat.ofHom ((algebraMap R S).comp e.toRingHom))
  let D := (derivedPrismaticCohomologyDiscrete (E := E) P (hP := isBoundedPrism_of_perfect P hP) ≫ _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.completeCAlgInclusion (E := E) (p := p) P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)
  let res := cAlgRestrictScalars (E := E) P.deltaStructure.frobeniusLift
  let φ : SSet.Edge D (res.app _ D) := by
    sorry -- 要確認：BS-D4 の離散 Frobenius 成分。P と A_inf(R) の Lemma 4.8 の同型で
          -- discreteDeltaFrobenius を移した同じ成分（G-A5-17）
  let T := restrictionSequence res φ
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit T := by sorry -- CAlg_B の逐次余極限
  exact (_root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.prismCAlgCompletion (E := E) (p := p) P ≫ prismScalarExtension (E := E) q).app _ ht.choose.vertex

/-- 概要：系 2：S_perfd は A によらない。二つの完全 prism (A,(d))、(A′,(d′))（A/d ≅ R ≅ A′/d′）で CAlg_R の同型。
方針：系 1 の右辺は A を含まない。
規約：`perfectPrism p R` は Not 8.1 で一つ固定しているので、主張は「別の選択」との比較として述べる。
使われ方：記録（E3 では使わない）。 -/
theorem perfectoidization_indep {B : Type u} [CommRing B] (P : OrientedPrism p B)
    (hP : P.deltaStructure.IsPerfect) (e : B ⧸ P.ideal ≃+* R)
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (perfectoidization (E := E) p R hR S hS) (perfdOverPerfectPrism (E := E) p R S P hP e)) := by
  sorry -- G-A5-17 および Lemma 4.8 で基底を移し、どちらも同じ S → T の図式の極限に比較

/-- 概要：系 3：S が semiperfectoid なら S_perfd は離散で、Cor 7.3 の普遍 perfectoid 環 R′ と S の下で同型。
方針：A5-2（証明 (4) そのもの）。
規約：R′ は A5-2 の `universalPerfectoidRing`。
使われ方：A5-4 の弱始対象、Cor 8.14。 -/
theorem perfectoidization_semiperfectoid (hS : IsSemiperfectoid p R S) :
    IsTheoryDiscrete (E := E) R (perfectoidization (E := E) p R hR S hS.1) ∧
      ∃ e : (directPerfdRing (E := E) p R hR (ofAlgebra R S)).right ≃+* universalPerfectoidRing p R S hS,
        e.toRingHom = perfectoidizationToUniversal (E := E) p R hR S hS ∧
        e.toRingHom.comp (directPerfdRingUnit (E := E) p R hR (ofAlgebra R S)).right.hom =
          universalPerfectoidUnit p R S hS := by
  obtain ⟨e, he, hu, _⟩ := perfectoidization_semiperfectoid_iso (E := E) p R hR S hS
  exact ⟨perfectoidization_discrete_of_semiperfectoid (E := E) p R hR S hS, e, he, hu⟩

/-! ## animated 版（D45 改訂）と系 4 -/

/-- π₀ は完備な離散代数の埋め込みの左随伴。単位が S → π₀ S を指定する。
A7/UniversalProperty より前に使うので A7-1 の completeDiscreteToAnimated だけで特徴付ける。 -/
def piZeroReflection : Σ F : CompleteAnimatedAlgebra p R ⟶ nerve (C_R R p),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F (completeDiscreteToAnimated p R) := by
  sorry -- 要確認：A2 の animated π₀。離散標的への写像を π₀ の環準同型で表す

abbrev piZeroObj (X : (CompleteAnimatedAlgebra p R) _⦋0⦌) : C_R R p :=
  ((piZeroReflection p R).1.app _ X).obj 0

abbrev piZeroUnit (X : (CompleteAnimatedAlgebra p R) _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (piZeroReflection p R).2.unitHom X

/-- A7-1 の塔を完備な離散入力で評価した比較。mod d を取ると perfectoidizationAnimated_discrete。 -/
def discretePerfectionIso (U : C_R R p) :
    letI := U.obj.hom.hom.toAlgebra
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((completeDiscreteToAnimated p R ≫ prismaticPerfectionAnimated (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))
      (prismaticPerfection (E := E) p R hR U.obj.right U.property) := by
  sorry -- 同じ離散 Frobenius 塔の余極限を完備化し、directPerfectionVertex で移送

def animatedComparison (X : (CompleteAnimatedAlgebra p R) _⦋0⦌) :
    let U := piZeroObj p R X
    letI := U.obj.hom.hom.toAlgebra
    (HomotopyCategory.mk ((prismaticPerfectionAnimated (E := E) p R hR).app _ X) :
      hoFunctor.obj (E.CAlg (perfectPrismRing p R))) ⟶
      HomotopyCategory.mk (Sheaves.globalSections (perfectStructurePresheaf (E := E) p R hR U.obj.right)
        (perfectStructure_hasLimit (E := E) p R hR U.obj.right)) := by
  let U := piZeroObj p R X
  letI := U.obj.hom.hom.toAlgebra
  exact (hoFunctor.map (prismaticPerfectionAnimated (E := E) p R hR)).toFunctor.map (piZeroUnit p R X) ≫
    eqToHom (by sorry) ≫ -- π₀ の nerve の頂点を U として読む
    (discretePerfectionIso (E := E) p R hR U).hom ≫ perfectionComparison (E := E) p R hR U.obj.right U.property

/-- 概要：Prop 8.5（animated 版）：導来 p 完備な animated R 代数 S（`CompleteAnimatedAlgebra`）について、site を π_0 S で取った比較写像
Δ_{S/A,perf} → lim_{(π_0 S/A)^perf} O は同値。
方針：§3 の四段を animated S で（T → S は π_0 で全射、semiperfectoid の段は π_0 S）。離散 S は `discreteToAnimated` 経由の特別な場合。
規約：π_0 S は piZeroReflection の値。
使われ方：系 4、A8（Thm 10.11 は animated LΛ_p S について）。 -/
theorem perfectionComparison_isIso_animated (X : (CompleteAnimatedAlgebra p R) _⦋0⦌) :
    IsIso (animatedComparison (E := E) p R hR X) := by
  sorry -- π₀ の完全 site で比較の脚を評価する。animated 入力にも四段の降下を適用し、
        -- 有限型の段で T → X に課す全射性は π₀ で判定する

/-- 概要：系 4（決定 6）：Δ_{S,perf} と S_perfd は π_0 S のみによる：S → π_0 S が Δ_{S,perf} ≃ Δ_{π_0 S,perf}、S_perfd ≃ (π_0 S)_perfd を誘導する。
方針：perfectoid 環は離散なので Perfd_{S/} = Perfd_{π_0 S/}、両辺とも同じ極限（animated 版の Prop 8.5）。
規約：—
使われ方：E3 の非完備な離散 S（perfd S := (completionRing S)_perfd、completionRing S = π_0(LΛ_p S)）と直接の式 (LΛ_p S)_perfd の一致（A4-3 `e3Perfd_eq_direct`）、
A8 の `integral`（Thm 10.11 の LΛ_p S から H⁰ 完備化へ）。 -/
theorem perfectoidization_piZero (X : (CompleteAnimatedAlgebra p R) _⦋0⦌) :
    IsIso ((hoFunctor.map (prismaticPerfectionAnimated (E := E) p R hR)).toFunctor.map (piZeroUnit p R X)) ∧
      IsIso ((hoFunctor.map (perfectoidizationAnimated (E := E) p R hR)).toFunctor.map (piZeroUnit p R X)) := by
  sorry -- 同一の π₀ site への二つの指定比較が同型なので単位の像も同型。modPrismFunctor で第二の同型

end SerrePositivity.BhattScholze.Perfectoidization.Derived
