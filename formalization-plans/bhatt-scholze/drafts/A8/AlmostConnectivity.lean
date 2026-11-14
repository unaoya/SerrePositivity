-- 将来の置き場所：SerrePositivity.BhattScholze.Almost.AlmostConnectivity（仮。原典 Prop 10.4 の必要部分、Lemma 10.5、J-almost の基本）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.1・§3.1、単位 A8-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates
public import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
public import SerrePositivity.BhattScholze.Almost.AlmostGenerators
public import SerrePositivity.BhattScholze.Almost.AlmostTensor
public import SerrePositivity.BhattScholze.Almost.AlmostTensorForward
public import SerrePositivity.BhattScholze.Almost.CompletedModuleTensor

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
public import SerrePositivity.BhattScholze.Almost.Lemma103
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.HeartFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
-- W9-III-08：Lemma103 は現行の CompletedTensor（→ IntegralExistence → Inputs）を import する。2a 後に Lemma103 の依存を E3 非依存の芯（仮称 CompletedTensorCore）へ向ける（a9-design §7）。
-- 本ファイルは drafts/A7/AnimatedPerfectoidization.lean（Prop 8.13）、drafts/DerivedGeneral/{Truncation,CompletionFunctor}.lean を import する。

/-!
# J-almost 連結性（BS 著者版 Prop 10.4 の必要部分、Lemma 10.5）と J-almost の基本

## 概要
R perfectoid、J ⊂ R 導来 p 完備、J_perfd = ker(R → (R/J)_perfd)（単項では既存の `perfectoidIdeal`）。導来 p 完備な複体 M が J-almost 零 ⇔ J_perfd ⊗̂^L M = 0
（Prop 10.4 の必要部分、D66）。Lemma 10.5：M 連結 ⇔ M ⊗̂^L R/J_perfd 連結かつ M が J-almost 連結。基本：J-almost は √J で不変、
J = (f_1..f_r) で J-almost ⇔ ∀i (f_i)-almost、忠実平坦な perfectoid の基底変換 R → R′ で反映（(JR′)_perfd = J_perfd R′）。

## 方針
加群版（B5 の `perfectoidIdeal_completedTensor_isZero_of_isAlmostZero`・`_of_completedTensor_isZero`）を truncation の帰納で有界複体に、
完備性と truncation の極限・余極限で非有界に。Lemma 10.5 は三角形 J_perfd ⊗̂ M → M → (R/J)_perfd ⊗̂ M。基底変換は Prop 8.13。

## 規約
J-almost 零は既存 `IsAlmostZero`（CommutativeAlgebra/Almost/Zero）を J_perfd で。cohomological な添字（連結 = D^{≤0}）。

## 使われ方
Thm 10.9 の J-almost 連結性（A8-2）、Thm 10.11 の帰納（A8-4）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Almost

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) (J : Ideal R)

open SerrePositivity.InfinityCategories SerrePositivity.DerivedCompletion
open SerrePositivity.BhattScholze.Perfectoidization.Derived

abbrev CompleteDerived (A : Type u) [CommRing A] : SSet.{u+1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) (SerrePositivity.DerivedInfinity.IsPComplete p A)

def completeModuleRestriction {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    CompleteDerived p B ⟶ CompleteDerived p A :=
  let D := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (SerrePositivity.DerivedInfinity.IsPComplete p B)).ι ≫ derivedInfinityRestrictScalars (E := E) f
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ D (by sorry) -- 係数を制限しても底の複体の p 完備性は同じ

/-- 概要：内部補題（W9-III-10）：B := (R/J)_perfd（perfectoid、R/K、K := J_perfd）について Lemma 10.3 の B ⊗̂^L_R B ≃ B から、忘却
U : D_{p-comp}(B) → D_{p-comp}(R) は完全忠実で、極限と余極限を保つ（通常の忘却は余極限を保ち、両側の完備化は同じ p）。像は安定部分圏で、
有界切り捨て（有限個の拡大）と Postnikov 塔の極限・完備余極限で閉じる。
方針：一般の perfectoid 商の Lemma 10.3（既存 `Lemma103` は単項 g の版なので K = ker(R → B) に一般化する）。完備テンソルが任意の逆極限と可換とは主張しない。
規約：—
使われ方：Prop 10.4 の非有界版。 -/
theorem restrictScalars_perfectoidQuotient_fullyFaithful
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J)) :
    let B := QuotientPerfectoidization R J p hR
    let U := completeModuleRestriction (E := E) p (quotientPerfdMap p R hR J)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful U ∧ ∀ (I : SSet.{u+1}) (F : I ⟶ CompleteDerived p B),
      (∀ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone U c)) ∧
      (∀ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone U c)) := by
  sorry -- B ≃ R/K。一般商の integralPerfectoid_completedQuotientMul_isIso による余単位の同値。
        -- 通常の D の係数制限は極限・余極限を保ち、p 完備化と両立する

/-- 概要：almost 連結な完備複体は完備 filtered 余極限で閉じる：M_λ が J-almost 連結なら LΛ_p(colim_λ M_λ) も。
方針：上の同値で K ⊗̂ − に移し、完備テンソルは完備余極限を保つ；連結な複体は完備 filtered 余極限で閉じる（通常の filtered 余極限は完全、LΛ_p は D^{≤0} を保つ）。
G-A8-8（perfectoid 性の余極限保存）とは別の補題で、各 M_λ が離散・perfectoid であることは使わない。
規約：—
使われ方：Thm 10.11 の A_λ → T̂_perfd（A8-4）。 -/
theorem isAlmostConnective_completedFilteredColimit
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J)) {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I]
    (F : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ CompleteDerived p R) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hF : ∀ i, IsAlmostConnective p R hR J (F.app _ i).val) :
    IsAlmostConnective p R hR J c.vertex.val := by
  sorry -- K ⊗̂ − は完備余極限を保ち、連結な複体の完備 filtered 余極限は連結


variable {R' : Type u} [CommRing R'] [Algebra R R']

/-- X の semifree 代表を R′ に延ばし、底変換先で p 完備化する。 -/
def completeModuleBaseChange (X : DVertex R) : DVertex R' := by
  let F := (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ)
  let Y := (derivedComplexCompletionFunctor R' (p : R')).obj (DerivedCategory.Q.obj (F.obj (X.obj 0).val))
  exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R').inverse.obj Y).pt

/-- 離散加群の完備底変換の H⁰。K→R の像はこの関手で指定射を送って取る。 -/
def completeBaseChangeH0 : ModuleCat.{u} R ⥤ ModuleCat.{u} R' :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R ⋙ (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⋙ derivedComplexCompletionFunctor R' (p : R') ⋙
    DerivedCategory.homologyFunctor (ModuleCat R') 0

def completeBaseChangeUnitIso (hR' : IsIntegralPerfectoid R' p) :
    (completeBaseChangeH0 p R (R' := R')).obj (ModuleCat.of R R) ≅ ModuleCat.of R' R' := by
  sorry -- R ⊗^L_R R′ の乗法同型と R′ の p 完備化単位の逆

/-- 一般 J について、(JR′)_perfd は K⊗̂_R R′→R′ の像、すなわち R′→B⊗̂_R R′ の核。
有限生成 J でのイデアルの式は K R′ の p 進閉包（Fayolle, Prop 2.9）。
通常の Ideal.map とは一般に異なる。K が有限生成なら一致するが、K = J_perfd 自体は
一般に有限生成でない（D2-02、a8-design §3.1）。 -/
theorem perfectoidIdeal_baseChange (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (hR' : IsIntegralPerfectoid R' p) (hf : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) R') :
    let K := perfectoidKernel p R hR J
    let K' := perfectoidKernel p R' hR' (J.map (algebraMap R R'))
    let i := (completeBaseChangeH0 p R (R' := R')).map (ModuleCat.ofHom K.subtype) ≫
      (completeBaseChangeUnitIso p R hR').hom
    Function.Injective i ∧ K' = LinearMap.range i.hom := by
  sorry -- 完備平坦な底変換の完全性と Prop 8.13 で B の完備底変換への核を同定。
        -- 有限生成 J での閉包の式は Fayolle, Proposition 2.9

/-- M′ は M の完備底変換。K′ ≅ K⊗̂_R R′ を用い、K′⊗̂_{R′}M′ ≃ K⊗̂_R M′
の零性を反映する。通常の拡大イデアルが閉であるという仮定は不要。 -/
theorem isAlmostZero_baseChange_iff (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (hR' : IsIntegralPerfectoid R' p) (hf : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) R')
    (M : DVertex R) (hM : SerrePositivity.DerivedInfinity.IsPComplete p R M) :
    IsJAlmostZero p R hR J M ↔ IsJAlmostZero p R' hR' (J.map (algebraMap R R'))
      (completeModuleBaseChange p R M) := by
  sorry -- 完備底変換後の K′⊗̂M′ は K⊗̂M の完備底変換。Prop 10.4 と忠実平坦性で零性を反映

end SerrePositivity.BhattScholze.Almost
