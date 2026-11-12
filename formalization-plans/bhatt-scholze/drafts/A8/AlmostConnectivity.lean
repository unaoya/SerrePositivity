-- 将来の置き場所：SerrePositivity.BhattScholze.Almost.AlmostConnectivity（仮。原典 Prop 10.4 の必要部分、Lemma 10.5、J-almost の基本）
-- 設計書：formalization-plans/bhatt-scholze/a8-design.md §2.1・§3.1、単位 A8-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Almost.PerfectoidAlmost
public import SerrePositivity.BhattScholze.Almost.Lemma103
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.HeartFullyFaithful
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

/-- 商の perfectoid 化への標準射。J が導来 p 完備なら Thm 7.4 により全射。 -/
def quotientPerfdMap : R →+* QuotientPerfectoidization R J p hR :=
  (toQuotientPerfectoidization R J p hR).comp (Ideal.Quotient.mk J)

def perfectoidKernel : Ideal R := RingHom.ker (quotientPerfdMap p R hR J)

abbrev DVertex (A : Type u) [CommRing A] := (derivedInfinityCategory A) _⦋0⦌

abbrev CompleteDerived (A : Type u) [CommRing A] : SSet.{u+1} :=
  fullSubcomplexOnVertices (derivedInfinityCategory A) (isPCompleteVertex p A)

/-- 主元 p の導来完備化。二つの頂点の semifree 複体をテンソルしてから完備化する。 -/
def completedModuleTensor (X Y : DVertex R) : DVertex R :=
  let C := DerivedCategory.Q.obj (cochainTensor (X.obj 0).val (Y.obj 0).val)
  ((derivedInfinityHomotopyEquivalence R).inverse.obj
    ((derivedComplexCompletionFunctor R (p : R)).obj C)).pt

abbrev kernelTensor (M : DVertex R) :=
  completedModuleTensor p R (moduleHeartVertex R (ModuleCat.of R (perfectoidKernel p R hR J))) M

abbrev quotientTensor (M : DVertex R) :=
  completedModuleTensor p R (moduleHeartVertex R (ModuleCat.of R (QuotientPerfectoidization R J p hR))) M

def IsJAlmostZero (M : DVertex R) : Prop :=
  ∀ i : ℤ, SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J) (derivedInfinityHomology R i M)

/-- 概要：導来 p 完備な複体 M が J-almost 連結 ⇔ H^i(M) が J-almost 零（∀ i > 0）。
方針：既存 `IsAlmostZero` を各コホモロジーに。
規約：D(R) の対象。
使われ方：Lemma 10.5、Thm 10.9。 -/
def IsAlmostConnective (M : DVertex R) : Prop :=
  ∀ i : ℤ, 0 < i → SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J)
    (derivedInfinityHomology R i M)

def completeModuleRestriction {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    CompleteDerived p B ⟶ CompleteDerived p A :=
  let D := (fullSubcomplexOnVertices _ (isPCompleteVertex p B)).ι ≫ derivedInfinityRestrictScalars (E := E) f
  fullSubcomplexLift _ D (by sorry) -- 係数を制限しても底の複体の p 完備性は同じ

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
    IsFullyFaithful U ∧ ∀ (I : SSet.{u+1}) (F : I ⟶ CompleteDerived p B),
      (∀ c : JoinCone F, IsLimitCone c → IsLimitCone (mapJoinCone U c)) ∧
      (∀ c : JoinCocone F, IsColimitCone c → IsColimitCone (mapJoinCocone U c)) := by
  sorry -- B ≃ R/K。一般商の integralPerfectoid_completedQuotientMul_isIso による余単位の同値。
        -- 通常の D の係数制限は極限・余極限を保ち、p 完備化と両立する

/-- 概要：Prop 10.4 の必要部分（D66）：導来 p 完備な複体 M について、M が J-almost 零（全 H^i）⇔ K ⊗̂^L_R M = 0（K = J_perfd）。
方針：加群版（B5。**単項 g の版**なので一般 J は K に対する補題として一般化、W9-III-10）を truncation の帰納で有界複体へ。非有界：各 H^i(M) は B 加群で U の像、
有界切り捨ても像、τ^{≤m}M を下側の切り捨ての逆極限で、M を完備余極限で復元（Postnikov 完備性と U の極限・余極限保存）して M が像に入る；像の上で
K ⊗̂ B = 0 を係数変更。逆は三角形 K ⊗̂ M → M → B ⊗̂ M。
規約：完備テンソル。D66：圏同値は結論にしないが、証明で完全忠実性・像の閉性は使う。
使われ方：Lemma 10.5。 -/
theorem isAlmostZero_iff_completedTensor_isZero (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsJAlmostZero p R hR J M ↔ IsZero ((derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨kernelTensor p R hR J M⟩) := by
  sorry -- B 加群からなる有界切り捨てを U の像で作り、Postnikov 極限と完備余極限で M を復元。
        -- K ⊗̂ B = 0。逆向きは K ⊗̂ M → M → B ⊗̂ M の三角形

/-- 概要：G-A8-1 の系（W9-III-10）：導来 p 完備な M について、M が J-almost 連結 ⇔ K ⊗̂^L_R M が連結。
方針：⇒：Prop 10.4 で K ⊗̂ τ^{>0}M = 0、K ⊗̂ τ^{≤0}M は連結（Lemma 10.5 の証明）。⇐：三角形 K ⊗̂ M → M → B ⊗̂ M で i > 0 の H^i(M) は B 加群 H^i(B ⊗̂ M) に一致。
規約：—
使われ方：下の余極限での閉性、Thm 10.11 の A_λ の段（A8-4）。 -/
theorem isAlmostConnective_iff_completedTensor_connective (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsAlmostConnective p R hR J M ↔ Derived.IsConnectiveAt R 0 (kernelTensor p R hR J M) := by
  sorry -- τ^{>0}M に Prop 10.4 を適用し、逆は三角形の正次数の長完全列

/-- 概要：almost 連結な完備複体は完備 filtered 余極限で閉じる：M_λ が J-almost 連結なら LΛ_p(colim_λ M_λ) も。
方針：上の同値で K ⊗̂ − に移し、完備テンソルは完備余極限を保つ；連結な複体は完備 filtered 余極限で閉じる（通常の filtered 余極限は完全、LΛ_p は D^{≤0} を保つ）。
G-A8-8（perfectoid 性の余極限保存）とは別の補題で、各 M_λ が離散・perfectoid であることは使わない。
規約：—
使われ方：Thm 10.11 の A_λ → T̂_perfd（A8-4）。 -/
theorem isAlmostConnective_completedFilteredColimit
    (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J)) {I : SSet.{u}} [Quasicategory I] [F2.IsFilteredInfinity I]
    (F : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ CompleteDerived p R) (c : JoinCocone F) (hc : IsColimitCone c)
    (hF : ∀ i, IsAlmostConnective p R hR J (F.app _ i).val) :
    IsAlmostConnective p R hR J c.vertex.val := by
  sorry -- K ⊗̂ − は完備余極限を保ち、連結な複体の完備 filtered 余極限は連結

/-- 概要：Lemma 10.5：p 完備な M ∈ D(R) が連結 ⇔ M ⊗̂^L_R R/J_perfd が連結かつ M が J-almost 連結。
方針：⇒ は ⊗̂ R/J_perfd が連結性を保つ。⇐：三角形 J_perfd ⊗̂ M → M → (R/J)_perfd ⊗̂ M、J_perfd ⊗̂ τ^{>0} M = 0（Prop 10.4）、
J_perfd ⊗̂ τ^{≤0} M 連結。(R/J)_perfd = R/J_perfd（Thm 7.4、既存）。
規約：—
使われ方：Thm 10.11 の帰納（A8-4）。 -/
theorem connective_iff_almost (hJ : IsModuleComplete R (p : R) (ModuleCat.of R J))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    Derived.IsConnectiveAt R 0 M ↔ Derived.IsConnectiveAt R 0 (quotientTensor p R hR J M) ∧
      IsAlmostConnective p R hR J M := by
  sorry -- K ⊗̂ M → M → B ⊗̂ M と G-A8-1 の連結性の判定

/-! ## J-almost の基本（G-A8-2） -/

/-- 概要：J_perfd = (√J)_perfd（(R/J)_perfd は perfectoid で被約、普遍性で (R/J)_perfd = (R/√J)_perfd）。J-almost は √J で不変。
方針：既存の perfectoid の被約性と `IsPerfectoidization` の一意性。
規約：—
使われ方：生成元の取り替え（Thm 10.9）。 -/
theorem perfectoidIdeal_radical : perfectoidKernel p R hR J = perfectoidKernel p R hR J.radical := by
  sorry -- perfectoid 標的は被約なので両商からの写像が同じ。単位に両立する普遍同型
theorem isAlmostZero_radical (M : DVertex R) :
    IsJAlmostZero p R hR J M ↔ IsJAlmostZero p R hR J.radical M := by
  unfold IsJAlmostZero
  rw [perfectoidIdeal_radical p R hR J]

/-- 概要：J = (f_1,…,f_r) のとき、M が J-almost 零 ⇔ ∀ i, M が (f_i)-almost 零。
方針（W9-III-03 で訂正）：⇐：Q := R/f_1 ⊗̂^L_R ⋯ ⊗̂^L_R R/f_r（animated な完備押し出し）は π_0 Q = R/J だが Q ≠ R/J（p ねじれなしの R、f_1 = f_2 = p で H^{−1} = R/p ≠ 0）。
Prop 8.5 系 4（`perfectoidization_piZero`）で Q_perfd ≃ (R/J)_perfd、Prop 8.13 で (R/J)_perfd ≃ (R/f_1)_perfd ⊗̂_R ⋯（単位と両立）。M が各 (f_i)-almost 零なら
三角形 (f_i)_perfd ⊗̂ M → M → (R/f_i)_perfd ⊗̂ M で M → (R/f_i)_perfd ⊗̂ M は同値、順にテンソルして M → (R/J)_perfd ⊗̂ M が同値、よって J_perfd ⊗̂ M = 0（紙 1）。
⇒：(f_i) ⊂ J から (f_i)_perfd ⊂ J_perfd を各 H^j(M) に。空の生成族は J = 0 で自明。
規約：—
使われ方：Thm 10.9 を一つの生成元に帰着。 -/
theorem isAlmostZero_iff_forall_gen {r : ℕ} (f : Fin r → R) (hf : J = Ideal.span (Set.range f))
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsJAlmostZero p R hR J M ↔ ∀ i, IsJAlmostZero p R hR (Ideal.span {f i}) M := by
  sorry -- Q の π₀ は R/J。系4で Q_perfd に移し、Prop 8.13 で各 (R/f_i)_perfd の完備テンソルに移す

variable {R' : Type u} [CommRing R'] [Algebra R R']

/-- X の semifree 代表を R′ に延ばし、底変換先で p 完備化する。 -/
def completeModuleBaseChange (X : DVertex R) : DVertex R' := by
  let F := (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ)
  let Y := (derivedComplexCompletionFunctor R' (p : R')).obj (DerivedCategory.Q.obj (F.obj (X.obj 0).val))
  exact ((derivedInfinityHomotopyEquivalence R').inverse.obj Y).pt

/-- 離散加群の完備底変換の H⁰。K→R の像はこの関手で指定射を送って取る。 -/
def completeBaseChangeH0 : ModuleCat.{u} R ⥤ ModuleCat.{u} R' :=
  moduleFreeCochainResolution R ⋙ (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ) ⋙
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
    (M : DVertex R) (hM : isPCompleteVertex p R M) :
    IsJAlmostZero p R hR J M ↔ IsJAlmostZero p R' hR' (J.map (algebraMap R R'))
      (completeModuleBaseChange p R M) := by
  sorry -- 完備底変換後の K′⊗̂M′ は K⊗̂M の完備底変換。Prop 10.4 と忠実平坦性で零性を反映

end SerrePositivity.BhattScholze.Almost
