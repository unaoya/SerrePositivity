module

public import SerrePositivity.BhattScholze.Almost.Lemma103
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeScalar
public import SerrePositivity.CategoryTheory.ExactDerivedTStructure
public import SerrePositivity.CLMST.Almost
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorModuleAction
public import SerrePositivity.CommutativeAlgebra.Almost.Quotient

/-!
# perfectoid 化の核に関する almost 数学（BS 著者版 Prop 10.2、Rem 10.7）

## 概要
核の conormal の導来完備化は零、核の mod pⁿ 像は冪等、核で零化される導来完備加群は拡大で閉じる。

## 方針
Lemma 10.3 から conormal を消し、冪等性と拡大閉性を出す。

## 規約
Prop 10.4 の全体は A8。

## 使われ方
CLMST の almost Tor。
-/

universe u

/-! ## perfectoid 化の核の conormal の導来完備化（旧 Almost/PerfectoidIdealConormalCompletion.lean）

## 概要
核 K の通常の conormal 加群 K/K² は p 作用が可逆であり、その導来 p 完備化は零である。
## 方針
Lemma 10.3 の商自己積を Koszul 錐へ移し、H⁻² の消滅から Tor₁ 上の p 単射性を得る。
## 規約
conormal の完備化と、導来自己テンソルの完備化を区別する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の mod p 冪冪等性の中間結果を明示する。
-/

@[expose] public noncomputable section PerfectoidIdealConormalCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/--
## 概要
perfectoid 化の核 K の conormal 加群 K/K² 上の p 作用は全単射である。
## 方針
商自己積の完備化同型の Koszul 還元から単射性を得て、既存の Tor₁ 可除性と合成する。
## 規約
通常の conormal 加群に関する主張であり、p ねじれなしを追加仮定しない。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の導来完備化消滅を証明する。
-/
theorem perfectoidIdeal_conormal_smul_bijective :
    Function.Bijective (fun x : (perfectoidIdeal R p hR g).Cotangent => (p : R) • x) := by
  let I := perfectoidIdeal R p hR g
  let Q := ModuleCat.of R (R ⧸ I)
  let μ := boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)
  have hμ := (perfectoidIdeal_lemma103 R p hR g).2.1
  have hk : IsIso ((derivedScalarConeFunctor R (p : R)).map μ.hom) := by
    have hh := derivedScalarCone_map_isIso_of_completion R (p : R) μ.hom hμ 1
    rw [_root_.pow_one] at hh
    exact hh
  let L := (CochainComplex.singleFunctor (ModuleCat R) 0).obj Q
  have hl (i : ℤ) (hi : i ≠ 0) : IsZero (L.homology i) :=
    (derivedSingleHomology_isZero Q i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L).symm
  have hzL : IsZero (((scalarConeFunctor (p : R)).obj L).homology (-2)) :=
    (Cone.exact₃ (smulId (p : R) L) (-2) (-1) (by omega)).isZero_of_both_isZero
      (hl (-2) (by omega)) (hl (-1) (by omega))
  have hzY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).obj
      ((derivedScalarConeFunctor R (p : R)).obj
        ((boundedAboveDerivedSingleFunctor.obj Q).obj))) := hzL.of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).mapIso
      ((derivedScalarConeComparison R (p : R)).app L) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-2)).app
        ((scalarConeFunctor (p : R)).obj L))
  have hzX := hzY.of_iso ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).mapIso
    (asIso ((derivedScalarConeFunctor R (p : R)).map μ.hom)))
  have hinj := derived_homology_smul_injective_of_scalarCone_isZero (p : R)
    ((boundedAboveDerivedTensorModuleFunctor Q).obj Q) (-1)
    (by simpa [boundedAboveDerivedTensorModuleFunctor, Q] using hzX)
  let e := (((boundedAboveDerivedTensorModuleTorNatIso Q 1).app Q).toLinearEquiv).trans
    (quotientTorOneConormalEquiv R I)
  constructor
  · intro x y hxy
    change (p : R) • x = (p : R) • y at hxy
    apply e.symm.injective
    apply hinj
    change (p : R) • e.symm x = (p : R) • e.symm y
    rw [← e.symm.map_smul, ← e.symm.map_smul, hxy]
  · exact (quotientTorOne_smul_surjective_iff_conormal R I (p : R)).mp
      (quotientTorOne_smul_surjective_of_completed_mul_isIso (p : R) I hμ)

/--
## 概要
perfectoid 化の核 K の通常の conormal 加群 K/K² の導来 p 完備化は零である。
## 方針
p 作用の全単射性を実完備化へ移す。その各ホモロジーは導来完備かつ p 可除なので零となる。
## 規約
G2 の元の完備化関手を degree zero の conormal 加群へ適用する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の冪等性を導く中間結果を公開する。
-/
theorem perfectoidIdeal_conormal_completion_isZero :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
        (ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent))) := by
  let M := ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent
  let X := (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M
  let F := derivedComplexCompletionFunctor R (p : R)
  have hM : IsIso ((p : R) • 𝟙 M) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (perfectoidIdeal_conormal_smul_bijective R p hR g)
  have hX : IsIso ((p : R) • 𝟙 X) := by
    have hh := (DerivedCategory.singleFunctor (ModuleCat R) 0).map_isIso ((p : R) • 𝟙 M)
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id] using hh
  have hF : IsIso ((p : R) • 𝟙 (F.obj X)) := by
    have hh := F.map_isIso ((p : R) • 𝟙 X)
    rwa [derivedCompletion_map_scalar_id] at hh
  apply (derived_isZero_iff_homology _).mpr
  intro i
  have hH : IsIso ((p : R) • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      (F.obj X))) := by
    have hh := (DerivedCategory.homologyFunctor (ModuleCat R) i).map_isIso
      ((p : R) • 𝟙 (F.obj X))
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id] using hh
  exact isZero_of_complete_of_smul_surjective (p : R) _
    (isComplete_homology_isModuleComplete R (p : R) (F.obj X)
      (derivedComplexCompletionFunctor_isComplete R (p : R) X) i)
    ((ConcreteCategory.isIso_iff_bijective _).mp hH).surjective

/--
## 概要
perfectoid 化の核 K の通常の conormal 加群を p で割ると零加群になる。
## 方針
p 作用の全射性で代表を p 倍に書き、通常の商写像が p 倍を消すことを使う。
## 規約
完備化後の H⁰ だけでなく、元の通常の conormal の mod p 商について主張する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の K=K²+pK へ移る中間結果である。
-/
theorem perfectoidIdeal_conormal_mod_p_isZero :
    IsZero (modulePowerReduction (p : R)
      (ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent) 1) := by
  let M := ModuleCat.of R (perfectoidIdeal R p hR g).Cotangent
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective (modulePowerReductionMap (p : R) M 1)).mp
    (inferInstance) x
  obtain ⟨y, hy⟩ := (perfectoidIdeal_conormal_smul_bijective R p hR g).surjective m
  change (modulePowerReductionMap (p : R) M 1).hom m = 0
  rw [← hy, map_smul]
  simpa only [_root_.pow_one] using
    modulePowerReduction_pow_smul_zero (p : R) M 1
      ((modulePowerReductionMap (p : R) M 1) y)

end SerrePositivity.BhattScholze

end PerfectoidIdealConormalCompletion

/-! ## Remark 10.7 の mod p 冪の冪等性（旧 Almost/PerfectoidIdealIdempotent.lean）

## 概要
perfectoid 化の核 K の mod pⁿ 像は冪等である（BS 著者版 Remark 10.7、印刷 p.80）。
## 方針
Lemma 10.3 の実自己積から既存の Tor₁・conormal 比較を通じて K/K² の p 可除性を得る。
それを反復し K=K²+pⁿK を証明して、既存の像イデアルの冪等性判定を使う。
## 規約
CLMST.Almost の既存の像イデアルの略記だけを利用し、入力引用は使わない。
## 使われ方
CLMST の BasicSetup と同じ署名で冪等性を渡す。BasicSetup 自体は編集しない。
-/

@[expose] public noncomputable section PerfectoidIdealIdempotent

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/--
## 概要
perfectoid 化の核 K の conormal 加群 K/K² は全 pⁿ で可除である。
## 方針
Lemma 10.3 の商自己積から実 Tor₁ の p 可除性を得て既存の conormal 比較で移し、反復する。
## 規約
通常の conormal 加群を使い、p ねじれの有無を仮定しない。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の冪等性の計算に使う。
-/
theorem perfectoidIdeal_conormal_pow_smul_surjective (n : ℕ) :
    Function.Surjective
      (fun x : (perfectoidIdeal R p hR g).Cotangent => (p : R) ^ n • x) := by
  have h := (perfectoidIdeal_conormal_smul_bijective R p hR g).surjective
  induction n with
  | zero =>
    intro x
    exact ⟨x, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := h y
    refine ⟨z, ?_⟩
    change (p : R) ^ n • y = x at hy
    change (p : R) • z = y at hz
    change (p : R) ^ (n + 1) • z = x
    rw [pow_succ, mul_smul, hz, hy]

/--
## 概要
perfectoid 化の核 K は K²+pⁿK に等しい。n=1 は K=K²+pK を与える。
## 方針
conormal 加群の pⁿ 可除性の原像を K に持ち上げ、差が K² に属することを使う。
## 規約
pⁿK は span{pⁿ} と K のイデアル積で明示する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の mod pⁿ 冪等性の中間等式である。
-/
theorem perfectoidIdeal_eq_square_sup_pow_mul (n : ℕ) :
    let K := perfectoidIdeal R p hR g
    K = K * K ⊔ Ideal.span {(p : R) ^ n} * K := by
  let K := perfectoidIdeal R p hR g
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := perfectoidIdeal_conormal_pow_smul_surjective R p hR g n
      (K.toCotangent ⟨x, hx⟩)
    obtain ⟨z, rfl⟩ := K.toCotangent_surjective y
    change (p : R) ^ n • K.toCotangent z = K.toCotangent ⟨x, hx⟩ at hy
    have hz : K.toCotangent (⟨x, hx⟩ - (p : R) ^ n • z) = 0 := by
      rw [map_sub, map_smul, hy, sub_self]
    have hmem : x - (p : R) ^ n * (z : R) ∈ K * K := by
      have hz₂ := (K.toCotangent_eq_zero _).mp hz
      change x - (p : R) ^ n * (z : R) ∈ K ^ 2 at hz₂
      simpa only [pow_two] using hz₂
    have hpz : (p : R) ^ n * (z : R) ∈ Ideal.span {(p : R) ^ n} * K :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) z.property
    exact Submodule.mem_sup.mpr ⟨_, hmem, _, hpz, sub_add_cancel _ _⟩
  · exact sup_le Ideal.mul_le_left Ideal.mul_le_right

/--
## 概要
単項商の perfectoid 化の核の mod pᴺ 像は冪等である
（BS 著者版 Remark 10.7、印刷 p.80）。
## 方針
実商自己積の同型性から、既存の Tor₁・conormal・像イデアルの冪等性判定を適用する。
## 規約
CLMST.Inputs.perfectoidIdealMod_idempotent と同じ署名を保持し、N=0 も含む。
## 使われ方
既存の入力引用を使わずに CLMST へ渡す証明済み入口である。
-/
theorem perfectoidIdealMod_idempotent (N : ℕ) :
    CLMST.perfectoidIdealMod R p hR g N * CLMST.perfectoidIdealMod R p hR g N =
      CLMST.perfectoidIdealMod R p hR g N :=
  ideal_mod_power_idempotent_of_conormal_surjective (p : R) (perfectoidIdeal R p hR g)
    (perfectoidIdeal_conormal_smul_bijective R p hR g).surjective N

end SerrePositivity.BhattScholze

end PerfectoidIdealIdempotent

/-! ## Prop 10.2 の導来完備 almost 零加群の拡大閉性（旧 Almost/PerfectoidAlmostExtension.lean）

## 概要
perfectoid 化の核で零化される導来完備加群は拡大で閉じる（BS 著者版 Prop 10.2、印刷 p.78）。
## 方針
Prop 10.4（印刷 p.79）の環版を使う。商加群の作用から完備テンソルの消滅を得て、
短完全列の三角形で中央へ移し、その H⁰ の商加群構造を復元する。
## 規約
既存の perfectoidIdeal、IsAlmostZero、G2 の実完備導来 tensor を使う。
## 使われ方
KL-T が指定した正確な署名の拡大閉性を供給する。
-/

@[expose] public noncomputable section PerfectoidAlmostExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits MonoidalCategory SerrePositivity.DerivedCompletion
open Almost
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

private lemma annihilates_of_completedTensor_zero (a : R) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M)
    (hz : IsZero ((derivedComplexCompletionFunctor R a).obj
      ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).obj M))) :
    IsAlmostZero I M := by
  let F := derivedComplexCompletionFunctor R a
  let Md := boundedAboveDerivedSingleFunctor.obj M
  let Id := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I)
  let Qd := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (R ⧸ I))
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ I) I.injective_subtype I.mkQ_surjective
  have hz' : IsZero (F.obj (Md ⊗ Id).obj) := hz.of_iso
    (F.mapIso (DerivedCategory.Minus.ι.mapIso (β_ Md Id)))
  have hg : IsIso (F.map ((boundedAboveDerivedTensorModuleFunctor M).map S.g)) :=
    completedTensor_shortExact_rightMap_isIso_of_isZero a M S hS hz'
  have := hg
  let eR : F.obj ((boundedAboveDerivedTensorModuleFunctor M).obj (ModuleCat.of R R)) ≅
      Md.obj :=
    F.mapIso (DerivedCategory.Minus.ι.mapIso (ρ_ Md)) ≪≫
      (derivedComplexCompletionUnitIso R a Md.obj hM).symm
  let e : Md.obj ≅ F.obj (Qd ⊗ Md).obj :=
    eR.symm ≪≫ asIso (F.map ((boundedAboveDerivedTensorModuleFunctor M).map S.g)) ≪≫
      F.mapIso (DerivedCategory.Minus.ι.mapIso (β_ Md Qd))
  let eH := ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app M).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso e
  let q := Ideal.Quotient.mk I
  let eQ := completedBaseChangeTensorRestrictionHomologyIso q a Md 0
  let eM := eH ≪≫ eQ.symm
  apply IsAlmostZero.of_equiv eM.toLinearEquiv.symm
  apply IsAlmostZero.iff_smul_eq_zero.mpr
  intro r hr m
  change (Ideal.Quotient.mk I r) • m = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/--
## 概要
perfectoid 化の核 K が M を零化すれば、K⊗̂ᴸM は零である
（BS 著者版 Prop 10.4、印刷 p.79 の加群に関する方向）。
## 方針
既存の商環作用で M を R/K 加群とし、Lemma 10.3 の混合積消滅と作用 retract を使う。
## 規約
この方向には M の完備性・平坦性・有限性は必要ない。
## 使われ方
短完全列の両端を完備テンソルで消し、Prop 10.2 の拡大閉性に使う。
-/
theorem perfectoidIdeal_completedTensor_isZero_of_isAlmostZero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (M : ModuleCat.{u} R) (hM : IsAlmostZero (perfectoidIdeal R p hR g) M) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of R (perfectoidIdeal R p hR g))).obj M)) := by
  let K := perfectoidIdeal R p hR g
  let := quotientModule K M hM
  let := quotientModule_scalarTower K M hM
  exact completedTensor_isZero_of_algebraModule R (p : R) (R ⧸ K) M
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R K))
    (perfectoidIdeal_lemma103 R p hR g).2.2

/--
## 概要
導来 p 完備加群 M について、K⊗̂ᴸM が零なら perfectoid 化の核 K は M を零化する
（BS 著者版 Prop 10.4、印刷 p.79 の逆方向）。
## 方針
K→R→R/K の tensor 三角形から M≅(R/K)⊗̂ᴸM を得て、実 H⁰ の商環作用を移す。
## 規約
導来完備性を標準完備化単位で使い、古典的完備化で代用しない。
## 使われ方
Prop 10.2 の中央加群のテンソル消滅から、元の零化条件を復元する。
-/
theorem perfectoidIdeal_isAlmostZero_of_completedTensor_isZero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R (p : R) M)
    (hz : IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of R (perfectoidIdeal R p hR g))).obj M))) :
    IsAlmostZero (perfectoidIdeal R p hR g) M :=
  annihilates_of_completedTensor_zero (p : R) (perfectoidIdeal R p hR g) M hM hz

-- 指定署名を保持する。両端の tensor 消滅には h₁,h₃ は不要である。
set_option linter.unusedVariables false in
/--
## 概要
perfectoid 化の核で零化される導来 p 完備加群は、導来完備加群の短完全拡大で閉じる
（BS 著者版 Prop 10.2、印刷 p.78）。
## 方針
商加群の作用から両端の K⊗̂ᴸ− を消し、完全三角形で中央も消えることを示す。
Prop 10.4 の逆方向により、その実 H⁰ の R/K 作用から中央の零化条件を復元する。
## 規約
指定の三つの完備性引数を保持する。両端からの消滅の方向は完備性なしにも成立する。
## 使われ方
KL-T に指定された署名で渡す、証明済みの拡大閉性定理である。
-/
theorem perfectoidIdeal_isAlmostZero_extension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : IsModuleComplete R (p : R) S.X₁) (h₂ : IsModuleComplete R (p : R) S.X₂)
    (h₃ : IsModuleComplete R (p : R) S.X₃)
    (hX₁ : IsAlmostZero (perfectoidIdeal R p hR g) S.X₁)
    (hX₃ : IsAlmostZero (perfectoidIdeal R p hR g) S.X₃) :
    IsAlmostZero (perfectoidIdeal R p hR g) S.X₂ := by
  apply perfectoidIdeal_isAlmostZero_of_completedTensor_isZero R p hR g S.X₂ h₂
  exact completedTensor_isZero_of_shortExact (p : R)
    (ModuleCat.of R (perfectoidIdeal R p hR g)) S hS
    (perfectoidIdeal_completedTensor_isZero_of_isAlmostZero R p hR g S.X₁ hX₁)
    (perfectoidIdeal_completedTensor_isZero_of_isAlmostZero R p hR g S.X₃ hX₃)

end SerrePositivity.BhattScholze

end PerfectoidAlmostExtension

/-! ## B5 の公開入口（旧 Almost/PerfectoidAlmost.lean）

## 概要
BS 著者版 Lemma 10.3（印刷 pp.78–79）、Remark 10.7（印刷 p.80）の冪等性、
Prop 10.2（印刷 p.78）の導来完備 almost 零加群の拡大閉性をまとめる。
## 方針
既存 B3・B4 と、完全 prism による実完備導来 tensor の一般定理を再利用する。
## 規約
核と mod p 冪像の既存定義を保持し、全定理は追加の引用なしに証明されている。
## 使われ方
ルートの一つの import と、KL-T・CLMST への証明済み公開定理の受渡しに使う。
-/
