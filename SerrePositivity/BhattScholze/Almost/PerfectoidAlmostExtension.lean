module

public import SerrePositivity.BhattScholze.Almost.PerfectoidIdealLemma103
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorModuleAction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeScalar
public import SerrePositivity.CommutativeAlgebra.Almost.Quotient

/-!
# Prop 10.2 の導来完備 almost 零加群の拡大閉性
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

@[expose] public noncomputable section
universe u
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
