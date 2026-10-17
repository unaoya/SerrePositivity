module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticIteratedResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplete
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative

/-!
# André E1・E2：モニック源の実逐次完備性と生成元冪商の p 完備性

## 概要

実逐次 p,d 完備化は両方向に導来完備で、正則な d の冪商への実還元も商環上で p 導来完備。
BS Rem 7.15（著者版 p.62）の生成元冪商の離散性の準備。

## 方針

完備性の錐と塔極限での閉性、正則冪商の Koszul 比較、G8 の係数制限の標準単位比較を使う。
原典の Prop 7.11 を使う証明とは異なる経路の計算。

## 規約

元の f/d 源と同じ実逐次対象を扱う。これらの完備性にはモニック性・正次数・有限性は不要。

## 使われ方

生成元冪商への実還元を、導来完備 Nakayama の同じ対象として固定する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)

/-- 概要：実p完備化後に実d完備化を施した具体的モニック族添加対象は、なおp導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceIteratedPDCompletion_isComplete_p :
    DerivedCompletion.IsComplete A (p : A)
      (MonicPrismaticSourceIteratedPDCompletion D d f).obj := by
  let X := MonicPrismaticSourceCoefficientObject D d f
  let Y := (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj X
  have hY : DerivedCompletion.IsComplete A (p : A) Y.obj :=
    DerivedCompletion.derivedComplexCompletionFunctor_isComplete A (p : A) X.obj
  let K := DerivedCategory.Q.objPreimage Y.obj
  let eK : DerivedCategory.Q.obj K ≅ Y.obj := DerivedCategory.Q.objObjPreimageIso Y.obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm hY
  have hstage (n : ℕ) : DerivedCompletion.IsComplete A (p : A)
      (DerivedCategory.Q.obj (DerivedCompletion.complexPowerKoszulStage A d K n)) :=
    DerivedCompletion.isComplete_Q_mappingCone A (p : A)
      (smulId (d ^ n) K) hK hK
  have hC : DerivedCompletion.IsComplete A (p : A)
      (DerivedCompletion.complexCompletionObject A d K) :=
    DerivedCompletion.isComplete_complexTowerHomotopyLimitObject_of_stages A (p : A)
      (DerivedCompletion.complexPowerKoszulStage A d K)
      (DerivedCompletion.complexPowerKoszulTransition A d K) hstage
  let e : DerivedCompletion.complexCompletionObject A d K ≅
      (MonicPrismaticSourceIteratedPDCompletion D d f).obj :=
    (DerivedCompletion.derivedComplexCompletionComparison A d).symm.app K ≪≫
      (DerivedCompletion.derivedComplexCompletionFunctor A d).mapIso eK
  exact DerivedCompletion.isComplete_of_iso A (p : A) e hC

/-- 概要：同じ具体的逐次対象は、最後の主元完備化によりd導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceIteratedPDCompletion_isComplete_d :
    DerivedCompletion.IsComplete A d
      (MonicPrismaticSourceIteratedPDCompletion D d f).obj :=
  DerivedCompletion.derivedComplexCompletionFunctor_isComplete A d
    ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
      (MonicPrismaticSourceCoefficientObject D d f)).obj

local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f

/-- 概要：正則dの実冪商への基底変更を制限すると、候補の実dⁿ Koszul錐になる。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
def monicPrismaticSourceGeneratorPowerReductionKoszulIso (hd : IsSMulRegular A d) (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj ≅
        (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).obj (X₀).obj :=
  restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) X₀

/-- 概要：正則dの任意冪商での実導来還元をAへ制限した対象は、p導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceGeneratorPowerReduction_isComplete_p
    (hd : IsSMulRegular A d) (n : ℕ) :
    DerivedCompletion.IsComplete A (p : A)
      (((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj) := by
  let K := DerivedCategory.Q.objPreimage (X₀).obj
  let eK : DerivedCategory.Q.obj K ≅ (X₀).obj := DerivedCategory.Q.objObjPreimageIso (X₀).obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm
      (monicPrismaticSourceIteratedPDCompletion_isComplete_p D d f)
  have hC := DerivedCompletion.isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
  let e := monicPrismaticSourceGeneratorPowerReductionKoszulIso D d f hd n ≪≫
    (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).mapIso eK.symm ≪≫
      (DerivedCompletion.derivedScalarConeComparison A (d ^ n)).app K
  exact DerivedCompletion.isComplete_of_iso A (p : A) e.symm hC

/-- 概要：正則生成元の任意冪商への実還元は、その商環上でp導来完備。n=0も含む。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS Rem 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceGeneratorPowerReduction_isComplete_over_quotient
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsComplete (A ⧸ Ideal.span {d ^ n}) (p : A ⧸ Ideal.span {d ^ n})
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj := by
  let q := Ideal.Quotient.mk (Ideal.span {d ^ n})
  let T := A ⧸ Ideal.span {d ^ n}
  let Y := ((boundedAboveDerivedBaseChange q).obj
    (MonicPrismaticSourceIteratedPDCompletion D d f)).obj
  let F := derivedRestrictScalars q
  have hR : IsComplete A (p : A) (F.obj Y) :=
    monicPrismaticSourceGeneratorPowerReduction_isComplete_p D d f hd n
  have hunitR : IsIso ((derivedComplexCompletionUnit A (p : A)).app (F.obj Y)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete A (p : A) (F.obj Y) hR
  let e := derivedRestrictionCompletionIso q (p : A)
  have hc : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y) ≫
      e.hom.app Y) := by
    rw [derivedRestrictionCompletionIso_unit]
    exact hunitR
  have hm : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y)) :=
    IsIso.of_isIso_comp_right _ (e.hom.app Y)
  have hS : IsIso ((derivedComplexCompletionUnit T (q (p : A))).app Y) :=
    isIso_of_reflects_iso _ F
  have hcomplete := (isComplete_iff_derivedComplexCompletionUnit_isIso T (q (p : A)) Y).mpr hS
  simpa only [map_natCast] using hcomplete


end SerrePositivity.BhattScholze.Andre
