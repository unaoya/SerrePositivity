module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseProjectiveCompletion
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange

/-!
# 各項完備化による有限 Koszul 複体の比較

## 概要
実主完備化の環の元で作る Koszul 複体は、元の複体の各項 H⁰ 完備化で計算できる。
## 方針
線形関手と有限 Koszul 操作の比較、single の比較、既存の完備環の係数加群の同型を合成する。
## 規約
BS 著者版 Proposition 7.10 の有限 T の模型。スカラーや関係列の正則性はここでは不要。
## 使われ方
係数環上で射影的な生の分解を、完備環上の実際の Koszul 複体へ移す。
-/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) (A : Type u) [CommRing A]

/-- 概要：完備環上の Koszul 複体は各項 H⁰ 完備化に一致する。
方針：線形な Koszul 操作と単一複体の比較を合成する。
規約：BS 著者版 Proposition 7.10。通常の整数次数の複体。
使われ方：有限根関係の完備化後の正則性。 -/
def pointwiseKoszulCompletionIso {r : ℕ} (z : Fin r → A) :
    ((moduleCompletionH0Functor A (p : A)).mapHomologicalComplex (.up ℤ)).obj (koszulComplex z) ≅
      ((ModuleCat.restrictScalars (principalCompletionRingCatUnit p (CommRingCat.of A)).hom).mapHomologicalComplex (.up ℤ)).obj
        (koszulComplex ((principalCompletionRingCatUnit p (CommRingCat.of A)).hom ∘ z)) := by
  let F := moduleCompletionH0Functor A (p : A)
  let K0 := (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)
  let e0 : (F.mapHomologicalComplex (.up ℤ)).obj K0 ≅
      (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A (CompletedRing p A)) :=
    (HomologicalComplex.singleMapHomologicalComplex F (c := .up ℤ) 0).app (ModuleCat.of A A) ≪≫
      (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).mapIso (moduleCompletionH0RingIso A p A)
  exact (F.mapHomologicalComplex _).mapIso (eqToIso (koszulComplexOn_single z)).symm ≪≫
    linearFunctorKoszulOnIso F z K0 ≪≫
    (koszulFunctor z).mapIso e0 ≪≫
    koszulModuleRestrictIso (principalCompletionRingCatUnit p (CommRingCat.of A)).hom z

variable {R : Type u} [CommRing R] (φ : R →+* A)

/-- 係数制限後に各項を完備化しても、同じ完備環上の Koszul 複体を得る。 -/
def pointwiseKoszulCompletionRestrictionIso {r : ℕ} (z : Fin r → A) :
    ((moduleCompletionH0Functor R (p : R)).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj (koszulComplex z)) ≅
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.restrictScalars (principalCompletionRingCatUnit p (CommRingCat.of A)).hom).mapHomologicalComplex (.up ℤ)).obj
        (koszulComplex ((principalCompletionRingCatUnit p (CommRingCat.of A)).hom ∘ z))) := by
  have e := (NatIso.mapHomologicalComplex (moduleCompletionH0RestrictionIso (p : R) φ)
    (.up ℤ)).app (koszulComplex z)
  have e' : ((ModuleCat.restrictScalars φ ⋙ moduleCompletionH0Functor R (p : R)).mapHomologicalComplex (.up ℤ)).obj (koszulComplex z) ≅
      ((moduleCompletionH0Functor A (p : A) ⋙ ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj (koszulComplex z) := by
    simpa only [map_natCast] using e
  let eL := Functor.mapHomologicalComplexCompIso
    (F := ModuleCat.restrictScalars φ) (G := moduleCompletionH0Functor R (p : R))
    (Iso.refl _) (.up ℤ)
  let eR := Functor.mapHomologicalComplexCompIso
    (F := moduleCompletionH0Functor A (p : A)) (G := ModuleCat.restrictScalars φ)
    (Iso.refl _) (.up ℤ)
  exact eL.app _ ≪≫ e' ≪≫ (eR.app _).symm ≪≫
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).mapIso
      (pointwiseKoszulCompletionIso p A z)

end SerrePositivity.DerivedCompletion
