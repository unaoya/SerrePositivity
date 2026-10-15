module

public import SerrePositivity.BhattScholze.RankOneDPDerivedFactorization
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-! # 分冪代数への実導来係数拡大のKoszul判定

通常テンソルへの置換には、明示した実Koszulホモロジーの消滅を用いる。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : P₀) ^ p)
local notation "G₀" => DividedPowerAlgebra A A
local notation "q₀" => AdjoinRoot.mk ((Polynomial.X : P₀) ^ p)

/-- 切断多項式側の全ホモロジーを制限した加群は、実Koszul coneのホモロジーと一致する。 -/
def rankOneDPTruncationHomologyKoszulIso
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
      ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj) ≅
      (ModuleCat.restrictScalars q₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
          (((boundedAboveDerivedBaseChange q₀).obj X).obj)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      (rankOneDPTruncationDerivedKoszulIso p X).symm ≪≫
    (derivedRestrictScalarsHomologyIso q₀ n).app _

/-- 実分冪導来拡大の各ホモロジーは、X^pの実Koszul coneと同時に零になる。 -/
theorem rankOneDPDerivedKoszulHomology_isZero_iff (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
      ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj)) := by
  have hr : IsZero ((ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj))) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj)) := by
    simp only [ModuleCat.isZero_iff_subsingleton]
    rfl
  exact (rankOneDPDerivedHomology_isZero_iff hprime hp X n).trans
    ((rankOneDPTruncationHomologyKoszulIso (p := p) X n).isZero_iff.trans hr).symm

/-- 全高次Tor消滅は、具体的なX^p Koszul coneの負次ホモロジー消滅で判定できる。 -/
theorem rankOneDPScalarExtensionTorVanishing_iff (hprime : p.Prime) (hp : (p : A) = 0)
    (M : ModuleCat.{u} P₀) :
    scalarExtensionTorVanishing (rankOneDPPolynomialMap A).toRingHom M ↔
      ∀ n : ℕ, 0 < n → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
          ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
            (boundedAboveDerivedSingleFunctor.obj M).obj)) := by
  change (∀ n : ℕ, 0 < n → IsZero
    (((Tor (ModuleCat.{u} P₀) n).obj
      (baseChangeScalarModule (rankOneDPPolynomialMap A).toRingHom)).obj M)) ↔ _
  rw [← derivedModuleBaseChange_negative_homology_vanishes_iff]
  apply forall₂_congr
  intro n _
  exact ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso
      (boundedAboveDerivedBaseChangeModuleIso
        (rankOneDPPolynomialMap A).toRingHom M)).isZero_iff.symm.trans
    (rankOneDPDerivedKoszulHomology_isZero_iff hprime hp
      (boundedAboveDerivedSingleFunctor.obj M) (-(n : ℤ)))

/-- 明示したKoszul消滅の下で、実分冪導来拡大の標準augmentationは通常テンソルへの同型。 -/
def rankOneDPDerivedOrdinaryIso_of_koszul (hprime : p.Prime) (hp : (p : A) = 0)
    (M : ModuleCat.{u} P₀)
    (hK : ∀ n : ℕ, 0 < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj
          (boundedAboveDerivedSingleFunctor.obj M).obj))) :
    (boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj
        (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj
        ((ModuleCat.extendScalars (rankOneDPPolynomialMap A).toRingHom).obj M) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso _ M
    ((rankOneDPScalarExtensionTorVanishing_iff hprime hp M).mpr hK)

end SerrePositivity.BhattScholze
