module

public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedCone
public import SerrePositivity.HomologicalAlgebra.DerivedKoszulDescent

/-! # 任意の導来底変換とスカラー錐の交換

上に有界な射影代表の実 mapping cone を用いる。
環写像の平坦性や、スカラーの正則性を要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory HomologicalComplex DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)

/-- スカラー錐の導来底変換は、導来底変換上の元の像によるスカラー錐。
選択した射影代表上の実錐を通して比較する。 -/
def boundedAboveDerivedBaseChangeScalarConeIso (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedBaseChange φ).obj ((boundedAboveDerivedScalarCone R a).obj X)).obj ≅
      (derivedScalarConeFunctor B (φ a)).obj ((boundedAboveDerivedBaseChange φ).obj X).obj := by
  let P := boundedAboveDerivedChosenModel X
  let e : (boundedAboveDerivedScalarCone R a).obj X ≅
      boundedAboveDerivedConeObject P P (smulId a P.complex) :=
    ObjectProperty.isoMk _
      ((derivedScalarConeFunctor R a).mapIso P.iso.symm ≪≫
        (derivedScalarConeComparison R a).app P.complex)
  exact DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange φ).mapIso e) ≪≫
    boundedAboveLeftDerivedConeIso (ModuleCat.extendScalars φ) P P (smulId a P.complex) ≪≫
    eqToIso (by rw [baseChange_smulId]; rfl) ≪≫
    (derivedScalarConeComparison B (φ a)).symm.app (baseChange φ P.complex) ≪≫
    (derivedScalarConeFunctor B (φ a)).mapIso (boundedAboveDerivedBaseChangeModelIso φ X P).symm

/-- 完備化の標準単位を使うと、全ての冪剰余が完備底変換の冪剰余と比較できる。 -/
def boundedAboveDerivedBaseChangePowerConeCompletionIso (a : R) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedBaseChange φ).obj
      ((boundedAboveDerivedScalarCone R (a ^ n)).obj X)).obj ≅
    (derivedScalarConeFunctor B ((φ a) ^ n)).obj
      ((derivedComplexCompletionFunctor B (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj X).obj) :=
  boundedAboveDerivedBaseChangeScalarConeIso φ (a ^ n) X ≪≫
    eqToIso (by rw [map_pow]) ≪≫
    derivedComplexCompletionReductionIso B (φ a) n
      ((boundedAboveDerivedBaseChange φ).obj X).obj

end SerrePositivity
