module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarEnhancementClosed

/-! # U13 enhancementの実際の係数拡大と主Perfの導来係数拡大の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarPerfectHomotopyDerivedIso (S : Set D) :
    perfectDGModuleToDerived A D S ⋙ ScalarExtension.derivedExtension φ D ≅
      scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToDerived A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) := by
  let I := (perfectDGModuleInclusion A D S).onClosed
  let J := (perfectDGModuleInclusion A' (ScalarExtension.DGBaseChange φ D)
    (scalarPerfectGenerators φ D S)).onClosed
  let C := scalarPerfectClosedExtension φ D S
  let e := Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft I (moduleToHomotopyDerivedIso A D))
      (ScalarExtension.derivedExtension φ D) ≪≫
    scalarPerfectClosedDerivedIso φ D S ≪≫
      (Functor.isoWhiskerLeft (C ⋙ J)
        (moduleToHomotopyDerivedIso A' (ScalarExtension.DGBaseChange φ D))).symm
  exact CategoryTheory.Quotient.natIsoLift _ e

/-- 実際のH⁰係数拡大と、受入済み導来係数拡大の主Perfへの制限はU13の比較と可換。 -/
def scalarPerfectHomotopyComparison (S : Set D) :
    perfectDGModuleToPerfect A D S ⋙ perfectScalarDerivedExtension φ D S ≅
      scalarPerfectHomotopyExtension φ D S ⋙
        perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
          (scalarPerfectGenerators φ D S) :=
  (((modulePerfectOver A' (ScalarExtension.DGBaseChange φ D)
    (scalarPerfectGenerators φ D S)).fullyFaithfulι).whiskeringRight _).preimageIso
        (scalarPerfectHomotopyDerivedIso φ D S)

end SerrePositivity.DifferentialGraded
