module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectShiftTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementTensorTriangles

/-! # 実際のenhancement再構成tensorと導来係数変更の三角比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

def perfectEndomorphismEnhancementScalarTensorComparison :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        (scalarPerfectHomotopyExtension φ D S ⋙
          perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
            (scalarPerfectGenerators φ D S)) ≅
      perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ ⋙
        (perfectEndomorphismTensorToPerfect A D S E ⋙ perfectScalarDerivedExtension φ D S) :=
  Functor.isoWhiskerLeft (perfectEndomorphismTensorDG A D S E).onHomotopy
      (scalarPerfectHomotopyComparison φ D S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectEndomorphismEnhancementTensorComparison A D S E hgen)
      (perfectScalarDerivedExtension φ D S) ≪≫
    Functor.associator _ _ _

local instance : (scalarPerfectHomotopyExtension φ D S).CommShift ℤ :=
  scalarPerfectHomotopyExtensionCommShift φ D S
local instance : (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A D S E
local instance : (perfectScalarDerivedExtension φ D S).CommShift ℤ :=
  perfectScalarDerivedExtensionCommShift φ D S

lemma perfectEndomorphismEnhancementScalarTensorComparison_commShift :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    NatTrans.CommShift
      (perfectEndomorphismEnhancementScalarTensorComparison φ D S E hgen).hom ℤ := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := scalarPerfectHomotopyComparison_commShift φ D S
  let := perfectEndomorphismEnhancementTensorComparison_commShift A D S E hgen
  simp only [perfectEndomorphismEnhancementScalarTensorComparison, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

def perfectEndomorphismEnhancementScalarTensorTriangleSquareIso :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    (perfectEndomorphismTensorDG A D S E).onHomotopy.mapTriangle ⋙
        (scalarPerfectHomotopyExtension φ D S ⋙
          perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
            (scalarPerfectGenerators φ D S)).mapTriangle ≅
      (perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ).mapTriangle ⋙
        (perfectEndomorphismTensorToPerfect A D S E ⋙
          perfectScalarDerivedExtension φ D S).mapTriangle := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := perfectEndomorphismEnhancementScalarTensorComparison_commShift φ D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismEnhancementScalarTensorComparison φ D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
